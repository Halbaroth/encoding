(***************************************************************************)
(* This file is part of the third-party OCaml library `smtml`.             *)
(* Copyright (C) 2023-2024 formalsec                                       *)
(* Written by Hichem Rami Ait El Hara                                      *)
(*                                                                         *)
(* This program is free software: you can redistribute it and/or modify    *)
(* it under the terms of the GNU General Public License as published by    *)
(* the Free Software Foundation, either version 3 of the License, or       *)
(* (at your option) any later version.                                     *)
(*                                                                         *)
(* This program is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the           *)
(* GNU General Public License for more details.                            *)
(*                                                                         *)
(* You should have received a copy of the GNU General Public License       *)
(* along with this program.  If not, see <https://www.gnu.org/licenses/>.  *)
(***************************************************************************)

module AE = AltErgoLib

(* Activate the model generation in the library. *)
let () = AE.Options.set_interpretation ILast

module Fresh = struct
  module D_cnf = AE.D_cnf
  module D_loop = AE.D_loop
  module DStd = D_loop.DStd
  module DExpr = DStd.Expr
  module Typer_Pipe = D_loop.Typer_Pipe
  module DTerm = DExpr.Term
  module DTy = DExpr.Ty
  module DBuiltin = DStd.Builtin

  module Th = (val AE.Sat_solver.get_theory ~no_th:false)
  module SatCont = (val AE.(Sat_solver.get Util.CDCL_Tableaux))
  module SAT = SatCont.Make (Th)
  module Frontend = AE.Frontend
  module FE = Frontend.Make (SAT)
  module ModelMap = AE.ModelMap
  module Q = AE.Numbers.Q

  module Var = struct
    include DTerm.Var

    let is_int _ = false
  end

  module Ex = struct
    type t = unit

    let empty : t = ()

    let union _ex1 _ex2 = ()

    let print ppf _ex = Fmt.pf ppf "()"
  end

  module Rat = struct
    include Q

    let m_one = Q.m_one

    let is_int = Q.is_int

    let is_zero v = Q.equal v Q.zero

    let is_one v = Q.equal v Q.one

    let is_m_one v = Q.equal v m_one

    let ceiling = Q.ceiling
  end

  module Make () = struct
    exception Error of string

    type expr = DTerm.t

    type model = ModelMap.t

    module Sim = OcplibSimplex.Basic.Make (Var) (Rat) (Ex)

    type optimize = Sim.Core.t

    type handle = optimize * (Sim.Core.P.t * bool) option

    type solver = {
      mutable ctx : AE.Commands.sat_tdecl list;
      mutable local : AE.Commands.sat_tdecl list;
      mutable global : AE.Commands.sat_tdecl list;
      mutable last_model : model option;
    }

    (* additional builtins *)

    let string_ty_cst : DExpr.Term.ty_const =
      DExpr.Id.mk ~builtin:DBuiltin.Base
        (Dolmen_std.Path.global "StringTy")
        DExpr.{ arity = 0; alias = No_alias }

    let string_ty = DTy.apply string_ty_cst []

    let float32_ty = DTy.float 8 24

    let float64_ty = DTy.float 11 53

    let int_to_string : DExpr.term_cst =
      DExpr.Id.mk ~name:"IntToString" ~builtin:DBuiltin.Base
        (Dolmen_std.Path.global "IntToString")
        (DTy.arrow [ DTy.int ] string_ty)

    let string_to_int : DExpr.term_cst =
      DExpr.Id.mk ~name:"StringToInt" ~builtin:DBuiltin.Base
        (Dolmen_std.Path.global "StringToInt")
        (DTy.arrow [ string_ty ] DTy.int)

    let real_to_string : DExpr.term_cst =
      DExpr.Id.mk ~name:"RealToString" ~builtin:DBuiltin.Base
        (Dolmen_std.Path.global "RealToString")
        (DTy.arrow [ DTy.real ] string_ty)

    let string_to_real : DExpr.term_cst =
      DExpr.Id.mk ~name:"StringToReal" ~builtin:DBuiltin.Base
        (Dolmen_std.Path.global "StringToReal")
        (DTy.arrow [ string_ty ] DTy.real)

    let real_to_uint32 : DExpr.term_cst =
      DExpr.Id.mk ~name:"RealToUInt32" ~builtin:DBuiltin.Base
        (Dolmen_std.Path.global "RealToUInt32")
        (DTy.arrow [ DTy.real ] DTy.real)

    let f32_to_string : DExpr.term_cst =
      DExpr.Id.mk ~name:"F32ToString" ~builtin:DBuiltin.Base
        (Dolmen_std.Path.global "F32ToString")
        (DTy.arrow [ float32_ty ] string_ty)

    let string_to_f32 : DExpr.term_cst =
      DExpr.Id.mk ~name:"StringToF32" ~builtin:DBuiltin.Base
        (Dolmen_std.Path.global "StringToF32")
        (DTy.arrow [ string_ty ] float32_ty)

    let f64_to_string : DExpr.term_cst =
      DExpr.Id.mk ~name:"F64ToString" ~builtin:DBuiltin.Base
        (Dolmen_std.Path.global "F64ToString")
        (DTy.arrow [ float64_ty ] string_ty)

    let string_to_f64 : DExpr.term_cst =
      DExpr.Id.mk ~name:"StringToF64" ~builtin:DBuiltin.Base
        (Dolmen_std.Path.global "StringToF64")
        (DTy.arrow [ string_ty ] float64_ty)

    module SHT = Hashtbl.Make (struct
      include Symbol

      let hash = Hashtbl.hash
    end)

    let tty_of_etype (e : Ty.t) : DTerm.ty =
      match e with
      | Ty_int -> DTy.int
      | Ty_real -> DTy.real
      | Ty_bool -> DTy.bool
      | Ty_str -> string_ty
      | Ty_bitv 32 -> DTy.bitv 32
      | Ty_bitv 64 -> DTy.bitv 64
      | Ty_fp 32 -> float32_ty
      | Ty_fp 64 -> float64_ty
      | Ty_fp _ | Ty_bitv _ | Ty_list | Ty_app | Ty_unit -> assert false

    let sym_cache = SHT.create 17

    let tcst_of_symbol (s : Symbol.t) =
      match SHT.find_opt sym_cache s with
      | None ->
        let x = Symbol.to_string s
        and t = Symbol.type_of s in
        let cst = DTerm.Const.mk (Dolmen_std.Path.global x) (tty_of_etype t) in
        SHT.add sym_cache s cst;
        cst
      | Some c -> c

    module I :
      Op_intf.S
        with type v := int
         and type t := expr
         and type unop := Ty.unop
         and type binop := Ty.binop
         and type relop := Ty.relop
         and type cvtop := Ty.cvtop
         and type triop := Ty.triop = struct
      open Ty

      let encode_val i = DTerm.Int.mk (Int.to_string i)

      let encode_unop op e =
        let op' =
          match op with
          | Neg -> DTerm.Int.minus
          | _ ->
            Fmt.failwith {|Int: Unsupported Z3 unop operator "%a"|} Ty.pp_unop
              op
        in
        op' e

      let encode_binop op e1 e2 =
        let op' =
          match op with
          | Add -> DTerm.Int.add
          | Sub -> DTerm.Int.sub
          | Mul -> DTerm.Int.mul
          | Div -> DTerm.Int.div
          | Rem -> DTerm.Int.rem
          (* TODO: add the Alt-Ergo power function *)
          (* | Pow ->
            fun e1 e2 ->
              DTerm.apply_cst
                Colibri2_theories_LRA.RealValue.Builtin.colibri_pow_int_int []
                [ e1; e2 ] *)
          | _ -> raise (Error "Unsupported integer operations")
        in
        op' e1 e2

      let encode_relop op e1 e2 =
        let op' =
          match op with
          | Eq -> DTerm.eq
          | Ne -> DTerm.neq
          | Lt -> DTerm.Int.lt
          | Gt -> DTerm.Int.gt
          | Le -> DTerm.Int.le
          | Ge -> DTerm.Int.ge
          | _ ->
            Fmt.failwith {|Arith: Unsupported Z3 relop operator "%a"|}
              Ty.pp_relop op
        in
        op' e1 e2

      let encode_cvtop op _ =
        Fmt.failwith {|Int: Unsupported Z3 cvtop operator "%a"|} Ty.pp_cvtop
              op

      let encode_triop op _ _ _ =
        Fmt.failwith {|Arith: Unsupported Z3 triop operator "%a"|} Ty.pp_triop
          op
    end

    module Real :
      Op_intf.S
        with type v := float
         and type t := expr
         and type unop := Ty.unop
         and type binop := Ty.binop
         and type relop := Ty.relop
         and type cvtop := Ty.cvtop
         and type triop := Ty.triop = struct
      open Ty

      let encode_val f = DTerm.Real.mk (Float.to_string f)

      let encode_unop op e =
        let op' =
          match op with
          | Neg -> DTerm.Real.minus
          | Abs -> assert false
          | Sqrt -> assert false
          (* TODO: add the support *)
          (* | Ceil ->
            fun e ->
              DTerm.apply_cst
                Colibri2_theories_LRA.RealValue.Builtin.colibri_ceil [] [ e ] *)
          | Floor -> DTerm.Real.floor
          | Nearest | Is_nan | _ ->
            Fmt.failwith {|Real: Unsupported Z3 cvtop operator "%a"|} Ty.pp_unop
              op
        in
        op' e

      let encode_binop op e1 e2 =
        let op' =
          match op with
          | Add -> DTerm.Real.add
          | Sub -> DTerm.Real.sub
          | Mul -> DTerm.Real.mul
          | Div -> DTerm.Real.div
          | Min -> fun e1 e2 -> DTerm.ite (DTerm.Real.le e1 e2) e1 e2
          | Max -> fun e1 e2 -> DTerm.ite (DTerm.Real.le e1 e2) e2 e1
          | _ ->
            Fmt.failwith {|Real: Unsupported Z3 binop operator "%a"|}
              Ty.pp_binop op
        in
        op' e1 e2

      let encode_relop op e1 e2 =
        let op' =
          match op with
          | Eq -> DTerm.eq
          | Ne -> DTerm.neq
          | Lt -> DTerm.Real.lt
          | Gt -> DTerm.Real.gt
          | Le -> DTerm.Real.le
          | Ge -> DTerm.Real.ge
          | _ ->
            Fmt.failwith {|Arith: Unsupported Z3 relop operator "%a"|}
              Ty.pp_relop op
        in
        op' e1 e2

      let encode_cvtop op _ =
        Fmt.failwith {|Real: Unsupported Z3 cvtop operator "%a"|} Ty.pp_cvtop op

      let encode_triop op _ _ _ =
        Fmt.failwith {|Arith: Unsupported Z3 triop operator "%a"|} Ty.pp_triop
          op
  end

  module Boolean = struct
    open Ty

    let encode_unop op e =
      let op' = match op with Not -> DTerm.neg | _ -> assert false in
      op' e

    let encode_binop op e1 e2 =
      let op' =
        match op with
        | And -> fun a b -> DTerm._and [ a; b ]
        | Or -> fun a b -> DTerm._or [ a; b ]
        | Xor -> DTerm.xor
        | _ -> assert false
      in
      op' e1 e2

    let encode_relop op e1 e2 =
      let op' =
        match op with Eq -> DTerm.eq | Ne -> DTerm.neq | _ -> assert false
      in
      op' e1 e2

    let encode_cvtop _op _e = assert false

    let encode_triop op e1 e2 e3 =
      let op' = match op with Ite -> DTerm.ite | _ -> assert false in
      op' e1 e2 e3
  end

  module Str = struct
    open Ty

    let encode_unop op e =
      let op' =
        match op with
        | Length -> assert false
        | Trim -> fun _v -> assert false
        | _ -> assert false
      in
      op' e

    let encode_binop op _e1 _e2 =
      let op' =
        match op with
        | At -> assert false
        | String_prefix -> assert false
        | String_suffix -> assert false
        | String_contains -> assert false
        | _ -> assert false
      in
      op'

    let encode_relop op =
      let op' =
        match op with
        | Eq -> DTerm.eq
        | Ne -> DTerm.neq
        | _ ->
          Fmt.failwith {|Str: Unsupported Z3 relop operator "%a"|} Ty.pp_relop
            op
      in
      op'

    let encode_triop op _e1 _e2 _e3 =
      let op' =
        match op with
        | String_extract -> assert false
        | String_replace -> assert false
        | String_index -> assert false
        | _ ->
          Fmt.failwith {|Str: Unsupported Z3 triop operator "%a"|} Ty.pp_triop
            op
      in
      op'

    let encode_cvtop _op _e = assert false
  end

  module Bv = struct
    open Ty

    let encode_val (type a) (cast : a Ty.cast) (i : a) =
      match cast with
      | C8 ->
        let n = if i >= 0 then i else i land ((1 lsl 8) - 1) in
        (* necessary to have the same behaviour as Z3 *)
        DTerm.Bitv.mk
          (Dolmen_type.Misc.Bitv.parse_decimal
            (String.cat "bv" (Int.to_string n))
            8 )
      | C32 ->
        let iint = Int32.to_int i in
        let n = if iint >= 0 then iint else iint land ((1 lsl 32) - 1) in
        (* necessary to have the same behaviour as Z3 *)
        DTerm.Bitv.mk
          (Dolmen_type.Misc.Bitv.parse_decimal
            (String.cat "bv" (Int.to_string n))
            32 )
      | C64 ->
        let n =
          if Int64.compare i Int64.zero >= 0 then Z.of_int64 i
          else Z.logand (Z.of_int64 i) (Z.sub (Z.( lsl ) Z.one 64) Z.one)
        in
        (* necessary to have the same behaviour as Z3 *)
        DTerm.Bitv.mk
          (Dolmen_type.Misc.Bitv.parse_decimal
            (String.cat "bv" (Z.to_string n))
            64 )

    let encode_unop op e =
      let op' =
        match op with
        | Not -> DTerm.Bitv.not
        | Neg -> DTerm.Bitv.neg
        | _ ->
          Fmt.failwith {|Bv: Unsupported Z3 unary operator "%a"|} Ty.pp_unop op
      in
      op' e

    let encode_binop op e1 e2 =
      let op' =
        match op with
        | Add -> DTerm.Bitv.add
        | Sub -> DTerm.Bitv.sub
        | Mul -> DTerm.Bitv.mul
        | Div -> DTerm.Bitv.sdiv
        | DivU -> DTerm.Bitv.udiv
        | And -> DTerm.Bitv.and_
        | Xor -> DTerm.Bitv.xor
        | Or -> DTerm.Bitv.or_
        | ShrA -> DTerm.Bitv.ashr
        | ShrL -> DTerm.Bitv.lshr
        | Shl -> DTerm.Bitv.shl
        | Rem -> DTerm.Bitv.srem
        | RemU -> DTerm.Bitv.urem
        | _ ->
          Fmt.failwith {|Bv: Unsupported Z3 binary operator "%a"|} Ty.pp_binop
            op
      in
      op' e1 e2

    let encode_triop op _ =
      Fmt.failwith {|Bv: Unsupported Z3 triop operator "%a"|} Ty.pp_triop op

    let encode_relop op e1 e2 =
      let op' =
        match op with
        | Eq -> DTerm.eq
        | Ne -> DTerm.neq
        | Lt -> DTerm.Bitv.slt
        | LtU -> DTerm.Bitv.ult
        | Le -> DTerm.Bitv.sle
        | LeU -> DTerm.Bitv.ule
        | Gt -> DTerm.Bitv.sgt
        | GtU -> DTerm.Bitv.ugt
        | Ge -> DTerm.Bitv.sge
        | GeU -> DTerm.Bitv.uge
      in
      op' e1 e2

    let encode_cvtop sz op e =
      let op' =
        match sz with
        | 32 -> (
          match op with
          | Sign_extend n -> DTerm.Bitv.sign_extend n
          | Zero_extend n -> DTerm.Bitv.zero_extend n
          | WrapI64 -> assert false
          | TruncSF32 | TruncSF64 ->
            DTerm.Float.to_sbv 32 DTerm.Float.roundTowardZero
          | TruncUF32 | TruncUF64 ->
            DTerm.Float.to_ubv 32 DTerm.Float.roundTowardZero
          | Reinterpret_float -> DTerm.Float.ieee_format_to_fp 8 24
          | ToBool -> encode_relop Ne (encode_val C32 0l)
          | OfBool ->
            fun e -> DTerm.ite e (encode_val C32 1l) (encode_val C32 0l)
          | _ -> assert false )
        | 64 -> (
          match op with
          | Sign_extend n -> DTerm.Bitv.sign_extend n
          | Zero_extend n -> DTerm.Bitv.zero_extend n
          | TruncSF32 | TruncSF64 ->
            DTerm.Float.to_sbv 64 DTerm.Float.roundTowardZero
          | TruncUF32 | TruncUF64 ->
            DTerm.Float.to_ubv 64 DTerm.Float.roundTowardZero
          | Reinterpret_float -> DTerm.Float.ieee_format_to_fp 11 51
          | ToBool -> encode_relop Ne (encode_val C64 0L)
          | OfBool ->
            fun e -> DTerm.ite e (encode_val C64 1L) (encode_val C64 0L)
          | _ -> assert false )
        | _ -> assert false
      in
      op' e
  end

  module Fp = struct
    open Ty

    let encode_val (type a) (sz : a Ty.cast) (f : a) =
      match sz with
      | C8 -> Fmt.failwith "Unable to create FP numeral using 8 bits"
      | C32 -> DTerm.Float.ieee_format_to_fp 8 24 (Bv.encode_val C32 f)
      | C64 -> DTerm.Float.ieee_format_to_fp 11 53 (Bv.encode_val C64 f)

    let encode_unop op e =
      let op' =
        match op with
        | Neg -> DTerm.Float.neg
        | Abs -> DTerm.Float.abs
        | Sqrt -> DTerm.Float.sqrt DTerm.Float.roundNearestTiesToEven
        | Is_nan -> DTerm.Float.isNaN
        | Ceil -> DTerm.Float.roundToIntegral DTerm.Float.roundTowardPositive
        | Floor -> DTerm.Float.roundToIntegral DTerm.Float.roundTowardNegative
        | Trunc -> DTerm.Float.roundToIntegral DTerm.Float.roundTowardZero
        | Nearest ->
          DTerm.Float.roundToIntegral DTerm.Float.roundNearestTiesToEven
        | _ ->
          Fmt.failwith {|Fp: Unsupported Z3 unary operator "%a"|} Ty.pp_unop op
      in
      op' e

    let encode_binop op e1 e2 =
      let op' =
        match op with
        | Add -> DTerm.Float.add DTerm.Float.roundNearestTiesToEven
        | Sub -> DTerm.Float.sub DTerm.Float.roundNearestTiesToEven
        | Mul -> DTerm.Float.mul DTerm.Float.roundNearestTiesToEven
        | Div -> DTerm.Float.div DTerm.Float.roundNearestTiesToEven
        | Min -> DTerm.Float.min
        | Max -> DTerm.Float.max
        | Rem -> DTerm.Float.rem
        | _ ->
          Fmt.failwith {|Fp: Unsupported Z3 binop operator "%a"|} Ty.pp_binop op
      in
      op' e1 e2

      let encode_triop op _ =
        Fmt.failwith {|Fp: Unsupported Z3 triop operator "%a"|} Ty.pp_triop op

      let encode_relop op e1 e2 =
        let op' =
          match op with
          | Eq -> DTerm.Float.eq
          | Ne -> fun e1 e2 -> DTerm.Float.eq e1 e2 |> DTerm.neg
          | Lt -> DTerm.Float.lt
          | Le -> DTerm.Float.leq
          | Gt -> DTerm.Float.gt
          | Ge -> DTerm.Float.geq
          | _ ->
            Fmt.failwith {|Fp: Unsupported Z3 relop operator "%a"|} Ty.pp_relop
              op
        in
        op' e1 e2

      let encode_cvtop sz op e =
        let op' =
          match sz with
          | 32 -> (
            match op with
            | DemoteF64 ->
              DTerm.Float.to_fp 8 24 DTerm.Float.roundNearestTiesToEven
            | ConvertSI32 | ConvertSI64 ->
              DTerm.Float.sbv_to_fp 8 24 DTerm.Float.roundNearestTiesToEven
            | ConvertUI32 | ConvertUI64 ->
              DTerm.Float.ubv_to_fp 8 24 DTerm.Float.roundNearestTiesToEven
            | Reinterpret_int -> DTerm.Float.ieee_format_to_fp 8 24
            | ToString -> fun v -> DTerm.apply_cst f32_to_string [] [ v ]
            | OfString -> fun v -> DTerm.apply_cst string_to_f32 [] [ v ]
            | _ -> assert false )
          | 64 -> (
            match op with
            | PromoteF32 ->
              DTerm.Float.to_fp 11 53 DTerm.Float.roundNearestTiesToEven
            | ConvertSI32 | ConvertSI64 ->
              DTerm.Float.sbv_to_fp 11 53 DTerm.Float.roundNearestTiesToEven
            | ConvertUI32 | ConvertUI64 ->
              DTerm.Float.ubv_to_fp 11 53 DTerm.Float.roundNearestTiesToEven
            | Reinterpret_int -> DTerm.Float.ieee_format_to_fp 11 53
            | ToString -> fun v -> DTerm.apply_cst f64_to_string [] [ v ]
            | OfString -> fun v -> DTerm.apply_cst string_to_f64 [] [ v ]
            | _ -> assert false )
          | _ -> assert false
        in
        op' e
    end

    let encode_val : Value.t -> expr = function
      | True -> DTerm.of_cst DTerm.Const._true
      | False -> DTerm.of_cst DTerm.Const._false
      | Int v -> I.encode_val v
      | Real v -> Real.encode_val v
      | Str _ -> assert false
      | Num (I8 x) -> Bv.encode_val C8 x
      | Num (I32 x) -> Bv.encode_val C32 x
      | Num (I64 x) -> Bv.encode_val C64 x
      | Num (F32 x) -> Fp.encode_val C32 x
      | Num (F64 x) -> Fp.encode_val C64 x
      | _ -> assert false

    let encode_unop = function
      | Ty.Ty_int -> I.encode_unop
      | Ty.Ty_real -> Real.encode_unop
      | Ty.Ty_bool -> Boolean.encode_unop
      | Ty.Ty_str -> Str.encode_unop
      | Ty.Ty_bitv _ -> Bv.encode_unop
      | Ty.Ty_fp _ -> Fp.encode_unop
      | (Ty.Ty_list | Ty_app | Ty_unit) as op ->
        Fmt.failwith
          "Alt_ergo_mappings: Trying to code unsupported op of type %a" Ty.pp op

    let encode_binop = function
      | Ty.Ty_int -> I.encode_binop
      | Ty.Ty_real -> Real.encode_binop
      | Ty.Ty_bool -> Boolean.encode_binop
      | Ty.Ty_str -> Str.encode_binop
      | Ty.Ty_bitv _ -> Bv.encode_binop
      | Ty.Ty_fp _ -> Fp.encode_binop
      | (Ty.Ty_list | Ty_app | Ty_unit) as op ->
        Fmt.failwith
          "Alt_ergo_mappings: Trying to code unsupported op of type %a" Ty.pp op

    let encode_triop = function
      | Ty.Ty_int -> I.encode_triop
      | Ty.Ty_real -> Real.encode_triop
      | Ty.Ty_bool -> Boolean.encode_triop
      | Ty.Ty_str -> Str.encode_triop
      | Ty.Ty_bitv _ -> Bv.encode_triop
      | Ty.Ty_fp _ -> Fp.encode_triop
      | (Ty.Ty_list | Ty_app | Ty_unit) as op ->
        Fmt.failwith
          "Alt_ergo_mappings: Trying to code unsupported op of type %a" Ty.pp op

    let encode_relop = function
      | Ty.Ty_int -> I.encode_relop
      | Ty.Ty_real -> Real.encode_relop
      | Ty.Ty_bool -> Boolean.encode_relop
      | Ty.Ty_str -> Str.encode_relop
      | Ty.Ty_bitv _ -> Bv.encode_relop
      | Ty.Ty_fp _ -> Fp.encode_relop
      | (Ty.Ty_list | Ty_app | Ty_unit) as op ->
        Fmt.failwith
          "Alt_ergo_mappings: Trying to code unsupported op of type %a" Ty.pp op

    let encode_cvtop = function
      | Ty.Ty_int -> I.encode_cvtop
      | Ty.Ty_real -> Real.encode_cvtop
      | Ty.Ty_bool -> Boolean.encode_cvtop
      | Ty.Ty_str -> Str.encode_cvtop
      | Ty.Ty_bitv sz -> Bv.encode_cvtop sz
      | Ty.Ty_fp sz -> Fp.encode_cvtop sz
      | (Ty.Ty_list | Ty_app | Ty_unit) as op ->
        Fmt.failwith
          "Alt_ergo_mappings: Trying to code unsupported op of type %a" Ty.pp op

    let encore_expr_aux ?(record_sym = fun _ -> ()) (e : Expr.t) : expr =
      let open Expr in
      let rec aux (hte : t) =
        match view hte with
        | Val v -> encode_val v
        | Ptr { base; offset } ->
          let base' = encode_val (Num (I32 base)) in
          let offset' = aux offset in
          DTerm.Bitv.add base' offset'
        | Symbol s ->
          let cst = tcst_of_symbol s in
          record_sym cst;
          DTerm.of_cst cst
        | Unop (ty, op, e) ->
          let e' = aux e in
          encode_unop ty op e'
        | Binop (ty, op, e1, e2) ->
          let e1' = aux e1 in
          let e2' = aux e2 in
          encode_binop ty op e1' e2'
        | Triop (ty, op, e1, e2, e3) ->
          let e1' = aux e1
          and e2' = aux e2
          and e3' = aux e3 in
          encode_triop ty op e1' e2' e3'
        | Relop (ty, op, e1, e2) ->
          let e1' = aux e1
          and e2' = aux e2 in
          encode_relop ty op e1' e2'
        | Cvtop (ty, op, e) ->
          let e' = aux e in
          encode_cvtop ty op e'
        | Naryop _ -> Fmt.failwith "Alt_ergo_mappings: Trying to encode naryop"
        | Extract (e, h, l) ->
          let e' = aux e in
          DTerm.Bitv.extract ((h * 8) - 1) (l * 8) e'
        | Concat (e1, e2) ->
          let e1' = aux e1
          and e2' = aux e2 in
          DTerm.Bitv.concat e1' e2'
        | List _ | App _ -> assert false
      in
      aux e

    let encode_expr e = encore_expr_aux e

    let pp_smt ?status:_ _ _ = ()

    module Solver = struct
      let make ?params:_ ?logic:_ () = {
        ctx = [];
        local = [];
        global = [];
        last_model = None;
      }

      let clone _ = assert false

      let dl_dummy_file = DStd.Loc.mk_file ""

      let to_stmt contents = Typer_Pipe.{
        id = DStd.Id.mk DStd.Namespace.decl "";
        loc = DStd.Loc.no_loc;
        contents;
        attrs = [];
        implicit = false;
      }

      let hook_on_status _status _i = ()

      let record_sym s c =
        let cnf =
          D_cnf.make dl_dummy_file s.ctx (to_stmt (`Decls [`Term_decl c]))
          |> List.rev
        in
        s.ctx <- cnf

      let add_simplifier s = s

      let add_command s td =
        (* XXX: we do not need to reverse this list??? *)
        let cnf = D_cnf.make dl_dummy_file s.ctx (to_stmt td) in
        s.ctx <- cnf

      let encore_expr s = encore_expr_aux ~record_sym:(record_sym s)

      let check s ~assumptions =
        let l = s.ctx @ s.global @ s.local in
        let assumptions = List.map (encore_expr s) assumptions in
        let cnf =
          D_cnf.make dl_dummy_file l (to_stmt (`Check assumptions))
          |> List.rev
        in
        let used_context = Frontend.init_all_used_context () in
        SAT.reset_refs ();
        let ftnd_env = FE.init_env used_context in
        List.iter (FE.process_decl ~hook_on_status ftnd_env) cnf;
        let () =
          match ftnd_env.FE.res, SAT.get_model ftnd_env.FE.sat_env with
          | (`Sat | `Unknown), Some AE.Models.{ model; _ } ->
            s.last_model <- Some model
          | _ ->
            s.last_model <- None
        in
        s.local <- [];
        match ftnd_env.FE.res with
        | `Unknown -> `Sat
        | s -> s

      let add s terms =
        let terms = List.map (encore_expr s) terms in
        let cnf =
          List.fold_left
            (fun cnf t ->
              D_cnf.make dl_dummy_file cnf (to_stmt (`Hyp t))
              |> List.rev
            ) s.ctx terms
        in
        s.ctx <- cnf

      let push s = add_command s (`Push 1)
      let pop s n = add_command s (`Pop n)
      let reset s = add_command s `Reset

      let model s = s.last_model

      let interrupt _s = ()

      let get_statistics _ =
        Fmt.failwith "Alt_ergo_mappings: Solver.get_statistics not implemented"
    end

    module Sy = AE.Symbols

    let to_int e =
      let AE.Expr.{ f; _ } = AE.Expr.term_view e in
      match f with
      | Sy.Int z -> Z.to_int z
      | _ -> assert false

    let to_float e =
      let AE.Expr.{ f; _ } = AE.Expr.term_view e in
      match f with
      | Sy.Real q -> Q.to_float q
      | _ -> assert false

    let ae_value_to_value (v : AE.Expr.t) =
      let AE.Expr.{ f; xs; ty; _ } = AE.Expr.term_view v in
      match f, ty, xs with
      | Sy.True, _, _ -> Value.True
      | Sy.False, _, _ -> Value.False
      | Sy.Int _, _, _ -> Value.Int (to_int v)
      | Sy.Real _, _, _ -> Value.Real (to_float v)
      | Sy.Op Div, _, [ n; m ] ->
        Value.Real ((to_float n) /. (to_float m))
      | Sy.Op Minus, AE.Ty.Tint, [ _; n ] ->
        Value.Int (- to_int n)
      | Sy.Op Minus, AE.Ty.Treal, [ _; n ] ->
        Value.Real (-. to_float n)
      | Sy.Bitv (8, z), _, [] -> Value.Num (I8 (Z.to_int z))
      | Sy.Bitv (32, z), _, [] -> Value.Num (I32 (Z.to_int32 z))
      | Sy.Bitv (64, z), _, [] -> Value.Num (I64 (Z.to_int64 z))
      | _ ->
        Fmt.failwith
          "Alt_ergo_mappings: Unsupported model generation of type %a"
            AE.Ty.pp_smtlib ty

    let value mdl t =
      match encore_expr_aux t with
      | DExpr.{ term_descr = Cst cst; _ } ->
        ModelMap.eval (ModelMap.get (AE.Uid.of_term_cst cst) mdl) []
        |> ae_value_to_value
      | t ->
        Fmt.failwith
          "Alt_ergo_mappings: unexpected %a" DExpr.Term.print t

    let values_of_model ?symbols mdl : Model.t =
      let m = Hashtbl.create 512 in
      match symbols with
(*       | Some symbols -> *)
      | None ->
        ModelMap.iter
          (fun g ->
            ae_value_to_value @@ ModelMap.eval g []
          ) mdl


    module Optimizer = struct
      let make () : optimize = Sim.Core.empty ~is_int:false ~check_invs:false

      let push _ = ()

      let pop _ = ()

      let add _ _ = assert false

      let check _ = assert false

      let model o =
        match Sim.Result.get None o with
        | Sim.Core.Sat s ->
          let _model = (Lazy.force s).Sim.Core.main_vars in
          (* TODO *)
          (* let l = List.map (fun (n, av) -> (n, LRA.RealValue.of_value av)) model in
             Some l *)
          None
        | Sim.Core.Unknown | Sim.Core.Unsat _ | Sim.Core.Unbounded _
        | Sim.Core.Max (_, _) ->
          None

      let maximize _ _ = assert false

      let minimize _ _ = assert false

      let interrupt _ = ()

      let get_statistics _ =
        Fmt.failwith
          "Alt_ergo_mappings: Optimizer.get_statistics not implemented"
    end

    (* TODO *)
    let set_debug _ = ()
  end
end

let is_available = true

include Fresh.Make ()
