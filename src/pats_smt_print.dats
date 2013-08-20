(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-20?? Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(*
** Author: Hanwen Wu (hwwu AT bu DOT edu)
** Time: April 2013
*)

(* ****** ****** *)
staload "./pats_smt_print.sats"
staload "./pats_lintprgm.sats"
staload _ = "libc/SATS/stdio.sats"

#define ATS_DYNLOADFLAG 0


implement {a} 
print_constraints_smt {n} {s} (ics, n) = let 

	fun declare_loop (out: FILEref, n: int) : void = if n > 0 then {
		val () = fprint_string (out, "(declare-fun x")
		val () = fprint_int (out, n)
		val () = fprint_string (out, " () Int)\n")
		val () = declare_loop (out, n-1)
	} 

	fun {a:t@ype} 
	assert_loop {n:int} {s:int} 
		(out: FILEref, ics: !list_vt (icnstr(a, n), s), n: int (n)): void = 
			if list_vt_length<icnstr(a,n)> (ics) > 0 then
				case+ ics of
				| list_vt_cons (!p_ic, !p_ics) => let
						val () = fprint_string (out, "(assert ")
						val () = fprint_icnstr_smt<a> (out, !p_ic, n)
						val () = fprint_string (out, ")\n")
						val () = assert_loop<a> (out, !p_ics, n)
					in fold@ ics end // end of [list_vt_cons]

				| list_vt_nil () => let (*nothing*) in fold@ ics end

	val out = open_file_exn ("constraint_smt.out", file_mode_a)

	val () = fprint_string (out, "(push)\n")
	val () = declare_loop (out, n - 1) (* length = n, define x1 ~ x(n-1)*)
	val () = assert_loop<a> (out, ics, n)
	val () = fprint_string (out, "(check-sat)\n")
	val () = fprint_string (out, "(pop)\n\n")
in  
	close_file_exn(out)
end


(*
**
** HX-2012-02:
** [myintvec] is a [myint] array of positive length
** Suppose A: myintvec(n+1) for some n >= 0; then A
** as a linear constraint stands for the following
** inequality:
**
** A[0] + A[1]*x1 + A[2]*x2 + ... + A[n]*xn >= 0
**
** It will become
**
** (+ (* A[0] 1) (* A[1] x1) (* A[2] x2) ... (* A[n] xn) )
** 
** 
*)*)*)*)*)

implement {a}
fprint_myintvec_smt {n} (out, iv, n) = let
	prval () = lemma_myintvec_params (iv)
	viewtypedef x = myint (a)
	val (pf | p) = myintvec_takeout (iv)
	var i: int = 0
	viewdef v = int@i

  	var !p_clo = @lam (pf: !v | x: &x): void => let 
		val () = if i > 0 then fprint (out, " ")

		val () = fprint (out, "(* ")
		val () = fprint_myint (out, x)  (* coefficient *)
			
		val _ = if i > 0 then let       (* variable name for A[1..n] *)
			val () = fprint (out, " x")
			val () = fprint_int (out, i)
		in end

		else fprint (out, " 1")         (* or constant for A[0] *)

		val () = fprint (out, ")")
		val () = i := i + 1
	in end

	val n = size1_of_int1 (n)
	val () = fprint (out, "(+ ")
	val () = array_ptr_foreach_vclo<x> {v} (view@(i) | !p, !p_clo, n)
	val () = fprint (out, ")")
	prval () = myintvecout_addback (pf | iv)
in
end

implement {a}
fprint_icnstr_smt {n} (out, ic, n) = let
	macdef prstr (s) = fprint_string (out, ,(s))
in case+ ic of

	| ICvec (knd, !p_ivec) => let
		val () = prstr "("

		val () = (case+ knd of
			|  1 => prstr "="
			| ~1 => prstr "distinct"
			|  2 => prstr ">="
			| ~2 => prstr "<"
			| _ => fprint_int (out, knd)
		) : void // end of [val]

		val () = prstr " "
		val () = fprint_myintvec_smt<a> (out, !p_ivec, n)
		val () = prstr " 0)"

	in fold@ (ic) end // end of [ICvec]


	| ICveclst (knd, !p_ics) => 
		if icnstrlst_is_cons(!p_ics, n) 
		then let
			val () = prstr "("

			val () = (
				case+ knd of
				| 0 => prstr "and "
				| 1 => prstr "or "
				| _ => fprint_int (out, knd)
				) : void // end of [val]

			val () = fprint_icnstrlst_smt (out, !p_ics, n)	

			val () = prstr ")"
		in fold@ (ic) end
		else let 
			val () = (
				case+ knd of
				| 0 => fprint (out, "true")
				| 1 => fprint (out, "false")
				| _ => fprint_int (out, knd)
				) : void
		in fold@ ic end
	// end of [ICveclst]
	


	| ICerr _ => let
			val () = prstr "ICerr("
			val () = fprint_string (out, "...")
			val () = prstr ")"
	  	in
			fold@ (ic)
	  	end // end of [ICerr]
end 



implement {a}
fprint_icnstrlst_smt {n} {s} (out, ics, n) = 
	if list_vt_length<icnstr(a,n)> (ics) > 0 then
		case+ ics of
		| list_vt_cons (!p_ic, !p_ics) => let
				val () = fprint_icnstr_smt<a> (out, !p_ic, n)
				val () = fprint (out, " ")
				val () = fprint_icnstrlst_smt<a> (out, !p_ics, n)
			in fold@ ics end // end of [list_vt_cons]

		| list_vt_nil () => let
				val () = fprint (out, "nil")
			in fold@ ics end

implement {a}
icnstrlst_is_cons {n} {s} (ics, n) = case+ ics of
| list_vt_cons (_, _) => let prval () = fold@ ics in true end
| list_vt_nil () => let prval () = fold@ ics in false end

