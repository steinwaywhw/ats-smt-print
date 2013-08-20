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

staload "./pats_lintprgm.sats"
staload _ = "libc/SATS/stdio.sats"

fun {a:t@ype}
fprint_myintvec_smt {n:int} 
(out: FILEref, iv: !myintvec(a, n), n: int n): void

fun {a:t@ype} 
fprint_icnstr_smt {n:int} 
(out: FILEref, ic: !icnstr(a, n), n: int n): void

fun {a:t@ype}
fprint_icnstrlst_smt {n:int} {s:int} 
(out: FILEref, ics: !list_vt (icnstr(a, n), s), n: int n) : void 

fun {a:t@ype}
icnstrlst_is_cons {n:int} {s:int} 
(ics: !list_vt (icnstr(a, n), s), n: int n) : bool 


fun {a:t@ype}
print_constraints_smt {n:int} {s:int} 
(ics: !list_vt (icnstr(a, n), s), n: int n): void