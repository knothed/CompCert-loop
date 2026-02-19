(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Pretty-printer for CminLoop *)

open Format
open! Camlcoq
open AST
open PrintAST
open PrintCminor
open CminLoop

(* Statements *)

let rec print_stmt p s =
  match s with
  | Sskip ->
      fprintf p "/*skip*/"
  | Sassign(id, e2) ->
      fprintf p "@[<hv 2>%s =@ %a;@]" (ident_name id) print_expr e2
  | Sstore(chunk, a1, a2) ->
      fprintf p "@[<hv 2>%s[%a] =@ %a;@]"
              (name_of_chunk chunk) print_expr a1 print_expr a2
  | Scall(None, sg, e1, el) ->
      fprintf p "@[<hv 2>%a@,(@[<hov 0>%a@])@ : @[<hov 0>%a@];@]"
                print_expr e1
                print_expr_list (true, el)
                print_sig sg
  | Scall(Some id, sg, e1, el) ->
      fprintf p "@[<hv 2>%s =@ %a@,(@[<hov 0>%a@])@] : @[<hov 0>%a;@]"
                (ident_name id)
                print_expr e1
                print_expr_list (true, el)
                print_sig sg
  | Stailcall(sg, e1, el) ->
      fprintf p "@[<hv 2>tailcall %a@,(@[<hov 0>%a@])@ : @[<hov 0>%a@];@]"
                print_expr e1
                print_expr_list (true, el)
                print_sig sg
  | Sbuiltin(None, ef, el) ->
      fprintf p "@[<hv 2>builtin %s@,(@[<hov 0>%a@])@ : @[<hov 0>%a@];@]"
                (name_of_external ef)
                print_expr_list (true, el)
	        print_sig (ef_sig ef)
  | Sbuiltin(Some id, ef, el) ->
      fprintf p "@[<hv 2>%s =@ builtin %s@,(@[<hov 0>%a@]) : @[<hov 0>%a@];@]"
                (ident_name id)
                (name_of_external ef)
                print_expr_list (true, el)
	        print_sig (ef_sig ef)
  | Sseq(s1, s2) ->
      fprintf p "(%a@; %a)" print_stmt s1 print_stmt s2
  | Sifthenelse(e, s1, Sskip) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
(*  | Sifthenelse(e, Sskip, s2) ->
      fprintf p "@[<v 2>if (! %a) {@ %a@;<0 -2>}@]"
              expr (15, e)
              print_stmt s2 *)
  | Sifthenelse(e, s1, s2) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
              print_stmt s2
  | Sloop(s) ->
      fprintf p "@[<v 2>loop {@ %a@;<0 -2>}@]"
              print_stmt s
  | Sdummy(s) ->
      fprintf p "@[<v 3>[(d) %a@;<0 -3>]@]"
              print_stmt s
  | Sblock(s) ->
      fprintf p "@[<v 3>{{ %a@;<0 -3>}}@]"
              print_stmt s
  | Sexit n ->
      fprintf p "exit %d;" (Nat.to_int n)
  | Sswitch(long, e, cases, dfl) ->
    let print_case (n,x) =
      let x = Nat.to_int x in
      if long then
        fprintf p "@ case %LdLL: exit %d;" (Z.to_int64 n) x
      else
        fprintf p "@ case %ld: exit %d;" (Z.to_int32 n) x in
      fprintf p "@[<v 2>switch%s (%a) {"
        (if long then "l" else "") print_expr e;
      List.iter print_case cases;
      fprintf p "@ default: exit %d;\n" (Nat.to_int dfl);
      fprintf p "@;<0 -2>}@]"
  | Sreturn None ->
      fprintf p "return;"
  | Sreturn (Some e) ->
      fprintf p "return %a;" print_expr e

(* Functions *)

let rec print_varlist p (vars, first) =
  match vars with
  | [] -> ()
  | v1 :: vl ->
      if not first then fprintf p ",@ ";
      fprintf p "%s" (ident_name v1);
      print_varlist p (vl, false)

let print_function p id f =
  fprintf p "@[<hov 4>\"%s\"(@[<hov 0>%a@])@ : @[<hov 0>%a@]@]@ "
            (extern_atom id)
            print_varlist (f.fn_params, true)
            print_sig f.fn_sig;
  fprintf p "@[<v 2>{@ ";
  let stksz = Z.to_int32 f.fn_stackspace in
  if stksz <> 0l then
    fprintf p "stack %ld;@ " stksz;
  if f.fn_vars <> [] then
    fprintf p "var @[<hov 0>%a;@]@ " print_varlist (f.fn_vars, true);
  print_stmt p f.fn_body;
  fprintf p "@;<0 -2>}@]@ "

let print_extfun p id ef =
  fprintf p "@[<v 0>extern @[<hov 2>\"%s\" =@ %s :@ %a@]@]@ "
    (extern_atom id) (name_of_external ef) print_sig (ef_sig ef)

let print_globdef p (id, gd) =
  match gd with
  | Gfun(External ef) ->
      print_extfun p id ef
  | Gfun(Internal f) ->
      print_function p id f
  | Gvar gv ->
     fprintf p "var \"%s\" %a\n" (extern_atom id) print_globvar gv

let print_program p prog =
  fprintf p "@[<v 0>";
  if extern_atom prog.prog_main <> "main" then
    fprintf p "= \"%s\"\n" (extern_atom prog.prog_main);
  List.iter (print_globdef p) prog.prog_defs;
  fprintf p "@]@."

let destination : string option ref = ref None

let print_if passno prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out (f ^ "." ^ Z.to_string passno) in
      print_program (formatter_of_out_channel oc) prog;
      close_out oc
