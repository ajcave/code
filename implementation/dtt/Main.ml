open Lexing

let parse (c : in_channel) : AbsSyntax.moduleT = 
    ParSyntax.pModuleT LexSyntax.token (Lexing.from_channel c)
;;

let showTree (t : AbsSyntax.moduleT) : string = 
    "[Abstract syntax]\n\n" ^ (fun x -> ShowSyntax.show (ShowSyntax.showModuleT x)) t ^ "\n\n" ^
    "[Linearized tree]\n\n" ^ PrintSyntax.printTree PrintSyntax.prtModuleT t ^ "\n"
;;

let main () =
    let channel =
      if Array.length Sys.argv > 1 then
        open_in Sys.argv.(1)
      else
        stdin
    in
    try
      let tree = parse channel in
        print_string (showTree tree);
        flush stdout;
	let itree = Desugar.index tree in
	if (Typecheck.chkMod itree)
	then Printf.printf "Yep\n"
	else Printf.printf "Nope\n"
    with BNFC_Util.Parse_error (start_pos, end_pos) ->
        Printf.printf "Parse error at %d.%d-%d.%d\n"
            start_pos.pos_lnum (start_pos.pos_cnum - start_pos.pos_bol)
            end_pos.pos_lnum (end_pos.pos_cnum - end_pos.pos_bol);
;;

main ();;
