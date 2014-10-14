module type SwitchType = sig
 type t
 val init : t
 val flip : t -> t
 val isOn : t -> bool
end

module Switch1 : SwitchType = struct
 type t = int 
 let init = 1 (* positive means "off", negative means "on" *)
 let flip n = -2*n
 let isOn n = (n < 0)
end

module Switch2 : SwitchType = struct
 type t = bool
 let init = false (* false means "off", true means "on" *)
 let flip b = not b
 let isOn b = b 
end

(*
# Switch1.isOn Switch1.init;;
- : bool = false
# Switch2.isOn Switch2.init;;
- : bool = false
# let y1 : bool = Obj.magic Switch1.init;;
val y1 : bool = true
# let y2 : bool = Obj.magic Switch2.init;;
val y2 : bool = false
# (Switch1.flip (Switch1.flip Switch1.init)) = Switch1.init;;
- : bool = false
# (Switch2.flip (Switch2.flip Switch2.init)) = Switch2.init;;
- : bool = true
*)
