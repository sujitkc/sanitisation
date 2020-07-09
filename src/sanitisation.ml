module Object = struct
  exception ObjectException of string

  type object_state = DIRTY | CLEAN
  let inf = 10

  type obj = {
    name : bytes;
    initial_state : object_state;
    final_state : object_state;
    cleaning_cost : int;
  }

  let new_obj n i f c =
  if c > inf then raise (ObjectException ("cleaning cost larger than " ^ (string_of_int inf)))
  else  { name = n; initial_state = i; final_state = f; cleaning_cost = c }

  let hand = new_obj "hand" DIRTY CLEAN 1

  type t = obj

  let compare o1 o2 = Bytes.compare o1.name o2.name
end

module Action = struct
  type action_type = CLEANING | DIRTYING | NEUTRAL

  type action = {
    name : bytes;
    objects : Object.obj list;
  }

  let new_action n objs = { name = n ; objects = Object.hand :: objs }

  let string_of_action a = a.name
end

module DAG = struct

  exception DAGException of string

  type node = {
    value : Action.action;
    mutable succ : node list;
  }

  type dag = { root : node; nodes : node list }

  let new_dag nodes =
    if nodes <> []  then { root = List.nth nodes 0; nodes = nodes }
    else raise (DAGException "Can't build empty DAG.")

  let dag_mem n d = List.mem n d.nodes
  
  let set_root n d =
    if dag_mem n d then {d with root = n }
    else raise (DAGException "Can't set non-member as root.")

  let new_node v = 
    { value = v; succ = [] }

  let add_node n d =
    if not (dag_mem n d) then
      {d with nodes = n :: d.nodes }
    else
      raise (DAGException "Node already there in the DAG.")
 
  let string_of_node n =
    let succ_names = List.map (fun x -> x.value.Action.name) n.succ in
    let str_succ_names = "[" ^ List.fold_left
      (fun x y -> x ^ ", " ^ y) "" succ_names ^ "]" in
    "Node ( description: " ^ 
    (Action.string_of_action n.value) ^ str_succ_names ^ ")"

  let predecessors n d = List.filter (fun n' -> List.mem n n'.succ) d.nodes

  let rec descendants n d =
    [n] @ (explore n.succ d)
  and explore nodes d =
    match nodes with
      [] -> []
    | n :: ns -> (descendants n d) @ (explore ns d)
      
  let add_succ n n' d =
    if not (List.mem n' n.succ) then
      if not (List.mem n (descendants n' d)) then
        n.succ <- (n'::n.succ)
      else
        raise (DAGException "Cycles not allowed in DAG.")
    else
      raise (DAGException "Successor already there.")

  let add_succs n lst d =
    let rec loop n = function
      [] -> ()
    | h :: t -> begin (add_succ n h d); loop n t end
    in
    loop n lst

  let string_of_dag d =
    List.fold_left (fun x y -> x ^"\n" ^ (string_of_node y)) "" d.nodes
end

module Node = struct
  type t = DAG.node
 
  (* dummy compare; not really used anywhere. *) 
  let compare n1 n2 =
    if n1.DAG.value.Action.name < n2.DAG.value.Action.name then -1
    else if n1.DAG.value.Action.name > n2.DAG.value.Action.name then 1
    else 0
end

module NodeSet = Set.Make(Node)
module ObjectSet = Set.Make(Object)

module Util = struct
  let is_node_subset x y = (NodeSet.union x y) = y

  let add_all_objects set objlist =
    let rec loop set = function
      [] -> set
    | h :: t -> loop (ObjectSet.add h set) t
    in
    loop set objlist

  let remove_all_objects set objlist =
    let objset = ObjectSet.of_list objlist in
    ObjectSet.diff set objset

  let is_object_subset x y = (ObjectSet.union x y) = y

  let sum_int_list l = List.fold_left (fun x y -> x + y) 0 l

  let flatten_list llst =
    List.fold_left (fun l1 l2 -> l1 @ l2) [] llst 

  let string_of_object_list olist =
    let onames = List.map (fun o -> o.Object.name) olist in
    "[" ^ (List.fold_left (fun x y -> x ^ ", " ^ y) "" onames) ^ "]"

  let print_node_sequence seq =
    let aseq = List.map 
      (fun n ->
        n.DAG.value.Action.name
        ^ (string_of_object_list n.DAG.value.Action.objects)) seq in
    print_endline (List.fold_left (fun x y -> x ^ ",\n" ^ y) "" aseq)

  let print_action_seq seq =
    let aseq =
      List.map
        (fun a -> a.Action.name
        ^ (string_of_object_list a.Action.objects)) seq in
    print_endline (List.fold_left (fun x y -> x ^ ",\n" ^ y) "" aseq)
  
end


module Sequence = struct
  exception SequenceException of string


  let pick_next ready =
    match NodeSet.elements ready with
      [] -> raise (SequenceException "Can't pick from an empty set.")
    | h :: _ -> h
  

  let make_sequence d =
    let rec loop seq ready =
      match NodeSet.elements ready with
        [] -> seq
      | h :: t ->
          let next = pick_next ready in
          let seq' = next :: seq in
          print_endline ("next = " ^ DAG.string_of_node next);
          let f x =
            not (List.mem x seq')
              &&
            let precs = (NodeSet.of_list (DAG.predecessors x d))
            and seq_set = NodeSet.of_list seq' in
            Util.is_node_subset precs seq_set
          in
          let succ = NodeSet.of_list (List.filter f next.DAG.succ)
          and ready' = NodeSet.remove next ready in
          begin
            let ready'' = (NodeSet.union succ ready') in
            let f = (fun n -> n.DAG.value.Action.name) in
            let aseq = List.map f  (NodeSet.elements ready'')  in
            print_endline (
              "ready = " ^
              (List.fold_left (fun x y -> x ^ ", " ^ y) "" aseq)
            );
            loop seq' ready''
          end
    in
    List.rev (loop [] (NodeSet.of_list [d.DAG.root]))
end

module Sanitisation = struct
  exception SanitisationError of bytes

  let count = ref 0

  type context = {
    dag : DAG.dag;
    objects: ObjectSet.t; (* Object.obj list;*)
    actions: Action.action list;
  }

  (*
    The update_clean_set function takes a set of clean objects
    and an action (a), and gives back an updated set of objects
    which are clean.
    If a is a cleaning action, the object cleaned by a will be 
    added to the clean set. In other cases, this function will
    remove objects getting dirtied by a. For example, if a = A(x, y)
    where A is an action and x, y are object parameters of the
    action, and if x is in clean set, while y is not, after a
    getting executed, x will be dirtied, and hence should be taken
    out of the clean set.
    Similarly, the unique hand object should be added to the clean
    set if a is a cleaning action, If a is a dirtying action, hand
    should be removed from the clean set.
  *)
  (*----- update_clean_set - begin -----------------------*)
  let update_clean_set a clean_set =
    if a.Action.name = "sanitise" then
     let clean_set' = Util.add_all_objects clean_set a.Action.objects in
     ObjectSet.add Object.hand clean_set'
    else if Util.is_object_subset 
      (ObjectSet.of_list a.Action.objects) clean_set then
      (* let clean_set' = ObjectSet.add Object.hand clean_set in *)
      clean_set
    else
    (*
      let dirty = (ObjectSet.union 
                    (ObjectSet.of_list [Object.hand])
                    (ObjectSet.diff 
                      clean_set 
                      (ObjectSet.of_list a.Action.objects))) in
      Util.remove_all_objects clean_set (ObjectSet.elements dirty)
    *)
      Util.remove_all_objects clean_set a.Action.objects
  (*----- update_clean_set - end -----------------------*)

  (*
    The cost function computes the sanitisation cost of an entire
    sequence of actions. It filters out the sanitisation actions
    from the sequence, and adds up the sanitisation costs of 
    individual objects that are sanitised.
  *)
  (*----- cost - begin -----------------------*)
  let cost seq = 
    let sanitisation_cost a =
      let costs = List.map (fun o -> o.Object.cleaning_cost) a.Action.objects in
      Util.sum_int_list costs
    in
    let san = List.filter (fun a -> a.Action.name = "sanitise") seq in
    let san_costs = List.map sanitisation_cost san in
    Util.sum_int_list san_costs
  (*----- cost - end -----------------------*)

  let insert seq (con : context) =
    (* list of objects which need to be CLEAN at the end of the process. *)
    let to_be_cleaned = List.filter
      (fun o -> o.Object.final_state = Object.CLEAN)
      (ObjectSet.elements con.objects) in
    let all_cleaners = List.map 
                (
                  fun o -> 
                    {
                      Action.name = "sanitise";
                      Action.objects = [o; Object.hand]
                    }
                ) (ObjectSet.elements con.objects)
    in 
    (*
      Candidates are:
      - sanitisation of those objects which are currently dirty.
      - sanitisation of those objects which are required to be clean
        or those who are involved in actions in the pending sequence
        with objects which are needed to be clean in the end.
      - sanitisation of those objects which are involved in such
        actions in the head action of the pending sequence.
    *) 
  (*----- candidates - begin -----------------------*)
    let candidates pending_seq curr_seq clean_set =
      let dirty_set = ObjectSet.diff con.objects clean_set in
      (* print_endline ("dirty = " ^ (Util.string_of_object_list (ObjectSet.elements dirty_set))); *)
      let cleans_dirty a =
        let tfs = List.map (fun o -> ObjectSet.mem o dirty_set) a.Action.objects in
        List.fold_left (fun x y -> x || y) false tfs
      in
      (* set of actions which clean currently dirty objects. *)
      let cand1 = List.filter cleans_dirty all_cleaners in
      (*----- is_relevant_object - begin -----------------------*)
      let is_relevant_object o =
        (* other objects that are involved in action a with object o *)
        let partner_objects o a =
          if List.mem o a.Action.objects then
            (List.filter (fun o' -> o' <> o) a.Action.objects)
          else []
        in
        (* o's partner objects in the pending sequence *)
        let all_future_partner_objects o =
          let all_partners_lst_lst = List.map (partner_objects o) pending_seq in
          Util.flatten_list all_partners_lst_lst
        in
        (
          (* if o is to be cleaned *)
          (List.mem o to_be_cleaned)
            ||
          (* any of the future partners of o is to be cleaned *)
          (List.mem
            true
            (List.map
              (fun o -> List.mem o to_be_cleaned)
              (all_future_partner_objects o))))
      (*----- is_relevant_object - end -----------------------*)
      in
      (* list of actions which clean relevant objects *)
      let cand2 = List.filter
                    (fun a ->
                      List.mem true 
                      (List.map
                        is_relevant_object a.Action.objects))
                    cand1
      in
      let cand3 =
        match pending_seq with
          [] -> cand2
        | a :: _ -> List.filter 
                      (fun a' ->
                         (ObjectSet.inter 
                            (ObjectSet.of_list a.Action.objects) 
                            (ObjectSet.of_list a'.Action.objects))
                            <>
                         ObjectSet.empty)
                      cand2
      in
      cand3
  (*----- candidates - end -----------------------*)
    in
    (*----- dive - begin -----------------------*)
    let rec dive pending_seq curr_seq best_seq clean_set =
      print_endline "DIVE";
      print_endline "Current sequence:";
      Util.print_action_seq curr_seq;
      print_endline "Pending sequence:";
      Util.print_action_seq pending_seq;
      (* let _ = read_line () in (); *)
      (*
      count := !count + 1;
      if !count > 10000 then
        exit 0
      else
        ();
      *)
      match pending_seq with
        [] -> raise (SanitisationError
                "Dive shouldn't be called empty pending sequence.")
      | a :: pending_seq' ->
          let curr_seq' = a :: curr_seq in
          let clean_set' = update_clean_set a clean_set in
          (* print_endline ("update clean set = " ^ (Util.string_of_object_list (ObjectSet.elements clean_set')));*)
          let curr_cost = cost curr_seq'
          and best_cost = cost best_seq in
          if curr_cost > best_cost then
            begin
            Printf.printf "current cost = %d, best cost = %d" curr_cost best_cost;
            print_endline "return 1";
            best_seq
            end
          else
            let cand = candidates pending_seq' curr_seq' clean_set' in
            (* print_string "(In Dive)";
            let _ = Util.print_action_seq cand in ();*)
            if pending_seq' = [] then
              if cand = [] then
                (*
                if curr_cost > best_cost then
                  begin
                  Printf.printf "current cost = %d, best cost = %d" curr_cost best_cost;
                  print_endline "return 2";
                  best_seq end
                else
                *)
                  begin
                  Printf.printf "current cost = %d, best cost = %d" curr_cost best_cost;
                  print_endline "return 3";
                  Util.print_action_seq curr_seq;
                  let _ = read_line() in ();
                  curr_seq
                  end
              else
                skid pending_seq' curr_seq' best_seq cand clean_set'
            else
              let best_seq' = dive pending_seq' curr_seq' best_seq clean_set' in
              skid pending_seq' curr_seq' best_seq' cand clean_set'

    (*----- dive - end -----------------------*)
    (*----- skid - begin -----------------------*)
    and skid pending_seq curr_seq best_seq cand clean_set =
(*      print_endline "SKID";
      print_endline "Candidates:";
      Util.print_action_seq cand; *)
      let rec loop best_seq = function
          [] -> best_seq
        | a :: cand' ->
            let pending_seq' = a :: pending_seq in
            let best_seq' = dive pending_seq' curr_seq best_seq clean_set in
            loop best_seq' cand'
      in
      if pending_seq = [] then
        loop best_seq cand
      else
        let best_seq' = dive pending_seq curr_seq best_seq clean_set in
        loop best_seq' cand
    (*----- skid - end -----------------------*)
    in
    (* a sequence with an unrealistically high cost. *)
    let costly = 
      let costly_action = {
          Action.name = "sanitise";
          Action.objects = [Object.hand]
      } in
      let rec loop acc n =
        if n = 0 then acc
        else loop (costly_action :: acc) (n - 1)
      in
      loop [] 10000
    in
    let clean_set = ObjectSet.filter
                      (fun o -> o.Object.initial_state = Object.CLEAN)
                      con.objects
    in
    dive seq [] costly clean_set
end

let d1 () =
  let door         = Object.new_obj "door" Object.DIRTY Object.DIRTY Object.inf
  and key          = Object.new_obj "key" Object.DIRTY Object.DIRTY 1
  and milk_packet  = Object.new_obj "milk packet" Object.DIRTY Object.DIRTY 2
  and milk         = Object.new_obj "milk" Object.DIRTY Object.CLEAN Object.inf
  and sink         = Object.new_obj "sink" Object.DIRTY Object.CLEAN Object.inf
  and scissors     = Object.new_obj "scissors" Object.CLEAN Object.CLEAN 1
  and container    = Object.new_obj "container" Object.CLEAN Object.CLEAN 1
  and bag          = Object.new_obj "bag" Object.DIRTY Object.DIRTY Object.inf
  and out_clothes  = Object.new_obj "outside clothes" Object.DIRTY Object.DIRTY Object.inf
  and home_clothes = Object.new_obj "home clothes" Object.CLEAN Object.CLEAN Object.inf
  and phone        = Object.new_obj "phone" Object.DIRTY Object.CLEAN 1
  and mask         = Object.new_obj "mask" Object.DIRTY Object.DIRTY 1
  and purse        = Object.new_obj "purse" Object.DIRTY Object.DIRTY Object.inf
  in
  let a1  = Action.new_action "Open door" [door]
  and a2  = Action.new_action "Keep key" [key]
  and a3  = Action.new_action "Take out milk packet" [bag; milk_packet]
  and a4  = Action.new_action "Keep milk packet" [milk_packet; sink]
  and a5  = Action.new_action "Take scissors" [scissors]
  and a6  = Action.new_action "Take container" [container]
  and a7  = Action.new_action "Cut packet" [scissors; milk_packet]
  and a8  = Action.new_action "Pour milk" [milk; milk_packet; container]
  and a9  = Action.new_action "Replace scissors" [scissors]
  and a10 = Action.new_action "Put container" [container]
  and a11 = Action.new_action "Dispose milk packet" [milk_packet]
  and a12 = Action.new_action "Replace bag" [bag]
  and a13 = Action.new_action "Take off outside clothes" [out_clothes]
  and a14 = Action.new_action "Put on home clothes" [home_clothes]
  and a15 = Action.new_action "Take out phone" [phone]
  and a16 = Action.new_action "Take out mask" [mask]
  and a17 = Action.new_action "Take out purse" [purse]
  in
  let n1  = DAG.new_node a1
  and n2  = DAG.new_node a2
  and n3  = DAG.new_node a3
  and n4  = DAG.new_node a4
  and n5  = DAG.new_node a5
  and n6  = DAG.new_node a6
  and n7  = DAG.new_node a7
  and n8  = DAG.new_node a8
  and n9  = DAG.new_node a9
  and n10 = DAG.new_node a10
  and n11 = DAG.new_node a11
  and n12 = DAG.new_node a12
  and n13 = DAG.new_node a13
  and n14 = DAG.new_node a14
  and n15 = DAG.new_node a15
  and n16 = DAG.new_node a16
  and n17 = DAG.new_node a17
  in
  let d1 = DAG.new_dag [n1; n2; n3; n4; n5; n6; n7; n8; n9; n10; n11; n12; n13; n14; n15; n16; n17 ] in
  let dag1 = DAG.set_root n1 d1
  in
  begin
    DAG.add_succs n1 [n2; n3; n15; n16; n17] dag1; 
    DAG.add_succs n3 [n4] dag1;   
    DAG.add_succs n4 [n5; n6; n12] dag1;
    DAG.add_succs n5 [n7] dag1;
    DAG.add_succs n6 [n8] dag1;
    DAG.add_succs n7 [n8] dag1;
    DAG.add_succs n8 [n9; n10; n11] dag1;
    DAG.add_succs n13 [n14] dag1;
    DAG.add_succs n15 [n13] dag1;
    DAG.add_succs n17 [n13] dag1;
  end;
  dag1

let context1 () =
  let door         = Object.new_obj "door" Object.DIRTY Object.DIRTY Object.inf
  and key          = Object.new_obj "key" Object.DIRTY Object.DIRTY 1
  and milk_packet  = Object.new_obj "milk packet" Object.DIRTY Object.DIRTY 2
  and milk         = Object.new_obj "milk" Object.DIRTY Object.CLEAN Object.inf
  and sink         = Object.new_obj "sink" Object.DIRTY Object.CLEAN Object.inf
  and scissors     = Object.new_obj "scissors" Object.CLEAN Object.CLEAN 1
  and container    = Object.new_obj "container" Object.CLEAN Object.CLEAN 1
  and bag          = Object.new_obj "bag" Object.DIRTY Object.DIRTY Object.inf
  and out_clothes  = Object.new_obj "outside clothes" Object.DIRTY Object.DIRTY Object.inf
  and home_clothes = Object.new_obj "home clothes" Object.CLEAN Object.CLEAN Object.inf
  and phone        = Object.new_obj "phone" Object.DIRTY Object.CLEAN 1
  and mask         = Object.new_obj "mask" Object.DIRTY Object.DIRTY 1
  and purse        = Object.new_obj "purse" Object.DIRTY Object.DIRTY Object.inf
  in
  let objects = [ door; key; milk_packet; milk; sink; scissors; container; bag; out_clothes;
    home_clothes; phone; mask; purse ]
  in
  let a1  = Action.new_action "Open door" [door]
  and a2  = Action.new_action "Keep key" [key]
  and a3  = Action.new_action "Take out milk packet" [bag; milk_packet]
  and a4  = Action.new_action "Keep milk packet" [milk_packet; sink]
  and a5  = Action.new_action "Take scissors" [scissors]
  and a6  = Action.new_action "Take container" [container]
  and a7  = Action.new_action "Cut packet" [scissors; milk_packet]
  and a8  = Action.new_action "Pour milk" [milk; milk_packet; container]
  and a9  = Action.new_action "Replace scissors" [scissors]
  and a10 = Action.new_action "Put container" [container]
  and a11 = Action.new_action "Dispose milk packet" [milk_packet]
  and a12 = Action.new_action "Replace bag" [bag]
  and a13 = Action.new_action "Take off outside clothes" [out_clothes]
  and a14 = Action.new_action "Put on home clothes" [home_clothes]
  and a15 = Action.new_action "Take out phone" [phone]
  and a16 = Action.new_action "Take out mask" [mask]
  and a17 = Action.new_action "Take out purse" [purse]
  in
  let actions = [ a1; a2; a3; a4; a5; a6; a7; a8; a9; a10;
    a11; a12; a13; a14; a15; a16; a17 ]
  in
  let n1  = DAG.new_node a1
  and n2  = DAG.new_node a2
  and n3  = DAG.new_node a3
  and n4  = DAG.new_node a4
  and n5  = DAG.new_node a5
  and n6  = DAG.new_node a6
  and n7  = DAG.new_node a7
  and n8  = DAG.new_node a8
  and n9  = DAG.new_node a9
  and n10 = DAG.new_node a10
  and n11 = DAG.new_node a11
  and n12 = DAG.new_node a12
  and n13 = DAG.new_node a13
  and n14 = DAG.new_node a14
  and n15 = DAG.new_node a15
  and n16 = DAG.new_node a16
  and n17 = DAG.new_node a17
  in
  let d1 = DAG.new_dag [n1; n2; n3; n4; n5; n6; n7; n8; n9; n10; n11; n12; n13; n14; n15; n16; n17 ] in
  let dag1 = DAG.set_root n1 d1
  in
  begin
    DAG.add_succs n1 [n2; n3; n15; n16; n17] dag1; 
    DAG.add_succs n3 [n4] dag1;   
    DAG.add_succs n4 [n5; n6; n12] dag1;
    DAG.add_succs n5 [n7] dag1;
    DAG.add_succs n6 [n8] dag1;
    DAG.add_succs n7 [n8] dag1;
    DAG.add_succs n8 [n9; n10; n11] dag1;
    DAG.add_succs n13 [n14] dag1;
    DAG.add_succs n15 [n13] dag1;
    DAG.add_succs n17 [n13] dag1;
  end;
  {
    Sanitisation.dag = dag1;
    Sanitisation.objects = ObjectSet.of_list objects;
    Sanitisation.actions = actions
  }


let t1 () =
  print_endline (DAG.string_of_dag (d1 ()))

let t2 () =
  let seq = Sequence.make_sequence (d1 ()) in
  Util.print_node_sequence seq

let t3 () =
  let c1 = context1 () in
  let dag = c1.Sanitisation.dag
  (* and actions = c1.Sanitisation.actions
  and objects = c1.Sanitisation.objects *)
  in
  let seq = Sequence.make_sequence dag in
  begin
    Util.print_node_sequence seq;
    let aseq = List.map (fun n -> n.DAG.value) seq in
    let final_seq = Sanitisation.insert aseq c1 in
    let fseq = List.map (fun a -> a.Action.name) final_seq in
    print_endline (List.fold_left (fun x y -> x ^ "\n" ^ y) "" fseq)
  end

let _ = t3 ()
