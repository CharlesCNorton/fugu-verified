(******************************************************************************)
(*                                                                            *)
(*               Fugu-Safety-Verified: Cross-Contamination Logic              *)
(*                                                                            *)
(*     Models toxin contamination across fugu parts (flesh/skin vs.           *)
(*     liver/ovaries/intestines) and kitchen tools across multiple stations.  *)
(*                                                                            *)
(*     Extended model features:                                               *)
(*       - Multiple preparation stations with independent tool sets           *)
(*       - Tool sharing/transfer between stations (contamination propagates)  *)
(*       - Batch contamination: shared trash affects all stations             *)
(*       - Temporal ordering: all toxic parts must be discarded before        *)
(*         any safe food can be prepared or served                            *)
(*                                                                            *)
(*     A policy checker accepts exactly the hygienic action sequences:        *)
(*       policy_state acts clean = Some _  <->  all_edible (run clean acts)   *)
(*                                                                            *)
(*     "I want to eat fugu, but I don't want to die."                         *)
(*     - Japanese Proverb                                                     *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 2025                                                    *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import Bool List.
Import ListNotations.

Set Implicit Arguments.

(** Parts, tools, stations, and dishes *)
Inductive Part := Flesh | Skin | Liver | Ovaries | Intestines.
Inductive LocalTool := Knife | Board | Plate | Hands.
Inductive StationId := S1 | S2.

Definition eqb_station (s1 s2 : StationId) : bool :=
  match s1, s2 with
  | S1, S1 => true
  | S2, S2 => true
  | _, _ => false
  end.

Section WithSkinToxicity.

Variable skin_is_lethal : bool.

Definition lethal_part (p : Part) : bool :=
  match p with
  | Flesh => false
  | Skin => skin_is_lethal
  | _ => true
  end.

Definition toxic_parts : list Part :=
  if skin_is_lethal then [Liver; Ovaries; Intestines; Skin]
  else [Liver; Ovaries; Intestines].

(** Station state: each station has its own tools *)
Record StationState := {
  knife_dirty : bool;
  board_dirty : bool;
  plate_dirty : bool;
  hands_dirty : bool
}.

Definition clean_station : StationState :=
  {| knife_dirty := false;
     board_dirty := false;
     plate_dirty := false;
     hands_dirty := false |}.

Definition dirty_of_local (st : StationState) (t : LocalTool) : bool :=
  match t with
  | Knife => knife_dirty st
  | Board => board_dirty st
  | Plate => plate_dirty st
  | Hands => hands_dirty st
  end.

Definition set_local_tool (t : LocalTool) (v : bool) (st : StationState) : StationState :=
  match t with
  | Knife => {| knife_dirty := v; board_dirty := board_dirty st;
                plate_dirty := plate_dirty st; hands_dirty := hands_dirty st |}
  | Board => {| knife_dirty := knife_dirty st; board_dirty := v;
                plate_dirty := plate_dirty st; hands_dirty := hands_dirty st |}
  | Plate => {| knife_dirty := knife_dirty st; board_dirty := board_dirty st;
                plate_dirty := v; hands_dirty := hands_dirty st |}
  | Hands => {| knife_dirty := knife_dirty st; board_dirty := board_dirty st;
                plate_dirty := plate_dirty st; hands_dirty := v |}
  end.

(** Global state: two stations, shared trash, dish edibility, toxic part tracking *)
Record State := {
  station1 : StationState;
  station2 : StationState;
  trash_dirty : bool;
  dish1_edible : bool;
  dish2_edible : bool;
  liver_discarded : bool;
  ovaries_discarded : bool;
  intestines_discarded : bool;
  skin_discarded : bool
}.

Definition get_station (s : State) (sid : StationId) : StationState :=
  match sid with
  | S1 => station1 s
  | S2 => station2 s
  end.

Definition set_station (sid : StationId) (st : StationState) (s : State) : State :=
  match sid with
  | S1 => {| station1 := st; station2 := station2 s;
             trash_dirty := trash_dirty s;
             dish1_edible := dish1_edible s; dish2_edible := dish2_edible s;
             liver_discarded := liver_discarded s;
             ovaries_discarded := ovaries_discarded s;
             intestines_discarded := intestines_discarded s;
             skin_discarded := skin_discarded s |}
  | S2 => {| station1 := station1 s; station2 := st;
             trash_dirty := trash_dirty s;
             dish1_edible := dish1_edible s; dish2_edible := dish2_edible s;
             liver_discarded := liver_discarded s;
             ovaries_discarded := ovaries_discarded s;
             intestines_discarded := intestines_discarded s;
             skin_discarded := skin_discarded s |}
  end.

Definition get_edible (s : State) (sid : StationId) : bool :=
  match sid with
  | S1 => dish1_edible s
  | S2 => dish2_edible s
  end.

Definition set_edible (sid : StationId) (v : bool) (s : State) : State :=
  match sid with
  | S1 => {| station1 := station1 s; station2 := station2 s;
             trash_dirty := trash_dirty s;
             dish1_edible := v; dish2_edible := dish2_edible s;
             liver_discarded := liver_discarded s;
             ovaries_discarded := ovaries_discarded s;
             intestines_discarded := intestines_discarded s;
             skin_discarded := skin_discarded s |}
  | S2 => {| station1 := station1 s; station2 := station2 s;
             trash_dirty := trash_dirty s;
             dish1_edible := dish1_edible s; dish2_edible := v;
             liver_discarded := liver_discarded s;
             ovaries_discarded := ovaries_discarded s;
             intestines_discarded := intestines_discarded s;
             skin_discarded := skin_discarded s |}
  end.

Definition all_toxic_discarded (s : State) : bool :=
  liver_discarded s && ovaries_discarded s && intestines_discarded s &&
  (negb skin_is_lethal || skin_discarded s).

Definition mark_discarded (p : Part) (s : State) : State :=
  match p with
  | Liver => {| station1 := station1 s; station2 := station2 s;
                trash_dirty := trash_dirty s;
                dish1_edible := dish1_edible s; dish2_edible := dish2_edible s;
                liver_discarded := true;
                ovaries_discarded := ovaries_discarded s;
                intestines_discarded := intestines_discarded s;
                skin_discarded := skin_discarded s |}
  | Ovaries => {| station1 := station1 s; station2 := station2 s;
                  trash_dirty := trash_dirty s;
                  dish1_edible := dish1_edible s; dish2_edible := dish2_edible s;
                  liver_discarded := liver_discarded s;
                  ovaries_discarded := true;
                  intestines_discarded := intestines_discarded s;
                  skin_discarded := skin_discarded s |}
  | Intestines => {| station1 := station1 s; station2 := station2 s;
                     trash_dirty := trash_dirty s;
                     dish1_edible := dish1_edible s; dish2_edible := dish2_edible s;
                     liver_discarded := liver_discarded s;
                     ovaries_discarded := ovaries_discarded s;
                     intestines_discarded := true;
                     skin_discarded := skin_discarded s |}
  | Skin => {| station1 := station1 s; station2 := station2 s;
               trash_dirty := trash_dirty s;
               dish1_edible := dish1_edible s; dish2_edible := dish2_edible s;
               liver_discarded := liver_discarded s;
               ovaries_discarded := ovaries_discarded s;
               intestines_discarded := intestines_discarded s;
               skin_discarded := true |}
  | Flesh => s
  end.

Definition clean_state : State :=
  {| station1 := clean_station;
     station2 := clean_station;
     trash_dirty := false;
     dish1_edible := true;
     dish2_edible := true;
     liver_discarded := false;
     ovaries_discarded := false;
     intestines_discarded := false;
     skin_discarded := false |}.

(** Actions *)
Inductive Action :=
| Wash (sid : StationId) (t : LocalTool)
| Cut (sid : StationId) (p : Part)
| Transfer (sid : StationId) (src dst : LocalTool)
| Discard (sid : StationId) (p : Part)
| MoveTool (src_sid dst_sid : StationId) (t : LocalTool).

(** One transition step *)
Definition step (s : State) (a : Action) : State :=
  match a with
  | Wash sid t =>
      let st := get_station s sid in
      let st' := set_local_tool t false st in
      set_station sid st' s

  | Cut sid p =>
      let st := get_station s sid in
      let lp := lethal_part p in
      let any_dirty := knife_dirty st || board_dirty st || hands_dirty st in
      let kbh := any_dirty || lp in
      let st' := {| knife_dirty := kbh; board_dirty := kbh;
                    plate_dirty := plate_dirty st || lp; hands_dirty := kbh |} in
      let ed := get_edible s sid in
      let ed' :=
        if lp then ed
        else if any_dirty then false
        else if all_toxic_discarded s then ed
        else false in
      set_edible sid ed' (set_station sid st' s)

  | Transfer sid src dst =>
      let st := get_station s sid in
      let d := dirty_of_local st src || dirty_of_local st dst || hands_dirty st in
      let st' := set_local_tool dst d (set_local_tool src d st) in
      let st'' := set_local_tool Hands d st' in
      let ed := get_edible s sid in
      let ed' :=
        if d then false
        else if all_toxic_discarded s then ed
        else false in
      set_edible sid ed' (set_station sid st'' s)

  | Discard sid p =>
      let st := get_station s sid in
      let hd := hands_dirty st || dirty_of_local st Board in
      let td := trash_dirty s || hd in
      let st' := set_local_tool Hands hd st in
      let s' := set_station sid st' s in
      let s'' := {| station1 := station1 s'; station2 := station2 s';
                    trash_dirty := td;
                    dish1_edible := dish1_edible s'; dish2_edible := dish2_edible s';
                    liver_discarded := liver_discarded s';
                    ovaries_discarded := ovaries_discarded s';
                    intestines_discarded := intestines_discarded s';
                    skin_discarded := skin_discarded s' |} in
      mark_discarded p s''

  | MoveTool src_sid dst_sid t =>
      let src_st := get_station s src_sid in
      let dst_st := get_station s dst_sid in
      let tool_dirty := dirty_of_local src_st t in
      let dst_st' := set_local_tool t tool_dirty dst_st in
      let dst_hands := hands_dirty dst_st || tool_dirty in
      let dst_st'' := set_local_tool Hands dst_hands dst_st' in
      set_station dst_sid dst_st'' s
  end.

Fixpoint run (s : State) (acts : list Action) : State :=
  match acts with
  | [] => s
  | a :: rest => run (step s a) rest
  end.

Definition all_edible (s : State) : bool :=
  dish1_edible s && dish2_edible s.

(******************************************************************************)
(* Basic invariants                                                           *)
(******************************************************************************)

Lemma step_edible_false :
  forall s sid a, get_edible s sid = false -> get_edible (step s a) sid = false.
Proof.
  intros s sid a Hed.
  destruct a as [sid' t|sid' p|sid' src dst|sid' p|src_sid dst_sid t]; simpl.
  - destruct sid, sid'; simpl in *; exact Hed.
  - destruct sid, sid'; simpl in *; try exact Hed.
    + destruct (lethal_part p); simpl.
      * exact Hed.
      * destruct (knife_dirty (station1 s) || board_dirty (station1 s) || hands_dirty (station1 s)); simpl; try reflexivity.
        destruct (all_toxic_discarded s); simpl; [exact Hed | reflexivity].
    + destruct (lethal_part p); simpl.
      * exact Hed.
      * destruct (knife_dirty (station2 s) || board_dirty (station2 s) || hands_dirty (station2 s)); simpl; try reflexivity.
        destruct (all_toxic_discarded s); simpl; [exact Hed | reflexivity].
  - destruct sid, sid'; simpl in *; try exact Hed.
    + destruct (dirty_of_local (station1 s) src || dirty_of_local (station1 s) dst || hands_dirty (station1 s)); simpl; try reflexivity.
      destruct (all_toxic_discarded s); simpl; [exact Hed | reflexivity].
    + destruct (dirty_of_local (station2 s) src || dirty_of_local (station2 s) dst || hands_dirty (station2 s)); simpl; try reflexivity.
      destruct (all_toxic_discarded s); simpl; [exact Hed | reflexivity].
  - destruct sid, sid', p; simpl in *; exact Hed.
  - destruct sid, src_sid, dst_sid; simpl in *; exact Hed.
Qed.

Lemma run_edible_false :
  forall acts s sid, get_edible s sid = false -> get_edible (run s acts) sid = false.
Proof.
  induction acts as [|a rest IH]; intros s sid Hed; simpl.
  - exact Hed.
  - apply IH. apply step_edible_false. exact Hed.
Qed.

Lemma step_all_edible_false :
  forall s a, all_edible s = false -> all_edible (step s a) = false.
Proof.
  intros s a Hed.
  unfold all_edible in *.
  apply Bool.andb_false_iff in Hed.
  apply Bool.andb_false_iff.
  destruct Hed as [H1 | H2].
  - left. apply (step_edible_false s S1 a). exact H1.
  - right. apply (step_edible_false s S2 a). exact H2.
Qed.

Lemma run_all_edible_false :
  forall acts s, all_edible s = false -> all_edible (run s acts) = false.
Proof.
  induction acts as [|a rest IH]; intros s Hed; simpl.
  - exact Hed.
  - apply IH. apply step_all_edible_false. exact Hed.
Qed.

(******************************************************************************)
(* Policy checker                                                             *)
(******************************************************************************)

Record PolicyState := {
  ps_s1_knife : bool;
  ps_s1_board : bool;
  ps_s1_plate : bool;
  ps_s1_hands : bool;
  ps_s2_knife : bool;
  ps_s2_board : bool;
  ps_s2_plate : bool;
  ps_s2_hands : bool;
  ps_trash : bool;
  ps_liver : bool;
  ps_ovaries : bool;
  ps_intestines : bool;
  ps_skin : bool
}.

Definition clean_policy : PolicyState :=
  {| ps_s1_knife := false; ps_s1_board := false;
     ps_s1_plate := false; ps_s1_hands := false;
     ps_s2_knife := false; ps_s2_board := false;
     ps_s2_plate := false; ps_s2_hands := false;
     ps_trash := false;
     ps_liver := false; ps_ovaries := false;
     ps_intestines := false; ps_skin := false |}.

Definition ps_get_tool (ps : PolicyState) (sid : StationId) (t : LocalTool) : bool :=
  match sid, t with
  | S1, Knife => ps_s1_knife ps
  | S1, Board => ps_s1_board ps
  | S1, Plate => ps_s1_plate ps
  | S1, Hands => ps_s1_hands ps
  | S2, Knife => ps_s2_knife ps
  | S2, Board => ps_s2_board ps
  | S2, Plate => ps_s2_plate ps
  | S2, Hands => ps_s2_hands ps
  end.

Definition ps_set_tool (sid : StationId) (t : LocalTool) (v : bool) (ps : PolicyState) : PolicyState :=
  match sid, t with
  | S1, Knife => {| ps_s1_knife := v; ps_s1_board := ps_s1_board ps;
                    ps_s1_plate := ps_s1_plate ps; ps_s1_hands := ps_s1_hands ps;
                    ps_s2_knife := ps_s2_knife ps; ps_s2_board := ps_s2_board ps;
                    ps_s2_plate := ps_s2_plate ps; ps_s2_hands := ps_s2_hands ps;
                    ps_trash := ps_trash ps;
                    ps_liver := ps_liver ps; ps_ovaries := ps_ovaries ps;
                    ps_intestines := ps_intestines ps; ps_skin := ps_skin ps |}
  | S1, Board => {| ps_s1_knife := ps_s1_knife ps; ps_s1_board := v;
                    ps_s1_plate := ps_s1_plate ps; ps_s1_hands := ps_s1_hands ps;
                    ps_s2_knife := ps_s2_knife ps; ps_s2_board := ps_s2_board ps;
                    ps_s2_plate := ps_s2_plate ps; ps_s2_hands := ps_s2_hands ps;
                    ps_trash := ps_trash ps;
                    ps_liver := ps_liver ps; ps_ovaries := ps_ovaries ps;
                    ps_intestines := ps_intestines ps; ps_skin := ps_skin ps |}
  | S1, Plate => {| ps_s1_knife := ps_s1_knife ps; ps_s1_board := ps_s1_board ps;
                    ps_s1_plate := v; ps_s1_hands := ps_s1_hands ps;
                    ps_s2_knife := ps_s2_knife ps; ps_s2_board := ps_s2_board ps;
                    ps_s2_plate := ps_s2_plate ps; ps_s2_hands := ps_s2_hands ps;
                    ps_trash := ps_trash ps;
                    ps_liver := ps_liver ps; ps_ovaries := ps_ovaries ps;
                    ps_intestines := ps_intestines ps; ps_skin := ps_skin ps |}
  | S1, Hands => {| ps_s1_knife := ps_s1_knife ps; ps_s1_board := ps_s1_board ps;
                    ps_s1_plate := ps_s1_plate ps; ps_s1_hands := v;
                    ps_s2_knife := ps_s2_knife ps; ps_s2_board := ps_s2_board ps;
                    ps_s2_plate := ps_s2_plate ps; ps_s2_hands := ps_s2_hands ps;
                    ps_trash := ps_trash ps;
                    ps_liver := ps_liver ps; ps_ovaries := ps_ovaries ps;
                    ps_intestines := ps_intestines ps; ps_skin := ps_skin ps |}
  | S2, Knife => {| ps_s1_knife := ps_s1_knife ps; ps_s1_board := ps_s1_board ps;
                    ps_s1_plate := ps_s1_plate ps; ps_s1_hands := ps_s1_hands ps;
                    ps_s2_knife := v; ps_s2_board := ps_s2_board ps;
                    ps_s2_plate := ps_s2_plate ps; ps_s2_hands := ps_s2_hands ps;
                    ps_trash := ps_trash ps;
                    ps_liver := ps_liver ps; ps_ovaries := ps_ovaries ps;
                    ps_intestines := ps_intestines ps; ps_skin := ps_skin ps |}
  | S2, Board => {| ps_s1_knife := ps_s1_knife ps; ps_s1_board := ps_s1_board ps;
                    ps_s1_plate := ps_s1_plate ps; ps_s1_hands := ps_s1_hands ps;
                    ps_s2_knife := ps_s2_knife ps; ps_s2_board := v;
                    ps_s2_plate := ps_s2_plate ps; ps_s2_hands := ps_s2_hands ps;
                    ps_trash := ps_trash ps;
                    ps_liver := ps_liver ps; ps_ovaries := ps_ovaries ps;
                    ps_intestines := ps_intestines ps; ps_skin := ps_skin ps |}
  | S2, Plate => {| ps_s1_knife := ps_s1_knife ps; ps_s1_board := ps_s1_board ps;
                    ps_s1_plate := ps_s1_plate ps; ps_s1_hands := ps_s1_hands ps;
                    ps_s2_knife := ps_s2_knife ps; ps_s2_board := ps_s2_board ps;
                    ps_s2_plate := v; ps_s2_hands := ps_s2_hands ps;
                    ps_trash := ps_trash ps;
                    ps_liver := ps_liver ps; ps_ovaries := ps_ovaries ps;
                    ps_intestines := ps_intestines ps; ps_skin := ps_skin ps |}
  | S2, Hands => {| ps_s1_knife := ps_s1_knife ps; ps_s1_board := ps_s1_board ps;
                    ps_s1_plate := ps_s1_plate ps; ps_s1_hands := ps_s1_hands ps;
                    ps_s2_knife := ps_s2_knife ps; ps_s2_board := ps_s2_board ps;
                    ps_s2_plate := ps_s2_plate ps; ps_s2_hands := v;
                    ps_trash := ps_trash ps;
                    ps_liver := ps_liver ps; ps_ovaries := ps_ovaries ps;
                    ps_intestines := ps_intestines ps; ps_skin := ps_skin ps |}
  end.

Definition ps_all_toxic_discarded (ps : PolicyState) : bool :=
  ps_liver ps && ps_ovaries ps && ps_intestines ps &&
  (negb skin_is_lethal || ps_skin ps).

Definition ps_mark_discarded (p : Part) (ps : PolicyState) : PolicyState :=
  match p with
  | Liver => {| ps_s1_knife := ps_s1_knife ps; ps_s1_board := ps_s1_board ps;
                ps_s1_plate := ps_s1_plate ps; ps_s1_hands := ps_s1_hands ps;
                ps_s2_knife := ps_s2_knife ps; ps_s2_board := ps_s2_board ps;
                ps_s2_plate := ps_s2_plate ps; ps_s2_hands := ps_s2_hands ps;
                ps_trash := ps_trash ps;
                ps_liver := true; ps_ovaries := ps_ovaries ps;
                ps_intestines := ps_intestines ps; ps_skin := ps_skin ps |}
  | Ovaries => {| ps_s1_knife := ps_s1_knife ps; ps_s1_board := ps_s1_board ps;
                  ps_s1_plate := ps_s1_plate ps; ps_s1_hands := ps_s1_hands ps;
                  ps_s2_knife := ps_s2_knife ps; ps_s2_board := ps_s2_board ps;
                  ps_s2_plate := ps_s2_plate ps; ps_s2_hands := ps_s2_hands ps;
                  ps_trash := ps_trash ps;
                  ps_liver := ps_liver ps; ps_ovaries := true;
                  ps_intestines := ps_intestines ps; ps_skin := ps_skin ps |}
  | Intestines => {| ps_s1_knife := ps_s1_knife ps; ps_s1_board := ps_s1_board ps;
                     ps_s1_plate := ps_s1_plate ps; ps_s1_hands := ps_s1_hands ps;
                     ps_s2_knife := ps_s2_knife ps; ps_s2_board := ps_s2_board ps;
                     ps_s2_plate := ps_s2_plate ps; ps_s2_hands := ps_s2_hands ps;
                     ps_trash := ps_trash ps;
                     ps_liver := ps_liver ps; ps_ovaries := ps_ovaries ps;
                     ps_intestines := true; ps_skin := ps_skin ps |}
  | Skin => {| ps_s1_knife := ps_s1_knife ps; ps_s1_board := ps_s1_board ps;
               ps_s1_plate := ps_s1_plate ps; ps_s1_hands := ps_s1_hands ps;
               ps_s2_knife := ps_s2_knife ps; ps_s2_board := ps_s2_board ps;
               ps_s2_plate := ps_s2_plate ps; ps_s2_hands := ps_s2_hands ps;
               ps_trash := ps_trash ps;
               ps_liver := ps_liver ps; ps_ovaries := ps_ovaries ps;
               ps_intestines := ps_intestines ps; ps_skin := true |}
  | Flesh => ps
  end.

Fixpoint policy_check (acts : list Action) (ps : PolicyState) : option PolicyState :=
  match acts with
  | [] => Some ps

  | Wash sid t :: rest =>
      policy_check rest (ps_set_tool sid t false ps)

  | Cut sid p :: rest =>
      let kd := ps_get_tool ps sid Knife in
      let bd := ps_get_tool ps sid Board in
      let hd := ps_get_tool ps sid Hands in
      if lethal_part p
      then let ps' := ps_set_tool sid Plate true (ps_set_tool sid Hands true (ps_set_tool sid Board true (ps_set_tool sid Knife true ps))) in
           policy_check rest ps'
      else if kd || bd || hd then None
           else if ps_all_toxic_discarded ps then policy_check rest ps
                else None

  | Transfer sid src dst :: rest =>
      let sd := ps_get_tool ps sid src in
      let dd := ps_get_tool ps sid dst in
      let hd := ps_get_tool ps sid Hands in
      if sd || dd || hd then None
      else if ps_all_toxic_discarded ps then policy_check rest ps
           else None

  | Discard sid p :: rest =>
      let bd := ps_get_tool ps sid Board in
      let hd := ps_get_tool ps sid Hands in
      let hd' := hd || bd in
      let td' := ps_trash ps || hd' in
      let ps' := {| ps_s1_knife := ps_s1_knife ps; ps_s1_board := ps_s1_board ps;
                    ps_s1_plate := ps_s1_plate ps;
                    ps_s1_hands := if eqb_station sid S1 then hd' else ps_s1_hands ps;
                    ps_s2_knife := ps_s2_knife ps; ps_s2_board := ps_s2_board ps;
                    ps_s2_plate := ps_s2_plate ps;
                    ps_s2_hands := if eqb_station sid S2 then hd' else ps_s2_hands ps;
                    ps_trash := td';
                    ps_liver := ps_liver ps; ps_ovaries := ps_ovaries ps;
                    ps_intestines := ps_intestines ps; ps_skin := ps_skin ps |} in
      policy_check rest (ps_mark_discarded p ps')

  | MoveTool src_sid dst_sid t :: rest =>
      let tool_dirty := ps_get_tool ps src_sid t in
      let dst_hd := ps_get_tool ps dst_sid Hands in
      let dst_hd' := dst_hd || tool_dirty in
      let ps' := ps_set_tool dst_sid Hands dst_hd' (ps_set_tool dst_sid t tool_dirty ps) in
      policy_check rest ps'
  end.

Definition hygienic (acts : list Action) : Prop :=
  exists ps, policy_check acts clean_policy = Some ps.

(******************************************************************************)
(* State correspondence                                                       *)
(******************************************************************************)

Definition state_matches_policy (s : State) (ps : PolicyState) : Prop :=
  knife_dirty (station1 s) = ps_s1_knife ps /\
  board_dirty (station1 s) = ps_s1_board ps /\
  plate_dirty (station1 s) = ps_s1_plate ps /\
  hands_dirty (station1 s) = ps_s1_hands ps /\
  knife_dirty (station2 s) = ps_s2_knife ps /\
  board_dirty (station2 s) = ps_s2_board ps /\
  plate_dirty (station2 s) = ps_s2_plate ps /\
  hands_dirty (station2 s) = ps_s2_hands ps /\
  trash_dirty s = ps_trash ps /\
  liver_discarded s = ps_liver ps /\
  ovaries_discarded s = ps_ovaries ps /\
  intestines_discarded s = ps_intestines ps /\
  skin_discarded s = ps_skin ps /\
  dish1_edible s = true /\
  dish2_edible s = true.

Lemma clean_state_matches_policy :
  state_matches_policy clean_state clean_policy.
Proof.
  unfold state_matches_policy, clean_state, clean_policy, clean_station.
  repeat split; reflexivity.
Qed.

(******************************************************************************)
(* Soundness: policy acceptance implies all dishes remain edible              *)
(******************************************************************************)

Lemma matches_implies_edible :
  forall s ps,
    state_matches_policy s ps ->
    all_edible s = true.
Proof.
  intros s ps Hm.
  destruct Hm as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [H14 H15]]]]]]]]]]]]]].
  unfold all_edible.
  rewrite H14, H15.
  reflexivity.
Qed.

Lemma step_wash_matches :
  forall s ps sid t,
    state_matches_policy s ps ->
    state_matches_policy (step s (Wash sid t)) (ps_set_tool sid t false ps).
Proof.
  intros s ps sid t Hm.
  destruct Hm as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 H15]]]]]]]]]]]]]].
  unfold state_matches_policy.
  destruct sid, t; simpl; repeat split; assumption.
Qed.

Lemma step_cut_lethal_matches :
  forall s ps sid p,
    state_matches_policy s ps ->
    lethal_part p = true ->
    state_matches_policy (step s (Cut sid p))
      (ps_set_tool sid Plate true (ps_set_tool sid Hands true (ps_set_tool sid Board true (ps_set_tool sid Knife true ps)))).
Proof.
  intros s ps sid p Hm Hlp.
  destruct Hm as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 H15]]]]]]]]]]]]]].
  unfold state_matches_policy.
  destruct sid; simpl; rewrite Hlp; rewrite ?Bool.orb_true_r; simpl;
  repeat split; try reflexivity; assumption.
Qed.

Lemma matches_tools_eq :
  forall s ps sid t,
    state_matches_policy s ps ->
    dirty_of_local (get_station s sid) t = ps_get_tool ps sid t.
Proof.
  intros s ps sid t Hm.
  destruct Hm as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 H15]]]]]]]]]]]]]].
  destruct sid, t; simpl; assumption.
Qed.

Lemma matches_toxic_eq :
  forall s ps,
    state_matches_policy s ps ->
    all_toxic_discarded s = ps_all_toxic_discarded ps.
Proof.
  intros s ps Hm.
  destruct Hm as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 H15]]]]]]]]]]]]]].
  unfold all_toxic_discarded, ps_all_toxic_discarded.
  rewrite H10, H11, H12, H13.
  reflexivity.
Qed.

Lemma step_cut_safe_matches :
  forall s ps sid p,
    state_matches_policy s ps ->
    lethal_part p = false ->
    ps_get_tool ps sid Knife = false ->
    ps_get_tool ps sid Board = false ->
    ps_get_tool ps sid Hands = false ->
    ps_all_toxic_discarded ps = true ->
    state_matches_policy (step s (Cut sid p)) ps.
Proof.
  intros s ps sid p Hm Hlp Hk Hb Hh Htox.
  destruct Hm as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 H15]]]]]]]]]]]]]].
  unfold state_matches_policy.
  assert (Htox' : all_toxic_discarded s = true).
  { unfold all_toxic_discarded, ps_all_toxic_discarded in *.
    rewrite H10, H11, H12, H13. exact Htox. }
  destruct sid; unfold ps_get_tool in Hk, Hb, Hh; simpl in Hk, Hb, Hh; simpl.
  - rewrite Hlp.
    rewrite H1, H2, H4, Hk, Hb, Hh. simpl.
    rewrite Htox'. simpl.
    rewrite Bool.orb_false_r.
    repeat split; try reflexivity; try assumption.
  - rewrite Hlp.
    rewrite H5, H6, H8, Hk, Hb, Hh. simpl.
    rewrite Htox'. simpl.
    rewrite Bool.orb_false_r.
    repeat split; try reflexivity; try assumption.
Qed.

Lemma step_transfer_matches :
  forall s ps sid src dst,
    state_matches_policy s ps ->
    ps_get_tool ps sid src = false ->
    ps_get_tool ps sid dst = false ->
    ps_get_tool ps sid Hands = false ->
    ps_all_toxic_discarded ps = true ->
    state_matches_policy (step s (Transfer sid src dst)) ps.
Proof.
  intros s ps sid src dst Hm Hsrc Hdst Hh Htox.
  destruct Hm as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 H15]]]]]]]]]]]]]].
  unfold state_matches_policy.
  assert (Htox' : all_toxic_discarded s = true).
  { unfold all_toxic_discarded, ps_all_toxic_discarded in *.
    rewrite H10, H11, H12, H13. exact Htox. }
  destruct sid; unfold ps_get_tool in Hsrc, Hdst, Hh; simpl in Hsrc, Hdst, Hh; simpl.
  - assert (Hsrc' : dirty_of_local (station1 s) src = false).
    { destruct src; simpl in *; congruence. }
    assert (Hdst' : dirty_of_local (station1 s) dst = false).
    { destruct dst; simpl in *; congruence. }
    assert (Hh' : hands_dirty (station1 s) = false) by congruence.
    rewrite Hsrc', Hdst', Hh'. simpl.
    rewrite Htox'. simpl.
    destruct src, dst; simpl in *;
    (repeat split; first [assumption | reflexivity | congruence]).
  - assert (Hsrc' : dirty_of_local (station2 s) src = false).
    { destruct src; simpl in *; congruence. }
    assert (Hdst' : dirty_of_local (station2 s) dst = false).
    { destruct dst; simpl in *; congruence. }
    assert (Hh' : hands_dirty (station2 s) = false) by congruence.
    rewrite Hsrc', Hdst', Hh'. simpl.
    rewrite Htox'. simpl.
    destruct src, dst; simpl in *;
    (repeat split; first [assumption | reflexivity | congruence]).
Qed.

Lemma step_discard_matches :
  forall s ps sid p,
    state_matches_policy s ps ->
    state_matches_policy (step s (Discard sid p))
      (ps_mark_discarded p
        {| ps_s1_knife := ps_s1_knife ps; ps_s1_board := ps_s1_board ps;
           ps_s1_plate := ps_s1_plate ps;
           ps_s1_hands := if eqb_station sid S1
                          then ps_get_tool ps sid Hands || ps_get_tool ps sid Board
                          else ps_s1_hands ps;
           ps_s2_knife := ps_s2_knife ps; ps_s2_board := ps_s2_board ps;
           ps_s2_plate := ps_s2_plate ps;
           ps_s2_hands := if eqb_station sid S2
                          then ps_get_tool ps sid Hands || ps_get_tool ps sid Board
                          else ps_s2_hands ps;
           ps_trash := ps_trash ps ||
                       (ps_get_tool ps sid Hands || ps_get_tool ps sid Board);
           ps_liver := ps_liver ps; ps_ovaries := ps_ovaries ps;
           ps_intestines := ps_intestines ps; ps_skin := ps_skin ps |}).
Proof.
  intros s ps sid p Hm.
  destruct Hm as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 H15]]]]]]]]]]]]]].
  unfold state_matches_policy.
  destruct sid, p; simpl;
  repeat split; try assumption; try reflexivity;
  try (rewrite H4; reflexivity);
  try (rewrite H8; reflexivity);
  try (rewrite H4, H2; reflexivity);
  try (rewrite H8, H6; reflexivity);
  try (rewrite H9, H4, H2; reflexivity);
  try (rewrite H9, H8, H6; reflexivity).
Qed.

Lemma step_movetool_matches :
  forall s ps src_sid dst_sid t,
    state_matches_policy s ps ->
    state_matches_policy (step s (MoveTool src_sid dst_sid t))
      (ps_set_tool dst_sid Hands
        (ps_get_tool ps dst_sid Hands || ps_get_tool ps src_sid t)
        (ps_set_tool dst_sid t (ps_get_tool ps src_sid t) ps)).
Proof.
  intros s ps src_sid dst_sid t Hm.
  destruct Hm as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 H15]]]]]]]]]]]]]].
  unfold state_matches_policy.
  destruct src_sid, dst_sid, t; simpl;
  repeat split; try assumption; try reflexivity;
  try (rewrite H1; reflexivity);
  try (rewrite H2; reflexivity);
  try (rewrite H3; reflexivity);
  try (rewrite H4; reflexivity);
  try (rewrite H5; reflexivity);
  try (rewrite H6; reflexivity);
  try (rewrite H7; reflexivity);
  try (rewrite H8; reflexivity);
  try (rewrite H4, H1; reflexivity);
  try (rewrite H4, H2; reflexivity);
  try (rewrite H4, H3; reflexivity);
  try (rewrite H4, H4; reflexivity);
  try (rewrite H8, H1; reflexivity);
  try (rewrite H8, H2; reflexivity);
  try (rewrite H8, H3; reflexivity);
  try (rewrite H8, H4; reflexivity);
  try (rewrite H4, H5; reflexivity);
  try (rewrite H4, H6; reflexivity);
  try (rewrite H4, H7; reflexivity);
  try (rewrite H4, H8; reflexivity);
  try (rewrite H8, H5; reflexivity);
  try (rewrite H8, H6; reflexivity);
  try (rewrite H8, H7; reflexivity);
  try (rewrite H8, H8; reflexivity).
Qed.

(******************************************************************************)
(* Main soundness theorem - via micro-lemmas                                   *)
(******************************************************************************)

Lemma step_preserves_run_edible :
  forall s a rest,
    all_edible (run (step s a) rest) = true ->
    all_edible (run s (a :: rest)) = true.
Proof.
  intros s a rest H.
  simpl. exact H.
Qed.

Lemma policy_wash_step :
  forall s ps sid t,
    state_matches_policy s ps ->
    state_matches_policy (step s (Wash sid t)) (ps_set_tool sid t false ps).
Proof.
  exact step_wash_matches.
Qed.

Lemma policy_cut_lethal_step :
  forall s ps sid p,
    state_matches_policy s ps ->
    lethal_part p = true ->
    state_matches_policy (step s (Cut sid p))
      (ps_set_tool sid Plate true (ps_set_tool sid Hands true (ps_set_tool sid Board true (ps_set_tool sid Knife true ps)))).
Proof.
  exact step_cut_lethal_matches.
Qed.

Lemma policy_cut_safe_step :
  forall s ps sid p,
    state_matches_policy s ps ->
    lethal_part p = false ->
    ps_get_tool ps sid Knife = false ->
    ps_get_tool ps sid Board = false ->
    ps_get_tool ps sid Hands = false ->
    ps_all_toxic_discarded ps = true ->
    state_matches_policy (step s (Cut sid p)) ps.
Proof.
  exact step_cut_safe_matches.
Qed.

Lemma policy_transfer_step :
  forall s ps sid src dst,
    state_matches_policy s ps ->
    ps_get_tool ps sid src = false ->
    ps_get_tool ps sid dst = false ->
    ps_get_tool ps sid Hands = false ->
    ps_all_toxic_discarded ps = true ->
    state_matches_policy (step s (Transfer sid src dst)) ps.
Proof.
  exact step_transfer_matches.
Qed.

Definition discard_policy_update (ps : PolicyState) (sid : StationId) (p : Part) : PolicyState :=
  let bd := ps_get_tool ps sid Board in
  let hd := ps_get_tool ps sid Hands in
  let hd' := hd || bd in
  let td' := ps_trash ps || hd' in
  ps_mark_discarded p
    {| ps_s1_knife := ps_s1_knife ps;
       ps_s1_board := ps_s1_board ps;
       ps_s1_plate := ps_s1_plate ps;
       ps_s1_hands := if eqb_station sid S1 then hd' else ps_s1_hands ps;
       ps_s2_knife := ps_s2_knife ps;
       ps_s2_board := ps_s2_board ps;
       ps_s2_plate := ps_s2_plate ps;
       ps_s2_hands := if eqb_station sid S2 then hd' else ps_s2_hands ps;
       ps_trash := td';
       ps_liver := ps_liver ps;
       ps_ovaries := ps_ovaries ps;
       ps_intestines := ps_intestines ps;
       ps_skin := ps_skin ps |}.

Lemma policy_discard_step :
  forall s ps sid p,
    state_matches_policy s ps ->
    state_matches_policy (step s (Discard sid p)) (discard_policy_update ps sid p).
Proof.
  intros s ps sid p Hm.
  unfold discard_policy_update.
  apply step_discard_matches. exact Hm.
Qed.

Definition movetool_policy_update (ps : PolicyState) (src_sid dst_sid : StationId) (t : LocalTool) : PolicyState :=
  let tool_dirty := ps_get_tool ps src_sid t in
  let dst_hd := ps_get_tool ps dst_sid Hands in
  let dst_hd' := dst_hd || tool_dirty in
  ps_set_tool dst_sid Hands dst_hd' (ps_set_tool dst_sid t tool_dirty ps).

Lemma policy_movetool_step :
  forall s ps src_sid dst_sid t,
    state_matches_policy s ps ->
    state_matches_policy (step s (MoveTool src_sid dst_sid t)) (movetool_policy_update ps src_sid dst_sid t).
Proof.
  intros s ps src_sid dst_sid t Hm.
  unfold movetool_policy_update.
  apply step_movetool_matches. exact Hm.
Qed.

Lemma policy_check_discard_unfold :
  forall ps sid p rest,
    policy_check (Discard sid p :: rest) ps =
    policy_check rest (discard_policy_update ps sid p).
Proof.
  intros ps sid p rest.
  unfold discard_policy_update. simpl.
  reflexivity.
Qed.

Lemma policy_check_movetool_unfold :
  forall ps src_sid dst_sid t rest,
    policy_check (MoveTool src_sid dst_sid t :: rest) ps =
    policy_check rest (movetool_policy_update ps src_sid dst_sid t).
Proof.
  intros ps src_sid dst_sid t rest.
  unfold movetool_policy_update. simpl.
  reflexivity.
Qed.

Lemma soundness_general :
  forall acts s ps ps',
    state_matches_policy s ps ->
    policy_check acts ps = Some ps' ->
    all_edible (run s acts) = true.
Proof.
  induction acts as [|a rest IH]; intros s ps ps' Hm Hpc.
  - simpl in Hpc. inversion Hpc; subst.
    eapply matches_implies_edible. exact Hm.
  - apply step_preserves_run_edible.
    destruct a as [sid t|sid p|sid src dst|sid p|src_sid dst_sid t].
    + simpl in Hpc.
      eapply IH.
      * apply policy_wash_step. exact Hm.
      * exact Hpc.
    + simpl in Hpc.
      destruct (lethal_part p) eqn:Hlp.
      * eapply IH.
        -- apply policy_cut_lethal_step. exact Hm. exact Hlp.
        -- exact Hpc.
      * destruct (ps_get_tool ps sid Knife || ps_get_tool ps sid Board ||
                  ps_get_tool ps sid Hands) eqn:Hdirty; [discriminate|].
        destruct (ps_all_toxic_discarded ps) eqn:Htox; [|discriminate].
        apply Bool.orb_false_iff in Hdirty as [Hdirty1 Hdirty2].
        apply Bool.orb_false_iff in Hdirty1 as [Hk Hb].
        eapply IH.
        -- apply policy_cut_safe_step. exact Hm. exact Hlp. exact Hk. exact Hb. exact Hdirty2. exact Htox.
        -- exact Hpc.
    + simpl in Hpc.
      destruct (ps_get_tool ps sid src || ps_get_tool ps sid dst ||
                ps_get_tool ps sid Hands) eqn:Hdirty; [discriminate|].
      destruct (ps_all_toxic_discarded ps) eqn:Htox; [|discriminate].
      apply Bool.orb_false_iff in Hdirty as [Hdirty1 Hdirty2].
      apply Bool.orb_false_iff in Hdirty1 as [Hsrc Hdst].
      eapply IH.
      * apply policy_transfer_step. exact Hm. exact Hsrc. exact Hdst. exact Hdirty2. exact Htox.
      * exact Hpc.
    + rewrite policy_check_discard_unfold in Hpc.
      eapply IH.
      * apply policy_discard_step. exact Hm.
      * exact Hpc.
    + rewrite policy_check_movetool_unfold in Hpc.
      eapply IH.
      * apply policy_movetool_step. exact Hm.
      * exact Hpc.
Qed.

Theorem soundness :
  forall acts ps',
    policy_check acts clean_policy = Some ps' ->
    all_edible (run clean_state acts) = true.
Proof.
  intros acts ps' Hpc.
  eapply soundness_general.
  - apply clean_state_matches_policy.
  - exact Hpc.
Qed.

(******************************************************************************)
(* Completeness: if all_edible then policy accepts                             *)
(******************************************************************************)

Lemma get_set_edible_same :
  forall s sid v, get_edible (set_edible sid v s) sid = v.
Proof.
  intros s sid v. destruct sid; reflexivity.
Qed.

Lemma get_edible_S1 : forall s, get_edible s S1 = dish1_edible s.
Proof. reflexivity. Qed.

Lemma get_edible_S2 : forall s, get_edible s S2 = dish2_edible s.
Proof. reflexivity. Qed.

Lemma cut_safe_contaminates :
  forall s sid p,
    lethal_part p = false ->
    (knife_dirty (get_station s sid) = true \/
     board_dirty (get_station s sid) = true \/
     hands_dirty (get_station s sid) = true) ->
    get_edible (step s (Cut sid p)) sid = false.
Proof.
  intros s sid p Hlp Hdirty.
  unfold step.
  rewrite Hlp.
  destruct Hdirty as [Hk | [Hb | Hh]].
  - rewrite Hk. simpl.
    rewrite get_set_edible_same. reflexivity.
  - destruct (knife_dirty (get_station s sid)) eqn:Ek; simpl.
    + rewrite get_set_edible_same. reflexivity.
    + rewrite Hb. simpl.
      rewrite get_set_edible_same. reflexivity.
  - destruct (knife_dirty (get_station s sid)) eqn:Ek; simpl.
    + rewrite get_set_edible_same. reflexivity.
    + destruct (board_dirty (get_station s sid)) eqn:Eb; simpl.
      * rewrite get_set_edible_same. reflexivity.
      * rewrite Hh. simpl.
        rewrite get_set_edible_same. reflexivity.
Qed.

Lemma cut_safe_before_discard_contaminates :
  forall s sid p,
    lethal_part p = false ->
    knife_dirty (get_station s sid) = false ->
    board_dirty (get_station s sid) = false ->
    hands_dirty (get_station s sid) = false ->
    all_toxic_discarded s = false ->
    get_edible (step s (Cut sid p)) sid = false.
Proof.
  intros s sid p Hlp Hk Hb Hh Htox.
  unfold step. rewrite Hlp, Hk, Hb, Hh. simpl.
  rewrite Htox.
  rewrite get_set_edible_same. reflexivity.
Qed.

Lemma transfer_dirty_contaminates :
  forall s sid src dst,
    (dirty_of_local (get_station s sid) src = true \/
     dirty_of_local (get_station s sid) dst = true \/
     hands_dirty (get_station s sid) = true) ->
    get_edible (step s (Transfer sid src dst)) sid = false.
Proof.
  intros s sid src dst Hdirty.
  unfold step.
  destruct Hdirty as [Hs | [Hd | Hh]].
  - rewrite Hs. simpl.
    rewrite get_set_edible_same. reflexivity.
  - destruct (dirty_of_local (get_station s sid) src) eqn:Es; simpl.
    + rewrite get_set_edible_same. reflexivity.
    + rewrite Hd. simpl.
      rewrite get_set_edible_same. reflexivity.
  - destruct (dirty_of_local (get_station s sid) src) eqn:Es; simpl.
    + rewrite get_set_edible_same. reflexivity.
    + destruct (dirty_of_local (get_station s sid) dst) eqn:Ed; simpl.
      * rewrite get_set_edible_same. reflexivity.
      * rewrite Hh. simpl.
        rewrite get_set_edible_same. reflexivity.
Qed.

Lemma transfer_before_discard_contaminates :
  forall s sid src dst,
    dirty_of_local (get_station s sid) src = false ->
    dirty_of_local (get_station s sid) dst = false ->
    hands_dirty (get_station s sid) = false ->
    all_toxic_discarded s = false ->
    get_edible (step s (Transfer sid src dst)) sid = false.
Proof.
  intros s sid src dst Hs Hd Hh Htox.
  unfold step. rewrite Hs, Hd, Hh. simpl.
  rewrite Htox.
  rewrite get_set_edible_same. reflexivity.
Qed.

Lemma state_policy_tools_agree :
  forall s ps sid t,
    state_matches_policy s ps ->
    dirty_of_local (get_station s sid) t = ps_get_tool ps sid t.
Proof.
  exact matches_tools_eq.
Qed.

Lemma knife_dirty_agree :
  forall s ps sid,
    state_matches_policy s ps ->
    knife_dirty (get_station s sid) = ps_get_tool ps sid Knife.
Proof.
  intros s ps sid Hm.
  change (dirty_of_local (get_station s sid) Knife = ps_get_tool ps sid Knife).
  apply state_policy_tools_agree. exact Hm.
Qed.

Lemma board_dirty_agree :
  forall s ps sid,
    state_matches_policy s ps ->
    board_dirty (get_station s sid) = ps_get_tool ps sid Board.
Proof.
  intros s ps sid Hm.
  change (dirty_of_local (get_station s sid) Board = ps_get_tool ps sid Board).
  apply state_policy_tools_agree. exact Hm.
Qed.

Lemma hands_dirty_agree :
  forall s ps sid,
    state_matches_policy s ps ->
    hands_dirty (get_station s sid) = ps_get_tool ps sid Hands.
Proof.
  intros s ps sid Hm.
  change (dirty_of_local (get_station s sid) Hands = ps_get_tool ps sid Hands).
  apply state_policy_tools_agree. exact Hm.
Qed.

Lemma dirty_of_local_agree :
  forall s ps sid t,
    state_matches_policy s ps ->
    dirty_of_local (get_station s sid) t = ps_get_tool ps sid t.
Proof.
  intros s ps sid t Hm.
  apply state_policy_tools_agree. exact Hm.
Qed.

Lemma state_policy_toxic_agree :
  forall s ps,
    state_matches_policy s ps ->
    all_toxic_discarded s = ps_all_toxic_discarded ps.
Proof.
  exact matches_toxic_eq.
Qed.

Lemma completeness_general :
  forall acts s ps,
    state_matches_policy s ps ->
    policy_check acts ps = None ->
    all_edible (run s acts) = false.
Proof.
  induction acts as [|a rest IH]; intros s ps Hm Hpc.
  - simpl in Hpc. discriminate.
  - simpl.
    destruct a as [sid t|sid p|sid src dst|sid p|src_sid dst_sid t].
    + simpl in Hpc.
      apply IH with (ps := ps_set_tool sid t false ps).
      * apply policy_wash_step. exact Hm.
      * exact Hpc.
    + simpl in Hpc.
      destruct (lethal_part p) eqn:Hlp.
      * apply IH with (ps := ps_set_tool sid Plate true
                              (ps_set_tool sid Hands true
                                (ps_set_tool sid Board true
                                  (ps_set_tool sid Knife true ps)))).
        -- apply policy_cut_lethal_step. exact Hm. exact Hlp.
        -- exact Hpc.
      * destruct (ps_get_tool ps sid Knife || ps_get_tool ps sid Board ||
                  ps_get_tool ps sid Hands) eqn:Hdirty.
        -- apply run_all_edible_false.
           unfold all_edible.
           apply Bool.andb_false_iff.
           apply Bool.orb_true_iff in Hdirty.
           destruct Hdirty as [Hdirty1 | Hh].
           ++ apply Bool.orb_true_iff in Hdirty1.
              destruct Hdirty1 as [Hk | Hb].
              ** destruct sid.
                 --- left. rewrite <- get_edible_S1. apply cut_safe_contaminates.
                     +++ exact Hlp.
                     +++ left.
                         assert (Heq: knife_dirty (get_station s S1) = ps_get_tool ps S1 Knife)
                           by (apply knife_dirty_agree; exact Hm).
                         rewrite Heq. exact Hk.
                 --- right. rewrite <- get_edible_S2. apply cut_safe_contaminates.
                     +++ exact Hlp.
                     +++ left.
                         assert (Heq: knife_dirty (get_station s S2) = ps_get_tool ps S2 Knife)
                           by (apply knife_dirty_agree; exact Hm).
                         rewrite Heq. exact Hk.
              ** destruct sid.
                 --- left. rewrite <- get_edible_S1. apply cut_safe_contaminates.
                     +++ exact Hlp.
                     +++ right. left.
                         assert (Heq: board_dirty (get_station s S1) = ps_get_tool ps S1 Board)
                           by (apply board_dirty_agree; exact Hm).
                         rewrite Heq. exact Hb.
                 --- right. rewrite <- get_edible_S2. apply cut_safe_contaminates.
                     +++ exact Hlp.
                     +++ right. left.
                         assert (Heq: board_dirty (get_station s S2) = ps_get_tool ps S2 Board)
                           by (apply board_dirty_agree; exact Hm).
                         rewrite Heq. exact Hb.
           ++ destruct sid.
              ** left. rewrite <- get_edible_S1. apply cut_safe_contaminates.
                 --- exact Hlp.
                 --- right. right.
                     assert (Heq: hands_dirty (get_station s S1) = ps_get_tool ps S1 Hands)
                       by (apply hands_dirty_agree; exact Hm).
                     rewrite Heq. exact Hh.
              ** right. rewrite <- get_edible_S2. apply cut_safe_contaminates.
                 --- exact Hlp.
                 --- right. right.
                     assert (Heq: hands_dirty (get_station s S2) = ps_get_tool ps S2 Hands)
                       by (apply hands_dirty_agree; exact Hm).
                     rewrite Heq. exact Hh.
        -- destruct (ps_all_toxic_discarded ps) eqn:Htox.
           ++ apply IH with (ps := ps).
              ** apply Bool.orb_false_iff in Hdirty as [Hdirty1 Hdirty2].
                 apply Bool.orb_false_iff in Hdirty1 as [Hk Hb].
                 apply policy_cut_safe_step. exact Hm. exact Hlp. exact Hk. exact Hb. exact Hdirty2. exact Htox.
              ** exact Hpc.
           ++ apply run_all_edible_false.
              unfold all_edible.
              apply Bool.andb_false_iff.
              apply Bool.orb_false_iff in Hdirty as [Hdirty1 Hdirty2].
              apply Bool.orb_false_iff in Hdirty1 as [Hk Hb].
              destruct sid.
              ** left. rewrite <- get_edible_S1. apply cut_safe_before_discard_contaminates.
                 --- exact Hlp.
                 --- assert (Heq: knife_dirty (get_station s S1) = ps_get_tool ps S1 Knife)
                       by (apply knife_dirty_agree; exact Hm).
                     rewrite Heq. exact Hk.
                 --- assert (Heq: board_dirty (get_station s S1) = ps_get_tool ps S1 Board)
                       by (apply board_dirty_agree; exact Hm).
                     rewrite Heq. exact Hb.
                 --- assert (Heq: hands_dirty (get_station s S1) = ps_get_tool ps S1 Hands)
                       by (apply hands_dirty_agree; exact Hm).
                     rewrite Heq. exact Hdirty2.
                 --- assert (Heq: all_toxic_discarded s = ps_all_toxic_discarded ps)
                       by (apply state_policy_toxic_agree; exact Hm).
                     rewrite Heq. exact Htox.
              ** right. rewrite <- get_edible_S2. apply cut_safe_before_discard_contaminates.
                 --- exact Hlp.
                 --- assert (Heq: knife_dirty (get_station s S2) = ps_get_tool ps S2 Knife)
                       by (apply knife_dirty_agree; exact Hm).
                     rewrite Heq. exact Hk.
                 --- assert (Heq: board_dirty (get_station s S2) = ps_get_tool ps S2 Board)
                       by (apply board_dirty_agree; exact Hm).
                     rewrite Heq. exact Hb.
                 --- assert (Heq: hands_dirty (get_station s S2) = ps_get_tool ps S2 Hands)
                       by (apply hands_dirty_agree; exact Hm).
                     rewrite Heq. exact Hdirty2.
                 --- assert (Heq: all_toxic_discarded s = ps_all_toxic_discarded ps)
                       by (apply state_policy_toxic_agree; exact Hm).
                     rewrite Heq. exact Htox.
    + simpl in Hpc.
      destruct (ps_get_tool ps sid src || ps_get_tool ps sid dst ||
                ps_get_tool ps sid Hands) eqn:Hdirty.
      * apply run_all_edible_false.
        unfold all_edible.
        apply Bool.andb_false_iff.
        apply Bool.orb_true_iff in Hdirty.
        destruct Hdirty as [Hdirty1 | Hh].
        -- apply Bool.orb_true_iff in Hdirty1.
           destruct Hdirty1 as [Hs | Hd].
           ++ destruct sid.
              ** left. rewrite <- get_edible_S1. apply transfer_dirty_contaminates.
                 left. assert (Heq: dirty_of_local (get_station s S1) src = ps_get_tool ps S1 src)
                   by (apply dirty_of_local_agree; exact Hm).
                 rewrite Heq. exact Hs.
              ** right. rewrite <- get_edible_S2. apply transfer_dirty_contaminates.
                 left. assert (Heq: dirty_of_local (get_station s S2) src = ps_get_tool ps S2 src)
                   by (apply dirty_of_local_agree; exact Hm).
                 rewrite Heq. exact Hs.
           ++ destruct sid.
              ** left. rewrite <- get_edible_S1. apply transfer_dirty_contaminates.
                 right. left. assert (Heq: dirty_of_local (get_station s S1) dst = ps_get_tool ps S1 dst)
                   by (apply dirty_of_local_agree; exact Hm).
                 rewrite Heq. exact Hd.
              ** right. rewrite <- get_edible_S2. apply transfer_dirty_contaminates.
                 right. left. assert (Heq: dirty_of_local (get_station s S2) dst = ps_get_tool ps S2 dst)
                   by (apply dirty_of_local_agree; exact Hm).
                 rewrite Heq. exact Hd.
        -- destruct sid.
           ++ left. rewrite <- get_edible_S1. apply transfer_dirty_contaminates.
              right. right. assert (Heq: hands_dirty (get_station s S1) = ps_get_tool ps S1 Hands)
                by (apply hands_dirty_agree; exact Hm).
              rewrite Heq. exact Hh.
           ++ right. rewrite <- get_edible_S2. apply transfer_dirty_contaminates.
              right. right. assert (Heq: hands_dirty (get_station s S2) = ps_get_tool ps S2 Hands)
                by (apply hands_dirty_agree; exact Hm).
              rewrite Heq. exact Hh.
      * destruct (ps_all_toxic_discarded ps) eqn:Htox.
        -- apply Bool.orb_false_iff in Hdirty as [Hdirty1 Hdirty2].
           apply Bool.orb_false_iff in Hdirty1 as [Hsrc Hdst].
           apply IH with (ps := ps).
           ++ apply policy_transfer_step. exact Hm. exact Hsrc. exact Hdst. exact Hdirty2. exact Htox.
           ++ exact Hpc.
        -- apply run_all_edible_false.
           unfold all_edible.
           apply Bool.andb_false_iff.
           apply Bool.orb_false_iff in Hdirty as [Hdirty1 Hdirty2].
           apply Bool.orb_false_iff in Hdirty1 as [Hsrc Hdst].
           destruct sid.
           ++ left. rewrite <- get_edible_S1. apply transfer_before_discard_contaminates.
              ** assert (Heq: dirty_of_local (get_station s S1) src = ps_get_tool ps S1 src)
                   by (apply dirty_of_local_agree; exact Hm).
                 rewrite Heq. exact Hsrc.
              ** assert (Heq: dirty_of_local (get_station s S1) dst = ps_get_tool ps S1 dst)
                   by (apply dirty_of_local_agree; exact Hm).
                 rewrite Heq. exact Hdst.
              ** assert (Heq: hands_dirty (get_station s S1) = ps_get_tool ps S1 Hands)
                   by (apply hands_dirty_agree; exact Hm).
                 rewrite Heq. exact Hdirty2.
              ** assert (Heq: all_toxic_discarded s = ps_all_toxic_discarded ps)
                   by (apply state_policy_toxic_agree; exact Hm).
                 rewrite Heq. exact Htox.
           ++ right. rewrite <- get_edible_S2. apply transfer_before_discard_contaminates.
              ** assert (Heq: dirty_of_local (get_station s S2) src = ps_get_tool ps S2 src)
                   by (apply dirty_of_local_agree; exact Hm).
                 rewrite Heq. exact Hsrc.
              ** assert (Heq: dirty_of_local (get_station s S2) dst = ps_get_tool ps S2 dst)
                   by (apply dirty_of_local_agree; exact Hm).
                 rewrite Heq. exact Hdst.
              ** assert (Heq: hands_dirty (get_station s S2) = ps_get_tool ps S2 Hands)
                   by (apply hands_dirty_agree; exact Hm).
                 rewrite Heq. exact Hdirty2.
              ** assert (Heq: all_toxic_discarded s = ps_all_toxic_discarded ps)
                   by (apply state_policy_toxic_agree; exact Hm).
                 rewrite Heq. exact Htox.
    + rewrite policy_check_discard_unfold in Hpc.
      apply IH with (ps := discard_policy_update ps sid p).
      * apply policy_discard_step. exact Hm.
      * exact Hpc.
    + rewrite policy_check_movetool_unfold in Hpc.
      apply IH with (ps := movetool_policy_update ps src_sid dst_sid t).
      * apply policy_movetool_step. exact Hm.
      * exact Hpc.
Qed.

Theorem completeness :
  forall acts,
    all_edible (run clean_state acts) = true ->
    exists ps', policy_check acts clean_policy = Some ps'.
Proof.
  intros acts Hed.
  destruct (policy_check acts clean_policy) as [ps'|] eqn:Hpc.
  - exists ps'. reflexivity.
  - exfalso.
    assert (Hfalse : all_edible (run clean_state acts) = false).
    { eapply completeness_general.
      - apply clean_state_matches_policy.
      - exact Hpc. }
    rewrite Hed in Hfalse. discriminate.
Qed.

Theorem policy_iff_edible :
  forall acts,
    (exists ps', policy_check acts clean_policy = Some ps') <->
    all_edible (run clean_state acts) = true.
Proof.
  intros acts. split.
  - intros [ps' Hpc]. eapply soundness. exact Hpc.
  - apply completeness.
Qed.

End WithSkinToxicity.

(******************************************************************************)
(* Examples                                                                   *)
(******************************************************************************)

Example single_station_hygienic_skin_safe :
  hygienic false [Cut S1 Liver; Discard S1 Liver;
                  Cut S1 Ovaries; Discard S1 Ovaries;
                  Cut S1 Intestines; Discard S1 Intestines;
                  Wash S1 Knife; Wash S1 Board; Wash S1 Plate; Wash S1 Hands;
                  Cut S1 Flesh; Transfer S1 Board Plate].
Proof.
  unfold hygienic.
  simpl.
  eexists; reflexivity.
Qed.

Example single_station_hygienic_skin_toxic :
  hygienic true [Cut S1 Liver; Discard S1 Liver;
                 Cut S1 Ovaries; Discard S1 Ovaries;
                 Cut S1 Intestines; Discard S1 Intestines;
                 Cut S1 Skin; Discard S1 Skin;
                 Wash S1 Knife; Wash S1 Board; Wash S1 Plate; Wash S1 Hands;
                 Cut S1 Flesh; Transfer S1 Board Plate].
Proof.
  unfold hygienic.
  simpl.
  eexists; reflexivity.
Qed.

Example cross_station_contamination_rejected :
  forall sil, ~hygienic sil [Cut S1 Liver; MoveTool S1 S2 Knife; Cut S2 Flesh].
Proof.
  intros sil.
  unfold hygienic.
  simpl.
  intros [ps H].
  destruct sil; simpl in H; discriminate.
Qed.

Example temporal_ordering_violated :
  forall sil, ~hygienic sil [Cut S1 Liver; Wash S1 Knife; Wash S1 Board; Wash S1 Hands; Cut S1 Flesh].
Proof.
  intros sil.
  unfold hygienic.
  simpl.
  intros [ps H].
  destruct sil; simpl in H; discriminate.
Qed.

Example parallel_stations_hygienic :
  hygienic false [Cut S1 Liver; Discard S1 Liver;
                  Cut S1 Ovaries; Discard S1 Ovaries;
                  Cut S1 Intestines; Discard S1 Intestines;
                  Wash S1 Knife; Wash S1 Board; Wash S1 Plate; Wash S1 Hands;
                  Wash S2 Knife; Wash S2 Board; Wash S2 Plate; Wash S2 Hands;
                  Cut S1 Flesh; Transfer S1 Board Plate;
                  Cut S2 Flesh; Transfer S2 Board Plate].
Proof.
  unfold hygienic.
  simpl.
  eexists; reflexivity.
Qed.

Example batch_contamination_via_tool_sharing :
  forall sil,
    ~hygienic sil [Cut S1 Liver; Discard S1 Liver;
                   Cut S1 Ovaries; Discard S1 Ovaries;
                   Cut S1 Intestines; Discard S1 Intestines;
                   MoveTool S1 S2 Knife;
                   Wash S1 Knife; Wash S1 Board; Wash S1 Hands;
                   Cut S1 Flesh;
                   Cut S2 Flesh].
Proof.
  intros sil.
  unfold hygienic.
  simpl.
  intros [ps H].
  destruct sil; simpl in H; discriminate.
Qed.
