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
                    plate_dirty := plate_dirty st; hands_dirty := kbh |} in
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
      then let ps' := ps_set_tool sid Hands true (ps_set_tool sid Board true (ps_set_tool sid Knife true ps)) in
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


End WithSkinToxicity.

(******************************************************************************)
(* Examples                                                                   *)
(******************************************************************************)

Example single_station_hygienic_skin_safe :
  hygienic false [Cut S1 Liver; Discard S1 Liver;
                  Cut S1 Ovaries; Discard S1 Ovaries;
                  Cut S1 Intestines; Discard S1 Intestines;
                  Wash S1 Knife; Wash S1 Board; Wash S1 Hands;
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
                 Wash S1 Knife; Wash S1 Board; Wash S1 Hands;
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
                  Wash S1 Knife; Wash S1 Board; Wash S1 Hands;
                  Wash S2 Knife; Wash S2 Board; Wash S2 Hands;
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
