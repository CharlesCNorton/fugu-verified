(******************************************************************************)
(*                                                                            *)
(*               Fugu-Safety-Verified: Cross-Contamination Logic              *)
(*                                                                            *)
(*     Models toxin contamination across fugu parts (flesh/skin vs.           *)
(*     liver/ovaries/intestines) and kitchen tools (knife/board/plate/trash). *)
(*                                                                            *)
(*     Operational model (high level):                                        *)
(*       - Cutting a toxic part contaminates knife and board.                 *)
(*       - Any cut of a non-lethal part using a contaminated knife or board   *)
(*         renders the meal unsafe (edible := false).                         *)
(*       - Any food transfer involving a contaminated endpoint renders the    *)
(*         meal unsafe (edible := false).                                     *)
(*       - Discarding to Trash does not affect edibility, but may contaminate *)
(*         the trash receptacle.                                              *)
(*                                                                            *)
(*     A policy checker accepts exactly the hygienic action sequences:        *)
(*       policy_state acts clean = Some _   <->   edible (run clean acts)=true *)
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

(** Parts and tools *)
Inductive Part := Flesh | Skin | Liver | Ovaries | Intestines.
Inductive Tool := Knife | Board | Plate | Trash | Hands.

Section WithSkinToxicity.

Variable skin_is_lethal : bool.

Definition lethal_part (p : Part) : bool :=
  match p with
  | Flesh => false
  | Skin => skin_is_lethal
  | _ => true
  end.

(** Kitchen state
    - *_dirty tracks toxin contamination of tools.
    - edible tracks whether the meal-to-be-eaten has remained safe. *)
Record State := {
  knife_dirty : bool;
  board_dirty : bool;
  plate_dirty : bool;
  trash_dirty : bool;
  hands_dirty : bool;
  edible : bool
}.

Definition mk_state (kd bd pd td hd ed : bool) : State :=
  {| knife_dirty := kd;
     board_dirty := bd;
     plate_dirty := pd;
     trash_dirty := td;
     hands_dirty := hd;
     edible := ed |}.

Definition clean_state : State := mk_state false false false false false true.

Definition dirty_of (s : State) (t : Tool) : bool :=
  match t with
  | Knife => knife_dirty s
  | Board => board_dirty s
  | Plate => plate_dirty s
  | Trash => trash_dirty s
  | Hands => hands_dirty s
  end.

Definition set_tool (t : Tool) (v : bool) (s : State) : State :=
  match t with
  | Knife => mk_state v (board_dirty s) (plate_dirty s) (trash_dirty s) (hands_dirty s) (edible s)
  | Board => mk_state (knife_dirty s) v (plate_dirty s) (trash_dirty s) (hands_dirty s) (edible s)
  | Plate => mk_state (knife_dirty s) (board_dirty s) v (trash_dirty s) (hands_dirty s) (edible s)
  | Trash => mk_state (knife_dirty s) (board_dirty s) (plate_dirty s) v (hands_dirty s) (edible s)
  | Hands => mk_state (knife_dirty s) (board_dirty s) (plate_dirty s) (trash_dirty s) v (edible s)
  end.

(** Actions *)
Inductive Action :=
| Wash (t : Tool)
| Cut (p : Part)
| Transfer (src dst : Tool)   (* food transfer: kept for consumption *)
| Discard (src : Tool).       (* discard to Trash: not consumed *)

(** One transition step *)
Definition step (s : State) (a : Action) : State :=
  match a with
  | Wash t =>
      set_tool t false s

  | Cut p =>
      let lp := lethal_part p in
      let any_dirty := knife_dirty s || board_dirty s || hands_dirty s in
      let kbh := any_dirty || lp in
      let ed :=
        if lp then edible s
        else if any_dirty then false else edible s in
      mk_state kbh kbh (plate_dirty s) (trash_dirty s) kbh ed

  | Transfer src dst =>
      let d := dirty_of s src || dirty_of s dst || hands_dirty s in
      let ed := if d then false else edible s in
      let s' := set_tool dst d (set_tool src d s) in
      mk_state (knife_dirty s') (board_dirty s') (plate_dirty s') (trash_dirty s') d ed

  | Discard src =>
      let hd := hands_dirty s || dirty_of s src in
      let td := trash_dirty s || hd in
      mk_state (knife_dirty s) (board_dirty s) (plate_dirty s) td hd (edible s)
  end.

Fixpoint run (s : State) (as_ : list Action) : State :=
  match as_ with
  | [] => s
  | a :: rest => run (step s a) rest
  end.

(******************************************************************************)
(* Helper equalities                                                          *)
(******************************************************************************)

Lemma step_cut_safe_clean :
  forall s p,
    lethal_part p = false ->
    knife_dirty s = false ->
    board_dirty s = false ->
    hands_dirty s = false ->
    step s (Cut p) = s.
Proof.
  intros s p Hp Hk Hb Hh.
  destruct s as [k b pd td hd ed]; simpl in *.
  unfold step; simpl.
  rewrite Hp, Hk, Hb, Hh.
  simpl.
  reflexivity.
Qed.

Lemma step_transfer_clean :
  forall s src dst,
    dirty_of s src = false ->
    dirty_of s dst = false ->
    hands_dirty s = false ->
    step s (Transfer src dst) = s.
Proof.
  intros s src dst Hsrc Hdst Hh.
  destruct s as [k b p t h ed]; simpl in *.
  destruct src; destruct dst; simpl in *;
    rewrite ?Hsrc, ?Hdst, ?Hh; simpl; reflexivity.
Qed.

(******************************************************************************)
(* Basic invariants                                                           *)
(******************************************************************************)

Lemma step_edible_false :
  forall s a, edible s = false -> edible (step s a) = false.
Proof.
  intros s a Hed.
  destruct a as [t|p|src dst|src]; simpl.
  - destruct t; simpl; rewrite Hed; reflexivity.
  - destruct (lethal_part p) eqn:Hp; simpl.
    + exact Hed.
    + destruct (knife_dirty s || board_dirty s || hands_dirty s) eqn:Hkbh; simpl; try reflexivity.
      exact Hed.
  - destruct (dirty_of s src || dirty_of s dst || hands_dirty s) eqn:Hd; simpl; try reflexivity.
    exact Hed.
  - simpl. exact Hed.
Qed.

Lemma run_edible_false :
  forall s acts, edible s = false -> edible (run s acts) = false.
Proof.
  intros s acts; revert s.
  induction acts as [|a rest IH]; intros s Hed; simpl.
  - exact Hed.
  - apply IH. apply step_edible_false. exact Hed.
Qed.

(******************************************************************************)
(* Key contamination lemmas                                                   *)
(******************************************************************************)

Lemma safe_cut_when_dirty_lethal :
  forall s p,
    lethal_part p = false ->
    (knife_dirty s = true \/ board_dirty s = true \/ hands_dirty s = true) ->
    edible (step s (Cut p)) = false.
Proof.
  intros s p Hp Hd.
  unfold step; simpl.
  rewrite Hp; simpl.
  destruct (knife_dirty s || board_dirty s || hands_dirty s) eqn:Hkbh.
  - reflexivity.
  - apply Bool.orb_false_iff in Hkbh as [Hkb Hh].
    apply Bool.orb_false_iff in Hkb as [Hk Hb].
    destruct Hd as [Hk' | [Hb' | Hh']].
    + rewrite Hk in Hk'. discriminate.
    + rewrite Hb in Hb'. discriminate.
    + rewrite Hh in Hh'. discriminate.
Qed.

Lemma transfer_with_dirty_lethal :
  forall s src dst,
    (dirty_of s src = true \/ dirty_of s dst = true \/ hands_dirty s = true) ->
    edible (step s (Transfer src dst)) = false.
Proof.
  intros s src dst Hd.
  unfold step; simpl.
  destruct (dirty_of s src || dirty_of s dst || hands_dirty s) eqn:Horb.
  - reflexivity.
  - apply Bool.orb_false_iff in Horb as [Hsd Hh].
    apply Bool.orb_false_iff in Hsd as [Hsrc Hdst].
    destruct Hd as [Hsrc' | [Hdst' | Hh']].
    + rewrite Hsrc in Hsrc'. discriminate.
    + rewrite Hdst in Hdst'. discriminate.
    + rewrite Hh in Hh'. discriminate.
Qed.

Theorem dirty_safe_cut_trace_lethal :
  forall s p actions,
    lethal_part p = false ->
    (knife_dirty s = true \/ board_dirty s = true \/ hands_dirty s = true) ->
    edible (run s (Cut p :: actions)) = false.
Proof.
  intros s p actions Hp Hd.
  simpl.
  apply run_edible_false.
  apply safe_cut_when_dirty_lethal; assumption.
Qed.

Theorem dirty_transfer_trace_lethal :
  forall s src dst actions,
    (dirty_of s src = true \/ dirty_of s dst = true \/ hands_dirty s = true) ->
    edible (run s (Transfer src dst :: actions)) = false.
Proof.
  intros s src dst actions Hd.
  simpl.
  apply run_edible_false.
  apply transfer_with_dirty_lethal; exact Hd.
Qed.

(******************************************************************************)
(* Policy checker                                                             *)
(******************************************************************************)

Definition matches (s : State) (kd bd pd td hd : bool) : Prop :=
  knife_dirty s = kd /\
  board_dirty s = bd /\
  plate_dirty s = pd /\
  trash_dirty s = td /\
  hands_dirty s = hd /\
  edible s = true.

(** Policy checker returns final cleanliness if hygienic; rejects otherwise. *)
Fixpoint policy_state (acts : list Action) (kd bd pd td hd : bool)
  : option (bool * bool * bool * bool * bool) :=
  match acts with
  | [] => Some (kd, bd, pd, td, hd)

  | Wash Knife :: rest => policy_state rest false bd pd td hd
  | Wash Board :: rest => policy_state rest kd false pd td hd
  | Wash Plate :: rest => policy_state rest kd bd false td hd
  | Wash Trash :: rest => policy_state rest kd bd pd false hd
  | Wash Hands :: rest => policy_state rest kd bd pd td false

  | Cut p :: rest =>
      if lethal_part p
      then policy_state rest true true pd td true
      else if kd || bd || hd then None
           else policy_state rest kd bd pd td hd

  | Transfer src dst :: rest =>
      let dsrc :=
        match src with Knife => kd | Board => bd | Plate => pd | Trash => td | Hands => hd end in
      let ddst :=
        match dst with Knife => kd | Board => bd | Plate => pd | Trash => td | Hands => hd end in
      if dsrc || ddst || hd then None else policy_state rest kd bd pd td hd

  | Discard src :: rest =>
      let dsrc :=
        match src with Knife => kd | Board => bd | Plate => pd | Trash => td | Hands => hd end in
      let hd' := hd || dsrc in
      policy_state rest kd bd pd (td || hd') hd'
  end.

(******************************************************************************)
(* Policy soundness: accepted traces preserve edibility                        *)
(******************************************************************************)

Lemma policy_run_sound :
  forall acts s kd bd pd td hd kd' bd' pd' td' hd',
    matches s kd bd pd td hd ->
    policy_state acts kd bd pd td hd = Some (kd', bd', pd', td', hd') ->
    matches (run s acts) kd' bd' pd' td' hd'.
Proof.
  induction acts as [|a rest IH]; simpl;
    intros s kd bd pd td hd kd' bd' pd' td' hd' Hm Hpol.
  - inversion Hpol; subst; exact Hm.
  - destruct a as [t|p|src dst|src]; simpl in Hpol.

    + destruct t; simpl in Hpol.
      * eapply IH; try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht [Hh He]]]]]; repeat split; simpl; auto.
      * eapply IH; try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht [Hh He]]]]]; repeat split; simpl; auto.
      * eapply IH; try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht [Hh He]]]]]; repeat split; simpl; auto.
      * eapply IH; try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht [Hh He]]]]]; repeat split; simpl; auto.
      * eapply IH; try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht [Hh He]]]]]; repeat split; simpl; auto.

    + destruct (lethal_part p) eqn:Hp; simpl in Hpol.
      * eapply IH; try exact Hpol.
        destruct Hm as [_ [_ [Hp0 [Ht [_ He]]]]].
        unfold step; simpl; rewrite Hp.
        repeat split; simpl.
        -- rewrite Bool.orb_true_r. reflexivity.
        -- rewrite Bool.orb_true_r. reflexivity.
        -- exact Hp0.
        -- exact Ht.
        -- rewrite Bool.orb_true_r. reflexivity.
        -- exact He.
      * destruct (kd || bd || hd) eqn:Hdirty; try discriminate.
        apply Bool.orb_false_iff in Hdirty as [Hkb Hhd].
        apply Bool.orb_false_iff in Hkb as [Hkd Hbd].
        destruct Hm as [Hk [Hb [Hp0 [Ht [Hh He]]]]].
        assert (knife_dirty s = false) as Hk0 by (rewrite Hk; exact Hkd).
        assert (board_dirty s = false) as Hb0 by (rewrite Hb; exact Hbd).
        assert (hands_dirty s = false) as Hh0 by (rewrite Hh; exact Hhd).
        assert (step s (Cut p) = s) as Hstep by (apply step_cut_safe_clean; auto).
        rewrite Hstep.
        eapply IH; try exact Hpol.
        repeat split; assumption.

    + remember (match src with Knife => kd | Board => bd | Plate => pd | Trash => td | Hands => hd end) as dsrc.
      remember (match dst with Knife => kd | Board => bd | Plate => pd | Trash => td | Hands => hd end) as ddst.
      destruct (dsrc || ddst || hd) eqn:Hdirty; try discriminate.
      apply Bool.orb_false_iff in Hdirty as [Hsd Hhd].
      apply Bool.orb_false_iff in Hsd as [Hdsrc Hddst].
      destruct Hm as [Hk [Hb [Hp0 [Ht [Hh He]]]]].
      assert (dirty_of s src = false) as Hsrc_clean.
      { destruct src; simpl in *; subst dsrc; rewrite ?Hk, ?Hb, ?Hp0, ?Ht, ?Hh; assumption. }
      assert (dirty_of s dst = false) as Hdst_clean.
      { destruct dst; simpl in *; subst ddst; rewrite ?Hk, ?Hb, ?Hp0, ?Ht, ?Hh; assumption. }
      assert (hands_dirty s = false) as Hh0 by (rewrite Hh; exact Hhd).
      assert (step s (Transfer src dst) = s) as Hstep by (apply step_transfer_clean; assumption).
      rewrite Hstep.
      eapply IH; try exact Hpol.
      repeat split; assumption.

    + remember (match src with Knife => kd | Board => bd | Plate => pd | Trash => td | Hands => hd end) as dsrc.
      remember (hd || dsrc) as hdnew.
      eapply IH; try exact Hpol.
      destruct Hm as [Hk [Hb [Hp0 [Ht [Hh He]]]]].
      repeat split; simpl; unfold step; simpl.
      * exact Hk.
      * exact Hb.
      * exact Hp0.
      * subst dsrc hdnew.
        destruct src; simpl in *; rewrite ?Hk, ?Hb, ?Hp0, ?Ht, ?Hh; reflexivity.
      * subst dsrc hdnew.
        destruct src; simpl in *; rewrite ?Hk, ?Hb, ?Hp0, ?Ht, ?Hh; reflexivity.
      * exact He.
Qed.

Theorem policy_sound :
  forall acts kd bd pd td hd,
    policy_state acts false false false false false = Some (kd, bd, pd, td, hd) ->
    edible (run clean_state acts) = true.
Proof.
  intros acts kd bd pd td hd Hpol.
  assert (matches clean_state false false false false false) as Hclean by (repeat split; reflexivity).
  pose proof (@policy_run_sound acts clean_state false false false false false kd bd pd td hd Hclean Hpol) as Hm.
  destruct Hm as [_ [_ [_ [_ [_ Hed]]]]]; exact Hed.
Qed.

(******************************************************************************)
(* Policy completeness: if execution stays edible, the policy must accept      *)
(******************************************************************************)

Lemma policy_run_complete :
  forall acts s kd bd pd td hd,
    matches s kd bd pd td hd ->
    policy_state acts kd bd pd td hd = None ->
    edible (run s acts) = false.
Proof.
  induction acts as [|a rest IH]; intros s kd bd pd td hd Hm Hpol; simpl in Hpol.
  - discriminate.
  - destruct a as [t|p|src dst|src].

    + destruct t; simpl in Hpol.
      * eapply IH; try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht [Hh He]]]]]; repeat split; simpl; auto.
      * eapply IH; try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht [Hh He]]]]]; repeat split; simpl; auto.
      * eapply IH; try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht [Hh He]]]]]; repeat split; simpl; auto.
      * eapply IH; try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht [Hh He]]]]]; repeat split; simpl; auto.
      * eapply IH; try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht [Hh He]]]]]; repeat split; simpl; auto.

    + destruct (lethal_part p) eqn:Hp; simpl in Hpol.
      * eapply IH; try exact Hpol.
        destruct Hm as [_ [_ [Hp0 [Ht [_ He]]]]].
        unfold step; simpl; rewrite Hp.
        repeat split; simpl.
        -- rewrite Bool.orb_true_r. reflexivity.
        -- rewrite Bool.orb_true_r. reflexivity.
        -- exact Hp0.
        -- exact Ht.
        -- rewrite Bool.orb_true_r. reflexivity.
        -- exact He.
      * destruct (kd || bd || hd) eqn:Hdirty.
        -- destruct Hm as [Hk [Hb [_ [_ [Hh _]]]]].
           assert (kd = true \/ bd = true \/ hd = true) as Hkbh_or.
           { destruct kd, bd, hd; simpl in Hdirty; try discriminate; auto. }
           assert (knife_dirty s = true \/ board_dirty s = true \/ hands_dirty s = true) as Htools_dirty.
           { destruct Hkbh_or as [Hkd' | [Hbd' | Hhd']].
             - left. rewrite Hk. exact Hkd'.
             - right. left. rewrite Hb. exact Hbd'.
             - right. right. rewrite Hh. exact Hhd'. }
           simpl.
           apply run_edible_false.
           apply safe_cut_when_dirty_lethal; assumption.
        -- apply Bool.orb_false_iff in Hdirty as [Hkb Hhd].
           apply Bool.orb_false_iff in Hkb as [Hkd Hbd].
           destruct Hm as [Hk [Hb [Hp0 [Ht [Hh He]]]]].
           assert (knife_dirty s = false) as Hk0 by (rewrite Hk; exact Hkd).
           assert (board_dirty s = false) as Hb0 by (rewrite Hb; exact Hbd).
           assert (hands_dirty s = false) as Hh0 by (rewrite Hh; exact Hhd).
           assert (step s (Cut p) = s) as Hstep by (apply step_cut_safe_clean; auto).
           change (edible (run (step s (Cut p)) rest) = false).
           rewrite Hstep.
           eapply IH; try exact Hpol.
           repeat split; assumption.

    + remember (match src with Knife => kd | Board => bd | Plate => pd | Trash => td | Hands => hd end) as dsrc.
      remember (match dst with Knife => kd | Board => bd | Plate => pd | Trash => td | Hands => hd end) as ddst.
      destruct (dsrc || ddst || hd) eqn:Hdirty.
      * destruct Hm as [Hk [Hb [Hp0 [Ht [Hh He]]]]].
        assert (dsrc = true \/ ddst = true \/ hd = true) as Hor.
        { destruct dsrc, ddst, hd; simpl in Hdirty; try discriminate; auto. }
        assert (dirty_of s src = true \/ dirty_of s dst = true \/ hands_dirty s = true) as Hdirty_tools.
        { destruct Hor as [Hdsrc | [Hddst | Hhd]].
          - left.
            destruct src; simpl in *; subst dsrc; rewrite ?Hk, ?Hb, ?Hp0, ?Ht, ?Hh; exact Hdsrc.
          - right. left.
            destruct dst; simpl in *; subst ddst; rewrite ?Hk, ?Hb, ?Hp0, ?Ht, ?Hh; exact Hddst.
          - right. right. rewrite Hh. exact Hhd. }
        simpl.
        apply run_edible_false.
        apply transfer_with_dirty_lethal; exact Hdirty_tools.
      * apply Bool.orb_false_iff in Hdirty as [Hsd Hhd].
        apply Bool.orb_false_iff in Hsd as [Hdsrc Hddst].
        destruct Hm as [Hk [Hb [Hp0 [Ht [Hh He]]]]].
        assert (dirty_of s src = false) as Hsrc_clean.
        { destruct src; simpl in *; subst dsrc; rewrite ?Hk, ?Hb, ?Hp0, ?Ht, ?Hh; assumption. }
        assert (dirty_of s dst = false) as Hdst_clean.
        { destruct dst; simpl in *; subst ddst; rewrite ?Hk, ?Hb, ?Hp0, ?Ht, ?Hh; assumption. }
        assert (hands_dirty s = false) as Hh0 by (rewrite Hh; exact Hhd).
        assert (step s (Transfer src dst) = s) as Hstep by (apply step_transfer_clean; assumption).
        change (edible (run (step s (Transfer src dst)) rest) = false).
        rewrite Hstep.
        eapply IH; try exact Hpol.
        repeat split; assumption.

    + remember (match src with Knife => kd | Board => bd | Plate => pd | Trash => td | Hands => hd end) as dsrc.
      remember (hd || dsrc) as hdnew.
      eapply IH; try exact Hpol.
      destruct Hm as [Hk [Hb [Hp0 [Ht [Hh He]]]]].
      repeat split; simpl; unfold step; simpl.
      * exact Hk.
      * exact Hb.
      * exact Hp0.
      * subst dsrc hdnew.
        destruct src; simpl in *; rewrite ?Hk, ?Hb, ?Hp0, ?Ht, ?Hh; reflexivity.
      * subst dsrc hdnew.
        destruct src; simpl in *; rewrite ?Hk, ?Hb, ?Hp0, ?Ht, ?Hh; reflexivity.
      * exact He.
Qed.

Theorem policy_complete :
  forall acts,
    edible (run clean_state acts) = true ->
    exists kd bd pd td hd,
      policy_state acts false false false false false = Some (kd, bd, pd, td, hd).
Proof.
  intros acts Hed.
  destruct (policy_state acts false false false false false) as [[[[[kd bd] pd] td] hd]|] eqn:Hpol.
  - exists kd, bd, pd, td, hd. reflexivity.
  - exfalso.
    assert (matches clean_state false false false false false) as Hm0 by (repeat split; reflexivity).
    pose proof (@policy_run_complete acts clean_state false false false false false Hm0 Hpol) as Hcontra.
    rewrite Hed in Hcontra. discriminate.
Qed.

Definition hygienic (acts : list Action) : Prop :=
  exists kd bd pd td hd,
    policy_state acts false false false false false = Some (kd, bd, pd, td, hd).

Theorem hygienic_iff_edible :
  forall acts,
    hygienic acts <-> edible (run clean_state acts) = true.
Proof.
  intros acts; split.
  - intros [kd [bd [pd [td [hd Hpol]]]]].
    eapply policy_sound; eauto.
  - intros Hed.
    apply policy_complete; exact Hed.
Qed.

(******************************************************************************)
(* Small corollaries / examples                                               *)
(******************************************************************************)

Corollary dirty_safe_cut_immediately_lethal_example :
  forall actions,
    edible (run (mk_state true false false false false true) (Cut Flesh :: actions)) = false.
Proof.
  intros actions.
  eapply dirty_safe_cut_trace_lethal with (p:=Flesh); simpl; auto.
Qed.

Example toxic_trim_discard_wash_serve_is_hygienic :
  hygienic [Cut Liver; Discard Board; Wash Knife; Wash Board; Wash Hands; Cut Flesh; Transfer Board Plate].
Proof.
  unfold hygienic.
  eexists false, false, false, true, false.
  simpl.
  reflexivity.
Qed.

Example toxic_trim_discard_wash_serve_is_edible :
  edible (run clean_state [Cut Liver; Discard Board; Wash Knife; Wash Board; Wash Hands; Cut Flesh; Transfer Board Plate]) = true.
Proof.
  apply hygienic_iff_edible.
  apply toxic_trim_discard_wash_serve_is_hygienic.
Qed.

(** Negative witnesses: unsafe sequences are correctly rejected. *)

Example unsafe_no_wash_not_hygienic :
  ~hygienic [Cut Liver; Cut Flesh].
Proof.
  unfold hygienic.
  intros [kd [bd [pd [td [hd H]]]]].
  simpl in H.
  discriminate.
Qed.

Example unsafe_no_wash_is_lethal :
  edible (run clean_state [Cut Liver; Cut Flesh]) = false.
Proof.
  reflexivity.
Qed.

Example unsafe_dirty_transfer_not_hygienic :
  ~hygienic [Cut Liver; Transfer Knife Plate].
Proof.
  unfold hygienic.
  intros [kd [bd [pd [td [hd H]]]]].
  simpl in H.
  discriminate.
Qed.

Example unsafe_dirty_transfer_is_lethal :
  edible (run clean_state [Cut Liver; Transfer Knife Plate]) = false.
Proof.
  reflexivity.
Qed.

Example unsafe_dirty_hands_not_hygienic :
  ~hygienic [Cut Liver; Wash Knife; Wash Board; Cut Flesh].
Proof.
  unfold hygienic.
  intros [kd [bd [pd [td [hd H]]]]].
  simpl in H.
  discriminate.
Qed.

Example unsafe_dirty_hands_is_lethal :
  edible (run clean_state [Cut Liver; Wash Knife; Wash Board; Cut Flesh]) = false.
Proof.
  reflexivity.
Qed.

End WithSkinToxicity.
