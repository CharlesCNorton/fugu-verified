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
Inductive Tool := Knife | Board | Plate | Trash.

Parameter skin_is_lethal : bool.

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
  edible : bool
}.

Definition mk_state (kd bd pd td ed : bool) : State :=
  {| knife_dirty := kd;
     board_dirty := bd;
     plate_dirty := pd;
     trash_dirty := td;
     edible := ed |}.

Definition clean_state : State := mk_state false false false false true.

Definition dirty_of (s : State) (t : Tool) : bool :=
  match t with
  | Knife => knife_dirty s
  | Board => board_dirty s
  | Plate => plate_dirty s
  | Trash => trash_dirty s
  end.

Definition set_tool (t : Tool) (v : bool) (s : State) : State :=
  match t with
  | Knife => mk_state v (board_dirty s) (plate_dirty s) (trash_dirty s) (edible s)
  | Board => mk_state (knife_dirty s) v (plate_dirty s) (trash_dirty s) (edible s)
  | Plate => mk_state (knife_dirty s) (board_dirty s) v (trash_dirty s) (edible s)
  | Trash => mk_state (knife_dirty s) (board_dirty s) (plate_dirty s) v (edible s)
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
      (* knife and board contact each other and the part *)
      let lp := lethal_part p in
      let kb := (knife_dirty s || board_dirty s) || lp in
      (* Cutting a toxic part contaminates tools but does not, by itself,
         render the meal unsafe (you can discard that part). *)
      let ed :=
        if lp then edible s
        else if (knife_dirty s || board_dirty s) then false else edible s in
      mk_state kb kb (plate_dirty s) (trash_dirty s) ed

  | Transfer src dst =>
      (* transfer creates contact between src and dst; contamination spreads *)
      let d := dirty_of s src || dirty_of s dst in
      let ed := if d then false else edible s in
      let s' := set_tool dst d (set_tool src d s) in
      mk_state (knife_dirty s') (board_dirty s') (plate_dirty s') (trash_dirty s') ed

  | Discard src =>
      (* discard to trash: only contaminates Trash from the source;
         does not affect edibility since the moved item is not consumed *)
      let td := trash_dirty s || dirty_of s src in
      mk_state (knife_dirty s) (board_dirty s) (plate_dirty s) td (edible s)
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
    step s (Cut p) = s.
Proof.
  intros s p Hp Hk Hb.
  destruct s as [k b pd td ed]; simpl in *.
  unfold step; simpl.
  rewrite Hp, Hk, Hb.
  simpl.
  reflexivity.
Qed.

Lemma step_transfer_clean :
  forall s src dst,
    dirty_of s src = false ->
    dirty_of s dst = false ->
    step s (Transfer src dst) = s.
Proof.
  intros s src dst Hsrc Hdst.
  destruct s as [k b p t ed]; simpl in *.
  destruct src; destruct dst; simpl in *;
    rewrite ?Hsrc, ?Hdst; simpl; reflexivity.
Qed.

(******************************************************************************)
(* Basic invariants                                                           *)
(******************************************************************************)

Lemma step_edible_false :
  forall s a, edible s = false -> edible (step s a) = false.
Proof.
  intros s a Hed.
  destruct a as [t|p|src dst|src]; simpl.
  - (* Wash *)
    destruct t; simpl; rewrite Hed; reflexivity.
  - (* Cut *)
    destruct (lethal_part p) eqn:Hp; simpl.
    + exact Hed.
    + destruct (knife_dirty s || board_dirty s) eqn:Hkb; simpl; try reflexivity.
      exact Hed.
  - (* Transfer *)
    destruct (dirty_of s src || dirty_of s dst) eqn:Hd; simpl; try reflexivity.
    exact Hed.
  - (* Discard *)
    simpl. exact Hed.
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
    (knife_dirty s = true \/ board_dirty s = true) ->
    edible (step s (Cut p)) = false.
Proof.
  intros s p Hp Hd.
  unfold step; simpl.
  rewrite Hp; simpl.
  destruct (knife_dirty s || board_dirty s) eqn:Hkb.
  - reflexivity.
  - apply Bool.orb_false_iff in Hkb as [Hk Hb].
    destruct Hd as [Hk' | Hb'].
    + rewrite Hk in Hk'. discriminate.
    + rewrite Hb in Hb'. discriminate.
Qed.

Lemma transfer_with_dirty_lethal :
  forall s src dst,
    (dirty_of s src = true \/ dirty_of s dst = true) ->
    edible (step s (Transfer src dst)) = false.
Proof.
  intros s src dst Hd.
  unfold step; simpl.
  destruct (dirty_of s src || dirty_of s dst) eqn:Horb.
  - reflexivity.
  - apply Bool.orb_false_iff in Horb as [Hsrc Hdst].
    destruct Hd as [Hsrc' | Hdst'].
    + rewrite Hsrc in Hsrc'. discriminate.
    + rewrite Hdst in Hdst'. discriminate.
Qed.

Theorem dirty_safe_cut_trace_lethal :
  forall s p actions,
    lethal_part p = false ->
    (knife_dirty s = true \/ board_dirty s = true) ->
    edible (run s (Cut p :: actions)) = false.
Proof.
  intros s p actions Hp Hd.
  simpl.
  apply run_edible_false.
  apply safe_cut_when_dirty_lethal; assumption.
Qed.

Theorem dirty_transfer_trace_lethal :
  forall s src dst actions,
    (dirty_of s src = true \/ dirty_of s dst = true) ->
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

Definition matches (s : State) (kd bd pd td : bool) : Prop :=
  knife_dirty s = kd /\
  board_dirty s = bd /\
  plate_dirty s = pd /\
  trash_dirty s = td /\
  edible s = true.

(** Policy checker returns final cleanliness if hygienic; rejects otherwise. *)
Fixpoint policy_state (acts : list Action) (kd bd pd td : bool)
  : option (bool * bool * bool * bool) :=
  match acts with
  | [] => Some (kd, bd, pd, td)

  | Wash Knife :: rest => policy_state rest false bd pd td
  | Wash Board :: rest => policy_state rest kd false pd td
  | Wash Plate :: rest => policy_state rest kd bd false td
  | Wash Trash :: rest => policy_state rest kd bd pd false

  | Cut p :: rest =>
      if lethal_part p
      then policy_state rest true true pd td
      else if kd || bd then None
           else policy_state rest kd bd pd td

  | Transfer src dst :: rest =>
      let dsrc :=
        match src with Knife => kd | Board => bd | Plate => pd | Trash => td end in
      let ddst :=
        match dst with Knife => kd | Board => bd | Plate => pd | Trash => td end in
      if dsrc || ddst then None else policy_state rest kd bd pd td

  | Discard src :: rest =>
      let dsrc :=
        match src with Knife => kd | Board => bd | Plate => pd | Trash => td end in
      policy_state rest kd bd pd (td || dsrc)
  end.

(******************************************************************************)
(* Policy soundness: accepted traces preserve edibility                        *)
(******************************************************************************)

Lemma policy_run_sound :
  forall acts s kd bd pd td kd' bd' pd' td',
    matches s kd bd pd td ->
    policy_state acts kd bd pd td = Some (kd', bd', pd', td') ->
    matches (run s acts) kd' bd' pd' td'.
Proof.
  induction acts as [|a rest IH]; simpl;
    intros s kd bd pd td kd' bd' pd' td' Hm Hpol.
  - inversion Hpol; subst; exact Hm.
  - destruct a as [t|p|src dst|src]; simpl in Hpol.

    + (* Wash *)
      destruct t; simpl in Hpol.
      * eapply IH with (s:=set_tool Knife false s) (kd:=false) (bd:=bd) (pd:=pd) (td:=td); try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht He]]]]; repeat split; simpl; auto.
      * eapply IH with (s:=set_tool Board false s) (kd:=kd) (bd:=false) (pd:=pd) (td:=td); try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht He]]]]; repeat split; simpl; auto.
      * eapply IH with (s:=set_tool Plate false s) (kd:=kd) (bd:=bd) (pd:=false) (td:=td); try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht He]]]]; repeat split; simpl; auto.
      * eapply IH with (s:=set_tool Trash false s) (kd:=kd) (bd:=bd) (pd:=pd) (td:=false); try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht He]]]]; repeat split; simpl; auto.

    + (* Cut *)
      destruct (lethal_part p) eqn:Hp; simpl in Hpol.
      * (* lethal cut: forces knife+board dirty *)
        eapply IH with (s:=step s (Cut p)) (kd:=true) (bd:=true) (pd:=pd) (td:=td); try exact Hpol.
        destruct Hm as [_ [_ [Hp0 [Ht He]]]].
        repeat split; simpl.
        -- unfold step; simpl. rewrite Hp. rewrite Bool.orb_true_r. reflexivity.
        -- unfold step; simpl. rewrite Hp. rewrite Bool.orb_true_r. reflexivity.
        -- unfold step; simpl. exact Hp0.
        -- unfold step; simpl. exact Ht.
        -- unfold step; simpl. rewrite Hp. exact He.

      * (* safe cut: requires clean knife+board *)
        destruct (kd || bd) eqn:Hdirty; try discriminate.
        apply Bool.orb_false_iff in Hdirty as [Hkd Hbd].
        destruct Hm as [Hk [Hb [Hp0 [Ht He]]]].
        assert (knife_dirty s = false) as Hk0 by (rewrite Hk; exact Hkd).
        assert (board_dirty s = false) as Hb0 by (rewrite Hb; exact Hbd).
        assert (step s (Cut p) = s) as Hstep by (apply step_cut_safe_clean; auto).
        rewrite Hstep.
        eapply IH; try exact Hpol.
        repeat split; assumption.

    + (* Transfer *)
      remember (match src with Knife => kd | Board => bd | Plate => pd | Trash => td end) as dsrc.
      remember (match dst with Knife => kd | Board => bd | Plate => pd | Trash => td end) as ddst.
      destruct (dsrc || ddst) eqn:Hdirty; try discriminate.
      apply Bool.orb_false_iff in Hdirty as [Hdsrc Hddst].
      destruct Hm as [Hk [Hb [Hp0 [Ht He]]]].

      assert (dirty_of s src = false) as Hsrc_clean.
      { destruct src; simpl in *; subst dsrc; rewrite ?Hk, ?Hb, ?Hp0, ?Ht; assumption. }
      assert (dirty_of s dst = false) as Hdst_clean.
      { destruct dst; simpl in *; subst ddst; rewrite ?Hk, ?Hb, ?Hp0, ?Ht; assumption. }

      assert (step s (Transfer src dst) = s) as Hstep by (apply step_transfer_clean; assumption).
      rewrite Hstep.
      eapply IH; try exact Hpol.
      repeat split; assumption.

    + (* Discard *)
      remember (match src with Knife => kd | Board => bd | Plate => pd | Trash => td end) as dsrc.
      eapply IH with (s:=step s (Discard src)) (kd:=kd) (bd:=bd) (pd:=pd) (td:=td || dsrc); try exact Hpol.
      destruct Hm as [Hk [Hb [Hp0 [Ht He]]]].
      repeat split; simpl.
      * (* knife *)
        unfold step; simpl. exact Hk.
      * (* board *)
        unfold step; simpl. exact Hb.
      * (* plate *)
        unfold step; simpl. exact Hp0.
      * (* trash *)
        unfold step; simpl.
        subst dsrc.
        destruct src; simpl in *; rewrite ?Hk, ?Hb, ?Hp0, ?Ht; reflexivity.
      * (* edible *)
        unfold step; simpl. exact He.
Qed.

Theorem policy_sound :
  forall acts kd bd pd td,
    policy_state acts false false false false = Some (kd, bd, pd, td) ->
    edible (run clean_state acts) = true.
Proof.
  intros acts kd bd pd td Hpol.
  assert (matches clean_state false false false false) as Hclean by (repeat split; reflexivity).
  pose proof (@policy_run_sound acts clean_state false false false false kd bd pd td Hclean Hpol) as Hm.
  destruct Hm as [_ [_ [_ [_ Hed]]]]; exact Hed.
Qed.

(******************************************************************************)
(* Policy completeness: if execution stays edible, the policy must accept      *)
(******************************************************************************)

Lemma policy_run_complete :
  forall acts s kd bd pd td,
    matches s kd bd pd td ->
    policy_state acts kd bd pd td = None ->
    edible (run s acts) = false.
Proof.
  induction acts as [|a rest IH]; intros s kd bd pd td Hm Hpol; simpl in Hpol.
  - discriminate.
  - destruct a as [t|p|src dst|src].

    + (* Wash *)
      destruct t; simpl in Hpol.
      * apply IH with (s:=set_tool Knife false s) (kd:=false) (bd:=bd) (pd:=pd) (td:=td); try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht He]]]]; repeat split; simpl; auto.
      * apply IH with (s:=set_tool Board false s) (kd:=kd) (bd:=false) (pd:=pd) (td:=td); try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht He]]]]; repeat split; simpl; auto.
      * apply IH with (s:=set_tool Plate false s) (kd:=kd) (bd:=bd) (pd:=false) (td:=td); try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht He]]]]; repeat split; simpl; auto.
      * apply IH with (s:=set_tool Trash false s) (kd:=kd) (bd:=bd) (pd:=pd) (td:=false); try exact Hpol.
        destruct Hm as [Hk [Hb [Hp0 [Ht He]]]]; repeat split; simpl; auto.

    + (* Cut *)
      destruct (lethal_part p) eqn:Hp; simpl in Hpol.
      * (* lethal cut: failure comes from the tail *)
        apply IH with (s:=step s (Cut p)) (kd:=true) (bd:=true) (pd:=pd) (td:=td); try exact Hpol.
        destruct Hm as [_ [_ [Hp0 [Ht He]]]].
        repeat split; simpl.
        -- unfold step; simpl. rewrite Hp. rewrite Bool.orb_true_r. reflexivity.
        -- unfold step; simpl. rewrite Hp. rewrite Bool.orb_true_r. reflexivity.
        -- unfold step; simpl. exact Hp0.
        -- unfold step; simpl. exact Ht.
        -- unfold step; simpl. rewrite Hp. exact He.

      * (* safe cut: policy fails immediately if kd||bd=true, else tail fails *)
        destruct (kd || bd) eqn:Hdirty.
        -- (* immediate rejection: safe cut on dirty knife/board => edible becomes false *)
           destruct Hm as [Hk [Hb _]].
           assert (kd = true \/ bd = true) as Hkd_or.
           { destruct kd, bd; simpl in Hdirty; try discriminate; auto. }
           assert (knife_dirty s = true \/ board_dirty s = true) as Htools_dirty.
           { destruct Hkd_or as [Hkd' | Hbd'].
             - left. rewrite Hk. exact Hkd'.
             - right. rewrite Hb. exact Hbd'. }
           simpl.
           apply run_edible_false.
           apply safe_cut_when_dirty_lethal; assumption.
        -- (* kd||bd=false: tail must fail; cut is a no-op *)
           apply Bool.orb_false_iff in Hdirty as [Hkd Hbd].
           destruct Hm as [Hk [Hb [Hp0 [Ht He]]]].
           assert (knife_dirty s = false) as Hk0 by (rewrite Hk; exact Hkd).
           assert (board_dirty s = false) as Hb0 by (rewrite Hb; exact Hbd).
           assert (step s (Cut p) = s) as Hstep by (apply step_cut_safe_clean; auto).
           change (edible (run (step s (Cut p)) rest) = false).
           rewrite Hstep.
           apply IH with (s:=s) (kd:=kd) (bd:=bd) (pd:=pd) (td:=td); try exact Hpol.
           repeat split; assumption.

    + (* Transfer *)
      remember (match src with Knife => kd | Board => bd | Plate => pd | Trash => td end) as dsrc.
      remember (match dst with Knife => kd | Board => bd | Plate => pd | Trash => td end) as ddst.
      destruct (dsrc || ddst) eqn:Hdirty.
      * (* immediate rejection: dirty endpoint => edible becomes false *)
        destruct Hm as [Hk [Hb [Hp0 [Ht He]]]].
        assert (dsrc = true \/ ddst = true) as Hor.
        { destruct dsrc, ddst; simpl in Hdirty; try discriminate; auto. }

        assert (dirty_of s src = true \/ dirty_of s dst = true) as Hdirty_tools.
        { destruct Hor as [Hdsrc | Hddst].
          - left.
            destruct src; simpl in *; subst dsrc; rewrite ?Hk, ?Hb, ?Hp0, ?Ht; exact Hdsrc.
          - right.
            destruct dst; simpl in *; subst ddst; rewrite ?Hk, ?Hb, ?Hp0, ?Ht; exact Hddst. }

        simpl.
        apply run_edible_false.
        apply transfer_with_dirty_lethal; exact Hdirty_tools.

      * (* clean endpoints: transfer is a no-op; tail must fail *)
        apply Bool.orb_false_iff in Hdirty as [Hdsrc Hddst].
        destruct Hm as [Hk [Hb [Hp0 [Ht He]]]].

        assert (dirty_of s src = false) as Hsrc_clean.
        { destruct src; simpl in *; subst dsrc; rewrite ?Hk, ?Hb, ?Hp0, ?Ht; assumption. }
        assert (dirty_of s dst = false) as Hdst_clean.
        { destruct dst; simpl in *; subst ddst; rewrite ?Hk, ?Hb, ?Hp0, ?Ht; assumption. }

        assert (step s (Transfer src dst) = s) as Hstep by (apply step_transfer_clean; assumption).
        change (edible (run (step s (Transfer src dst)) rest) = false).
        rewrite Hstep.
        apply IH with (s:=s) (kd:=kd) (bd:=bd) (pd:=pd) (td:=td); try exact Hpol.
        repeat split; assumption.

    + (* Discard *)
      remember (match src with Knife => kd | Board => bd | Plate => pd | Trash => td end) as dsrc.
      apply IH with (s:=step s (Discard src)) (kd:=kd) (bd:=bd) (pd:=pd) (td:=td || dsrc); try exact Hpol.
      destruct Hm as [Hk [Hb [Hp0 [Ht He]]]].
      repeat split; simpl.
      * unfold step; simpl. exact Hk.
      * unfold step; simpl. exact Hb.
      * unfold step; simpl. exact Hp0.
      * unfold step; simpl.
        subst dsrc.
        destruct src; simpl in *; rewrite ?Hk, ?Hb, ?Hp0, ?Ht; reflexivity.
      * unfold step; simpl. exact He.
Qed.

Theorem policy_complete :
  forall acts,
    edible (run clean_state acts) = true ->
    exists kd bd pd td,
      policy_state acts false false false false = Some (kd, bd, pd, td).
Proof.
  intros acts Hed.
  destruct (policy_state acts false false false false) as [[[[kd bd] pd] td]|] eqn:Hpol.
  - exists kd, bd, pd, td. reflexivity.
  - exfalso.
    assert (matches clean_state false false false false) as Hm0 by (repeat split; reflexivity).
    pose proof (@policy_run_complete acts clean_state false false false false Hm0 Hpol) as Hcontra.
    rewrite Hed in Hcontra. discriminate.
Qed.

Definition hygienic (acts : list Action) : Prop :=
  exists kd bd pd td,
    policy_state acts false false false false = Some (kd, bd, pd, td).

Theorem hygienic_iff_edible :
  forall acts,
    hygienic acts <-> edible (run clean_state acts) = true.
Proof.
  intros acts; split.
  - intros [kd [bd [pd [td Hpol]]]].
    eapply policy_sound; eauto.
  - intros Hed.
    apply policy_complete; exact Hed.
Qed.

(******************************************************************************)
(* Small corollaries / examples                                               *)
(******************************************************************************)

Corollary dirty_safe_cut_immediately_lethal_example :
  forall actions,
    edible (run (mk_state true false false false true) (Cut Flesh :: actions)) = false.
Proof.
  intros actions.
  eapply dirty_safe_cut_trace_lethal with (p:=Flesh); simpl; auto.
Qed.

Example toxic_trim_discard_wash_serve_is_hygienic :
  hygienic [Cut Liver; Discard Board; Wash Knife; Wash Board; Cut Flesh; Transfer Board Plate].
Proof.
  unfold hygienic.
  (* This holds for any value of skin_is_lethal. *)
  eexists false, false, false, true.
  simpl.
  reflexivity.
Qed.

Example toxic_trim_discard_wash_serve_is_edible :
  edible (run clean_state [Cut Liver; Discard Board; Wash Knife; Wash Board; Cut Flesh; Transfer Board Plate]) = true.
Proof.
  apply hygienic_iff_edible.
  apply toxic_trim_discard_wash_serve_is_hygienic.
Qed.
