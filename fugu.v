(******************************************************************************)
(*                                                                            *)
(*               Fugu-Safety-Verified: Cross-Contamination Logic              *)
(*                                                                            *)
(*     Models knife contamination across pufferfish parts (flesh/skin vs.     *)
(*     liver/ovaries) and proves that any safe cut made with a dirty knife    *)
(*     or board is lethal unless preceded by a wash. A simple policy checker  *)
(*     characterizes hygienic sequences and guarantees edibility.             *)
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
Inductive Tool := Knife | Board | Plate.

Parameter skin_is_lethal : bool.

Definition lethal_part (p : Part) : bool :=
  match p with
  | Flesh => false
  | Skin => skin_is_lethal
  | _ => true
  end.

(** Kitchen state *)
Record State := {
  knife_dirty : bool;
  board_dirty : bool;
  plate_dirty : bool;
  edible : bool
}.

Definition mk_state kd bd pd ed : State :=
  {| knife_dirty := kd; board_dirty := bd; plate_dirty := pd; edible := ed |}.

Definition clean_state : State := mk_state false false false true.

Definition dirty_of (s : State) (t : Tool) : bool :=
  match t with
  | Knife => knife_dirty s
  | Board => board_dirty s
  | Plate => plate_dirty s
  end.

Definition set_tool (t : Tool) (v : bool) (s : State) : State :=
  match t with
  | Knife => mk_state v (board_dirty s) (plate_dirty s) (edible s)
  | Board => mk_state (knife_dirty s) v (plate_dirty s) (edible s)
  | Plate => mk_state (knife_dirty s) (board_dirty s) v (edible s)
  end.

(** Actions *)
Inductive Action :=
| Wash (t : Tool)
| Cut (p : Part)
| Transfer (src dst : Tool).

(** One transition step *)
Definition step (s : State) (a : Action) : State :=
  match a with
  | Wash t => set_tool t false s
  | Cut p =>
      if lethal_part p
      then mk_state true true (plate_dirty s) false
      else if knife_dirty s || board_dirty s
           then mk_state (knife_dirty s) (board_dirty s) (plate_dirty s) false
           else s
  | Transfer src dst =>
      if dirty_of s src
      then
        let s' := set_tool dst true s in
        mk_state (knife_dirty s') (board_dirty s') (plate_dirty s') false
      else s
  end.

Fixpoint run (s : State) (as_ : list Action) : State :=
  match as_ with
  | [] => s
  | a :: rest => run (step s a) rest
  end.

(** Basic invariants *)
Lemma step_edible_false : forall s a, edible s = false -> edible (step s a) = false.
Proof.
  intros s a H.
  destruct a as [t|p|src dst]; simpl.
  - destruct t; simpl; rewrite H; reflexivity.
  - destruct (lethal_part p) eqn:Hp; simpl.
    + reflexivity.
    + destruct (knife_dirty s || board_dirty s) eqn:Horb; simpl; try reflexivity.
      exact H.
  - destruct (dirty_of s src); simpl; try reflexivity; exact H.
Qed.

Lemma run_edible_false : forall s acts, edible s = false -> edible (run s acts) = false.
Proof.
  intros s acts; revert s.
  induction acts as [|a rest IH]; intros s H; simpl.
  - exact H.
  - apply IH. apply step_edible_false; assumption.
Qed.

Lemma safe_cut_when_dirty_lethal :
  forall s p,
    lethal_part p = false ->
    (knife_dirty s = true \/ board_dirty s = true) ->
    edible (step s (Cut p)) = false.
Proof.
  intros s p Hp Hd; simpl.
  rewrite Hp.
  destruct (knife_dirty s || board_dirty s) eqn:Heq.
  - reflexivity.
  - apply Bool.orb_false_iff in Heq as [Hk Hb].
    destruct Hd as [Hk' | Hb']; rewrite ?Hk', ?Hb' in *; congruence.
Qed.

Lemma transfer_from_dirty_lethal :
  forall s src dst,
    dirty_of s src = true ->
    edible (step s (Transfer src dst)) = false.
Proof. intros; simpl; rewrite H; reflexivity. Qed.

(** Policy checker (returns final cleanliness if hygienic) *)
Fixpoint policy_state (acts : list Action) (kd bd pd : bool)
  : option (bool * bool * bool) :=
  match acts with
  | [] => Some (kd, bd, pd)
  | Wash Knife :: rest => policy_state rest false bd pd
  | Wash Board :: rest => policy_state rest kd false pd
  | Wash Plate :: rest => policy_state rest kd bd false
  | Cut p :: rest =>
      if lethal_part p then None
      else if kd || bd then None
           else policy_state rest kd bd pd
  | Transfer src _dst :: rest =>
      let dirty_src := match src with
                       | Knife => kd | Board => bd | Plate => pd end in
      if dirty_src then None else policy_state rest kd bd pd
  end.

Definition matches (s : State) (kd bd pd : bool) : Prop :=
  knife_dirty s = kd /\ board_dirty s = bd /\ plate_dirty s = pd /\ edible s = true.

Lemma policy_run_sound :
  forall acts s kd bd pd kd' bd' pd',
    matches s kd bd pd ->
    policy_state acts kd bd pd = Some (kd', bd', pd') ->
    matches (run s acts) kd' bd' pd'.
Proof.
  induction acts as [|a rest IH]; simpl; intros s kd bd pd kd' bd' pd' Hm Hpol.
  - inversion Hpol; subst; assumption.
  - destruct a as [t|p|src dst]; simpl in Hpol.
    + (* Wash *)
      destruct t; simpl in Hpol.
      * eapply IH with (s:=set_tool Knife false s) (kd:=false) (bd:=bd) (pd:=pd); try exact Hpol.
        destruct Hm as [Hk [Hb [Hp He]]]; repeat split; simpl; auto.
      * eapply IH with (s:=set_tool Board false s) (kd:=kd) (bd:=false) (pd:=pd); try exact Hpol.
        destruct Hm as [Hk [Hb [Hp He]]]; repeat split; simpl; auto.
      * eapply IH with (s:=set_tool Plate false s) (kd:=kd) (bd:=bd) (pd:=false); try exact Hpol.
        destruct Hm as [Hk [Hb [Hp He]]]; repeat split; simpl; auto.
    + (* Cut *)
      destruct (lethal_part p) eqn:Hp'; try discriminate.
      destruct (kd || bd) eqn:Hdirty; try discriminate.
      destruct Hm as [Hk [Hb [Hp He]]].
      apply Bool.orb_false_iff in Hdirty as [Hkd Hbd].
      assert (step s (Cut p) = s) as Hstep.
      { assert (Hkn : knife_dirty s = false) by (rewrite Hk; exact Hkd).
        assert (Hbn : board_dirty s = false) by (rewrite Hb; exact Hbd).
        unfold step; rewrite Hp', Hkn, Hbn; reflexivity. }
      rewrite Hstep.
      eapply IH with (s:=s) (kd:=kd) (bd:=bd) (pd:=pd) (kd':=kd') (bd':=bd') (pd':=pd');
        [repeat split; assumption|exact Hpol].
    + (* Transfer *)
      remember (match src with Knife => kd | Board => bd | Plate => pd end) as dsrc.
      destruct Hm as [Hk [Hb [Hp He]]].
      destruct dsrc; try discriminate.
      assert (dirty_of s src = false) as Hclean.
      { destruct src; simpl in *; subst; rewrite ?Hk, ?Hb, ?Hp; auto. }
      assert (step s (Transfer src dst) = s) as Hstep by (unfold step; rewrite Hclean; reflexivity).
      rewrite Hstep.
      eapply IH with (s:=s) (kd:=kd) (bd:=bd) (pd:=pd) (kd':=kd') (bd':=bd') (pd':=pd');
        [repeat split; assumption|exact Hpol].
Qed.

Theorem policy_sound :
  forall acts kd bd pd,
    policy_state acts false false false = Some (kd, bd, pd) ->
    edible (run clean_state acts) = true.
Proof.
  intros acts kd bd pd Hpol.
  assert (matches clean_state false false false) as Hclean by (repeat split; reflexivity).
  pose proof (@policy_run_sound acts clean_state false false false kd bd pd Hclean Hpol) as Hm.
  destruct Hm as [_ [_ [_ Hed]]]; exact Hed.
Qed.

Theorem dirty_safe_cut_immediately_lethal :
  forall actions,
    edible (run (mk_state true false false true) (Cut Flesh :: actions)) = false.
Proof.
  intros actions.
  simpl.
  assert (edible (step (mk_state true false false true) (Cut Flesh)) = false) as Hstep by reflexivity.
  apply run_edible_false; assumption.
Qed.
