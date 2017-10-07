Require Import Relations.
Require Import List.
Import ListNotations.

Record lts {S L : Type} :=
  {
    init : S -> Prop;
    step : S -> L -> S -> Prop
  }.

Inductive trace {S L} (m : @lts S L) : S -> list L -> Prop :=
| init_trace : forall s, init m s -> trace m s []
| step_trace : forall s l s' t,
    trace m s t -> step m s l s' -> trace m s' (l::t).

Definition has_trace {S L} (m : @lts S L) (t : list L) : Prop :=
  exists s, trace m s t.

Definition reachable {S L} (m : @lts S L) (s : S) : Prop :=
  exists t, trace m s t.

Definition reactive_state {S L} (m : @lts S L) (s : S) : Prop :=
  exists l s', step m s l s'.

Definition deterministic_state {S L} (m : @lts S L) (s : S) : Prop :=
  forall l1 s1 l2 s2,
    step m s l1 s1 -> step m s l2 s2 -> s1 = s2 /\ l1 = l2.

Definition reactive {S L} (m : @lts S L) : Prop :=
  forall s, reachable m s -> reactive_state m s.

Definition deterministic {S L} (m : @lts S L) : Prop :=
  forall s, reachable m s -> deterministic_state m s.

Definition trace_equiv {S L} (m1 m2 : @lts S L) : Prop :=
  forall t, has_trace m1 t <-> has_trace m2 t.

Definition simulation {S L} (m : @lts S L) (R : relation S) : Prop :=
  forall l p q,
    R p q ->
    forall p', step m p l p' -> exists q', R p' q' /\ step m q l q'.

Definition bisimulation {S L} (m : @lts S L) (R : relation S) : Prop :=
  forall l p q,
    R p q ->
    (forall p', step m p l p' -> exists q', R p' q' /\ step m q l q') /\
    (forall q', step m q l q' -> exists p', R p' q' /\ step m p l p').

Theorem bisim_sim_inv :
  forall S L (m : @lts S L) R,
    bisimulation m R <-> simulation m R /\ simulation m (transp _ R).
Proof.
  intros S L m R.
  split; unfold simulation, bisimulation, transp.

  (* -> *)
  intros H.
  split.
  intros l p q HR p' Hp.
  specialize (H l p q HR).
  destruct H as (H1,H2).
  specialize (H1 p').
  apply H1; assumption.

  intros l q p HR q' Hq.
  specialize (H l p q HR).
  destruct H as (H1,H2).
  specialize (H2 q').
  apply H2; assumption.

  (* <- *)
  intros (H1,H2) l p q HR.
  split.

  intros p' Hp.
  specialize (H1 l p q HR p' Hp).
  inversion H1 as (q',Hq); subst; clear H1.
  exists q'; auto.

  intros q' Hq.
  specialize (H2 l q p HR q' Hq).
  inversion H2 as (p',Hp); subst; clear H2.
  exists p'; auto.
Qed.
