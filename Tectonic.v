(** * Tectonic *)

Require Import Reals.
Require Import List.
Require Import Lia.
Require Import Lra.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapFacts.
Require Import Psatz.
From RecordUpdate Require Import RecordUpdate.
Import ListNotations.
Local Open Scope R_scope.

(** * Numbers
    These are just aliases for real numbers ([R]).
 *)

Notation amount := R.
Notation price := R.
Notation timestamp := R.

(** * Protocol parameters
    - [r_supcrit], the supercritical reserve ratio threshold
    - [r_crit], the critical reserve ratio threshold
    - [r_safe], the safe reserve ratio threshold
    - [f_T], the treasury fee rate
    - [f], the protocol fee rate
    - and [phi_max], the maximum stability fee rate.

    They are dependently typed as real numbers with constraints.
 *)

Parameter r_supcrit_ : {x : R | 1 < x}.
Parameter r_crit_    : {x : R | proj1_sig r_supcrit_ < x}.
Parameter r_safe_    : {x : R | proj1_sig r_crit_ < x}.
Parameter f_T_       : {x : R | 0 <= x /\ x < 1}.
Parameter f_         : {x : R | 0 <= x /\ x < 1 /\ x + (proj1_sig f_T_) < 1}.
Parameter phi_max_   : {x : R | 0 <= x /\ x < 1}.

Definition r_supcrit := proj1_sig r_supcrit_.
Definition r_crit := proj1_sig r_crit_.
Definition r_safe := proj1_sig r_safe_.
Definition f_T := proj1_sig f_T_.
Definition f := proj1_sig f_.
Definition phi_max := proj1_sig phi_max_.

Lemma r_supcrit_gt_1 : 1 < r_supcrit.
Proof.
  unfold r_supcrit.
  exact (proj2_sig r_supcrit_).
Qed.

Lemma r_crit_gt_supcrit : r_supcrit < r_crit.
Proof.
  unfold r_crit.
  exact (proj2_sig r_crit_).
Qed.

Lemma r_safe_gt_crit : r_crit < r_safe.
Proof.
  unfold r_safe.
  exact (proj2_sig r_safe_).
Qed.

Lemma r_crit_gt_1 : 1 < r_crit.
Proof.
  pose proof r_supcrit_gt_1.
  pose proof r_crit_gt_supcrit.
  lra.
Qed.

Lemma r_safe_gt_supcrit : r_supcrit < r_safe.
Proof.
  pose proof r_crit_gt_supcrit.
  pose proof r_safe_gt_crit.
  lra.
Qed.

Lemma r_safe_minus_r_supcrit_pos :
  0 < r_safe - r_supcrit.
Proof.
  pose proof r_safe_gt_supcrit.
  lra.
Qed.

(** * Oracle
    We represent the oracle as a function from time to price.
    The oracle is supposed to return X^{PC}_{BC}, the price of 1 peg currency in basecoins.
 *)

Definition Oracle : Type := timestamp -> price.
Parameter oracle : Oracle.

Axiom oracle_pos :
  forall t, 0  < oracle t.

(** * Users and Maps *)

Definition User : Type := nat.
Definition UserSet := list User.

Parameter Users : UserSet.
Axiom Users_NoDup : NoDup Users.

Module UserOT := Nat_as_OT.
Module UserMap := FMapList.Make(UserOT).
Module UMFacts := WFacts_fun UserOT UserMap.

Definition getR (u : User) (m : UserMap.t R) : R :=
  match UserMap.find u m with
  | Some x => x
  | None => 0
  end.

Definition setR (u : User) (v : R) (m : UserMap.t R) : UserMap.t R :=
  UserMap.add u v m.

Definition addR (u : User) (dv : R) (m : UserMap.t R) : UserMap.t R :=
  setR u (getR u m + dv) m.

Definition getNat (u : User) (m : UserMap.t nat) : nat :=
  match UserMap.find u m with
  | Some n => n
  | None => 0%nat
  end.

Definition setNat (u : User) (n : nat) (m : UserMap.t nat) : UserMap.t nat :=
  UserMap.add u n m.

(** * State *)

Record State := mkState {
  R_ : amount;
  N_SC : amount;
  N_EC : amount;
  B_SC : UserMap.t amount;
  B_EC : UserMap.t amount;
  H : UserSet;
  T : UserMap.t timestamp
}.

#[export] Instance etaState : Settable State :=
  settable! mkState
          < R_; N_SC; N_EC; B_SC; B_EC; H; T >.

(** * Initial State
      Everything set to 1 initially and empty holders. 
 *)

Definition init_user : User := 0%nat.

Definition init_state : State :=
  {|
    R_ := 1;
    N_SC := 1;
    N_EC := 1;
    B_SC := setR init_user 1 (UserMap.empty amount);
    B_EC := setR init_user 1 (UserMap.empty amount);
    H := [init_user];
    T := setR init_user 0 (UserMap.empty timestamp)
  |}.

(** * Holders *)

Definition get_B_SC (u : User) (st : State) : R :=
  getR u (B_SC st).

Definition get_B_EC (u : User) (st : State) : R :=
  getR u (B_EC st).

Definition add_holder (u : User) (t : timestamp) (st : State) : State :=
  if in_dec Nat.eq_dec u (H st)
  then
    st
  else
    st
    <| H := (H st) ++ [u]   |>
    <| T := setR u t (T st) |>.

Definition remove_holder (u : User) (st : State) : State :=
  if in_dec Nat.eq_dec u (H st)
  then
    st
    <| H := remove Nat.eq_dec u (H st) |>
  else
    st.

Definition update_holder (u : User) (t : timestamp) (st : State) : State :=
  if Rlt_dec 0 (get_B_SC u st)
  then
    if in_dec Nat.eq_dec u (H st) then
      st
    else
      add_holder u t st
  else
    if in_dec Nat.eq_dec u (H st) then
      remove_holder u st
    else
      st.

(** ** Well-formed holder set *)

(** * Prices
    - the oracle [oracle] gives us the price of one peg currency in basecoins [X_PC_BC],
    - which sets the stablecoin target price [P_target_SC]
    - which sets the stablecoin minting price [P_mint_SC].
    - Meanwhile, the stablecoin redemption price [P_redeem_SC] is a minimum of the target price and reserve per stablecoin. (TODO: update)
    - The equity coin price (both mint and redeem) [P_EC] is equity divided by number of equity coins.
      Thus it is defined after equity is defined.

    The zero cases/guards are not present due to invariants on the positivity of [N_SC, N_EC, R] that removes the need for casing.
 *)
Definition X_PC_BC (t : timestamp) : price :=
  oracle t.

Definition P_target_SC (t : timestamp) : price :=
  X_PC_BC t.

Definition P_mint_SC (t : timestamp) : price :=
  P_target_SC t.

(** ** True ratio
    Several prices depend on the true ratio, since they case on whether q < r_supcrit.
 *)
Definition q (t : timestamp) (st : State) : R :=
  R_ st / (N_SC st * P_target_SC t).

Definition P_redeem_SC (t : timestamp) (st : State) : price :=
  if Rlt_dec (q t st) r_supcrit then
    R_ st / (N_SC st * r_supcrit)
  else
    P_target_SC t.

(** * Liabilities, equity, reserve ratio
    Similarly, note that the zero guards are removed.
 *)

Definition L (t : timestamp) (st : State) : R :=
  (N_SC st) * (P_redeem_SC t st).

Definition E (t : timestamp) (st : State) : R :=
  (R_ st) - (L t st).

Definition r (t : timestamp) (st : State) : R :=
  (R_ st) / (L t st).

(** ** Equity coin price *)
Definition P_EC (t : timestamp) (st : State) : price :=
  E t st / N_EC st.

(** *** Alternate versions
    The above versions take a timestamp and a state.
    The below versions take a timestamp and other arguments - to calculate the liabilities for a certain [N_SC], when doing proofs for example.
    The below versions are closer to the paper definitions (except [P_redeem_SC_]).
    The definition in the paper is abbreviated in the sense that,
    for example, [P_redeem_SC] is really shorthand for [P_redeem_SC(\sigma, t)], which is equivalent to [P_redeem_SC_(R, N_SC, t)] where [R] and [N_SC] are tuple items in the state [\sigma].
 *)

Definition q_ (t : timestamp) (R_ : amount) (N_SC : amount) : R :=
  R_ / (N_SC * P_target_SC t).

Definition P_redeem_SC_ (t : timestamp) (R_ : amount) (N_SC : amount) : price :=
  if Rlt_dec (q_ t R_ N_SC) r_supcrit then
    R_ / (N_SC * r_supcrit)
  else
    P_target_SC t.

Definition L_ (t : timestamp) (R_ : amount) (N_SC : amount) : R :=
  N_SC * (P_redeem_SC_ t R_ N_SC).

Definition E_ (t : timestamp) (R_ : amount) (N_SC : amount) : R :=
  R_ - (L_ t R_ N_SC).

Definition r_ (t : timestamp) (R_ : amount) (N_SC : amount) : R :=
  R_ / (L_ t R_ N_SC).

(** ** Stability fee *)

Definition stability_fee (t : timestamp) (st : State) : R :=
  if Rgt_dec (r t st) r_safe then
    0
  else
    ((r_safe - r t st) / (r_safe - r_supcrit)) * phi_max.

Definition seconds_per_day : R := 86400.

Definition Phi
  (t : timestamp) (u : User) (st : State) : amount :=
  let elapsed := t - getR u (T st) in
  if Rle_dec elapsed 0 then
    0
  else
    get_B_SC u st *
      (1 - exp (- (stability_fee t st) * (elapsed / seconds_per_day))).

Lemma r_safe_gt_1 :
  1 < r_safe.
Proof.
  pose proof (proj2_sig r_safe_) as H1.
  pose proof (proj2_sig r_crit_) as H2.
  pose proof (proj2_sig r_supcrit_) as H3.
  simpl in H1, H2, H3.
  unfold r_safe.
  lra.
Qed.

Lemma seconds_per_day_pos :
  0 < seconds_per_day.
Proof.
  unfold seconds_per_day; lra.
Qed.

Lemma stability_fee_nonneg :
  forall t st, 0 <= stability_fee t st.
Proof.
  intros t st.
  unfold stability_fee.
  destruct (Rgt_dec (r t st) r_safe) as [Hgt | Hnotgt].
  - lra.
  - unfold Rdiv.
    apply Rmult_le_pos.
    + apply Rmult_le_pos.
      * lra.
      * apply Rlt_le.
        apply Rinv_0_lt_compat.
        exact r_safe_minus_r_supcrit_pos.
    + unfold phi_max.
      destruct (proj2_sig phi_max_) as [Hphi_nonneg Hphi_lt].
      exact Hphi_nonneg.
Qed.

Lemma stability_fee_at_r_supcrit :
  forall t st,
    r t st = r_supcrit ->
    stability_fee t st = phi_max.
Proof.
  intros t st H_r_eq_supcrit.
  unfold stability_fee.
  rewrite H_r_eq_supcrit.
  destruct (Rgt_dec r_supcrit r_safe) as [Hbad | Hnot].
  - pose proof r_safe_gt_supcrit.
    lra.
  - replace ((r_safe - r_supcrit) / (r_safe - r_supcrit)) with 1.
    + ring.
    + field.
      pose proof r_safe_minus_r_supcrit_pos.
      lra.
Qed.

Lemma stability_fee_le_phi_max :
  forall t st,
    r_supcrit <= r t st ->
    stability_fee t st <= phi_max.
Proof.
  intros t st H_r_ge_supcrit.
  unfold stability_fee.
  destruct (Rgt_dec (r t st) r_safe) as [H_r_gt_safe | H_not_gt_safe].
  - (* fee = 0 *)
    unfold phi_max.
    destruct (proj2_sig phi_max_) as [Hphi_nonneg _].
    exact Hphi_nonneg.

  - (* fee = ((r_safe - r)/(r_safe - r_supcrit)) * phi_max *)
    assert (H_rt_le_safe : r t st <= r_safe) by lra.

    assert (Hden_pos : 0 < r_safe - r_supcrit).
    {
      exact r_safe_minus_r_supcrit_pos.
    }

    assert (Hcoeff_le_1 :
      (r_safe - r t st) / (r_safe - r_supcrit) <= 1).
    {
      unfold Rdiv.
      apply Rmult_le_reg_r with (r := r_safe - r_supcrit).
      - exact Hden_pos.
      - rewrite Rmult_1_l.
        rewrite Rmult_assoc.
        rewrite Rinv_l.
        + rewrite Rmult_1_r.
          lra.
        + lra.
    }

    replace phi_max with (1 * phi_max) at 2 by ring.
    apply Rmult_le_compat_r.
    + unfold phi_max.
      destruct (proj2_sig phi_max_) as [Hphi_nonneg _].
      exact Hphi_nonneg.
    + exact Hcoeff_le_1.
Qed.

Lemma one_minus_exp_neg_nonneg :
  forall a, 0 <= a -> 0 <= 1 - exp (- a).
Proof.
  intros a Ha.
  assert (Hexp : exp (- a) <= 1).
  {
    rewrite exp_Ropp.
    apply Rmult_le_reg_l with (r := exp a).
    - apply exp_pos.
    - rewrite Rmult_1_r.
      rewrite Rinv_r.
      + assert (Hge1 : 1 <= exp a).
        {
          specialize (exp_ineq1_le a) as Hineq.
          lra.
        }
        exact Hge1.
      + apply exp_neq_0.
  }
  lra.
Qed.

Lemma Phi_nonneg_if_balance_nonneg :
  forall u t st,
    0 <= get_B_SC u st ->
    0 <= Phi t u st.
Proof.
  intros u t st HB.
  unfold Phi.
  destruct (Rle_dec (t - getR u (T st)) 0).
  - lra.
  - apply Rmult_le_pos.
    + exact HB.
    + replace
        (- stability_fee t st *
          ((t - getR u (T st)) / seconds_per_day))
        with
        (- (stability_fee t st *
          ((t - getR u (T st)) / seconds_per_day)))
        by lra.
      apply one_minus_exp_neg_nonneg.
      apply Rmult_le_pos.
      * apply stability_fee_nonneg.
      * unfold Rdiv.
        apply Rmult_le_pos.
        -- lra.
        -- apply Rlt_le.
           apply Rinv_0_lt_compat.
           exact seconds_per_day_pos.
Qed.

(* fee nonnegativity requires a nonnegative balance *)
Lemma Phi_nonneg :
  forall u t st,
    0 <= get_B_SC u st -> 0 <= Phi t u st.
Proof.
  exact Phi_nonneg_if_balance_nonneg.
Qed.

Lemma Phi_lt_balance :
  forall u t st,
    0 < get_B_SC u st ->
    Phi t u st < get_B_SC u st.
Proof.
  intros u t st HB.
  unfold Phi.
  destruct (Rle_dec (t - getR u (T st)) 0).
  - lra.
  - set (B := get_B_SC u st).
    replace (- stability_fee t st * ((t - getR u (T st)) / seconds_per_day)) with
            (- (stability_fee t st * ((t - getR u (T st)) / seconds_per_day))) by lra.
    set (a := stability_fee t st * ((t - getR u (T st)) / seconds_per_day)).
    replace B with (B * 1) at 2 by lra.
    apply Rmult_lt_compat_l.
    + unfold B; exact HB.
    + assert (Hexp_pos : 0 < exp (- a)).
      {
        apply exp_pos.
      }
      apply Rplus_lt_reg_r with (r := exp (- a)).
      replace (1 - exp (- a) + exp (- a)) with 1 by ring.
      lra.
Qed.

Lemma Phi_le_balance :
  forall u t st,
    0 <= get_B_SC u st ->
    Phi t u st <= get_B_SC u st.
Proof.
  intros u t st HBnonneg.
  destruct (Rlt_dec 0 (get_B_SC u st)) as [HBpos | HBnotpos].
  - left.
    apply Phi_lt_balance.
    exact HBpos.
  - assert (HBzero : get_B_SC u st = 0) by lra.
    unfold Phi.
    rewrite HBzero.
    destruct (Rle_dec (t - getR u (T st)) 0).
    + lra.
    + replace (0 * (1 - exp
          (- stability_fee t st * ((t - getR u (T st)) / seconds_per_day)))) with 0 by ring.
      lra.
Qed.

Lemma Phi_nonpos_if_balance_nonpos :
  forall u t st,
    get_B_SC u st <= 0 ->
    Phi t u st <= 0.
Proof.
  intros u t st HB.
  unfold Phi.
  destruct (Rle_dec (t - getR u (T st)) 0).
  - lra.
  - assert (Hfactor :
      0 <= 1 - exp
        (- stability_fee t st *
          ((t - getR u (T st)) / seconds_per_day))).
    {
      replace
        (- stability_fee t st *
          ((t - getR u (T st)) / seconds_per_day))
        with
        (- (stability_fee t st *
          ((t - getR u (T st)) / seconds_per_day)))
        by lra.
      apply one_minus_exp_neg_nonneg.
      apply Rmult_le_pos.
      - apply stability_fee_nonneg.
      - unfold Rdiv.
        apply Rmult_le_pos.
        + lra.
        + apply Rlt_le.
          apply Rinv_0_lt_compat.
          exact seconds_per_day_pos.
    }
    replace 0 with
      (0 * (1 - exp
        (- stability_fee t st *
          ((t - getR u (T st)) / seconds_per_day))))
      by ring.
    apply Rmult_le_compat_r; assumption.
Qed.

Lemma Phi_lt_supply :
  forall t u st,
    0 < N_SC st ->
    get_B_SC u st <= N_SC st ->
    Phi t u st < N_SC st.
Proof.
  intros t u st HN Hbound.
  destruct (Rlt_dec 0 (get_B_SC u st)) as [HBpos | HBnotpos].
  - pose proof (Phi_lt_balance u t st HBpos) as Hfee.
    lra.
  - assert (HBnonpos : get_B_SC u st <= 0) by lra.
    pose proof
      (Phi_nonpos_if_balance_nonpos u t st HBnonpos)
      as Hfee.
    lra.
Qed.

(** * Operations
    We do not execute the operation if the resulting [N_SC] or [N_EC] becomes zero.
    The guards for those are only added to certain operations, but /technically/ they should be in every operation.

    We distinguish between "primitive" operations and "non-primitive" operations.
    Primitive operations correspond to the state updates in the operation tables in the paper, including implicit holder updates.
    Non-primitive operations correspond to primitive operations wrapped with [trigger_if_critical].
 *)

(** ** (primitive) Redeem SC *)

Definition redeemSC_ (t : timestamp) (x: amount) (u : User) (st : State) : State :=
  if Rle_dec (N_SC st) 0 then st else
  if Rlt_dec x 0 then st else
  if Rlt_dec ((get_B_SC u st) - (Phi t u st) - x) 0 then st else
  if Rle_dec (N_SC st - (Phi t u st) - x) 0 then st else
  let st0 :=
    st
    <| R_   := (R_ st) - x * (P_redeem_SC t st) * (1 - f)            |>
    <| N_SC := (N_SC st - (Phi t u st) - x)                          |>
    <| B_SC := setR u ((get_B_SC u st) - (Phi t u st) - x) (B_SC st) |>
  in
    update_holder u t st0.

(** ** (primitive) Mint SC *)

Definition mintSC_ (t : timestamp) (x : amount) (u : User) (st : State) : State :=
  if Rle_dec x 0 then st else
  let st0 :=
    st
    <| R_   := (R_ st) + x * (1 - f_T)                                                            |>
    <| N_SC := (N_SC st - (Phi t u st) + (x * (1 - f - f_T) / P_mint_SC t))                       |>
    <| B_SC := setR u ((get_B_SC u st) - (Phi t u st) + x * (1 - f - f_T)/ P_mint_SC t ) (B_SC st) |>
    <| T    := setR u t (T st)                                                                     |>
  in
    update_holder u t st0.

(** ** (primitive) Redeem EC *)

Definition redeemEC_ (t : timestamp) (x: amount) (u : User) (st : State) : State :=
  if Rle_dec x 0 then st else
  if Rlt_dec (get_B_EC u st - x) 0 then st else
  if Rle_dec (N_EC st - x) 0 then st else
    st
    <| R_   := (R_ st) - x * (P_EC t st) * (1 - f)                   |>
    <| N_EC := (N_EC st - x)                                         |>
    <| B_EC := setR u ((get_B_EC u st) - x) (B_EC st)                |>.

(** ** (primitive) Mint EC *)

Definition mintEC_ (t : timestamp) (x : amount) (u : User) (st : State) : State :=
  if Rle_dec x 0 then st else
    st
    <| R_   := (R_ st) + x * (1 - f_T)                                           |>
    <| N_EC := (N_EC st + (x * (1 - f - f_T) / P_EC t st))                       |>
    <| B_EC := setR u ((get_B_EC u st) + x * (1 - f - f_T)/ P_EC t st) (B_EC st) |>.

(** * Triggered Redemptions *)

Definition y_rem
  (t : timestamp) (u : User) (st : State) : amount :=
  let num := r_crit * (N_SC st - Phi t u st) * P_target_SC t - R_ st in
  let den := r_crit * P_target_SC t - P_redeem_SC t st * (1 - f)
  in
  if Rle_dec num 0
  then 0
  else num / den.

Fixpoint triggerRedemptions_aux
  (t : timestamp) (hs : UserSet) (st : State) : State :=
  match hs with
  | [] => st
  | h :: hs' =>
      if Rlt_dec (q t st) r_crit then
        let y :=
          Rmin (y_rem t h st)
               (get_B_SC h st - Phi t h st)
        in
        let st' := redeemSC_ t y h st in
        triggerRedemptions_aux t hs' st'
      else
        st
  end.

Definition triggerRedemptions
  (t : timestamp) (st : State) : State :=
  triggerRedemptions_aux t (H st) st.

Definition trigger_if_critical (t : timestamp) (st : State) : State :=
  if Rlt_dec (q t st) r_crit
  then triggerRedemptions t st
  else st.

(** ** Redeem SC *)

Definition redeemSC (t : timestamp) (x : amount) (u : User) (st : State) : State :=
  if Rlt_dec (q t st) r_supcrit then st
  else redeemSC_ t x u st.

(** ** Mint SC *)

Definition mintSC (t : timestamp) (x : amount) (u : User) (st : State) : State :=
  let st0 := trigger_if_critical t st in
  if Rlt_dec (q t st0) r_supcrit then st0
  else mintSC_ t x u st0.

(** ** Mint EC *)

Definition mintEC (t : timestamp) (x : amount) (u : User) (st : State) : State :=
  let st0 := trigger_if_critical t st in
  if Rlt_dec (q t st0) r_supcrit then st0
  else mintEC_ t x u st0.

(** ** Redeem EC *)

Definition redeemEC (t : timestamp) (x : amount) (u : User) (st : State) : State :=
  let st0 := trigger_if_critical t st in
  if Rlt_dec (q t st0) r_supcrit then st0
  else redeemEC_ t x u st0.

(** ** Operations datatype *)

Inductive Operation :=
| MintSC (t : timestamp) (x : amount) (u : User)
| RedeemSC (t : timestamp) (x : amount) (u : User)
| MintEC (t : timestamp) (x : amount) (u : User)
| RedeemEC (t : timestamp) (x : amount) (u : User).

Inductive POperation :=
| MintSC_ (t : timestamp) (x : amount) (u : User)
| RedeemSC_ (t : timestamp) (x : amount) (u : User)
| MintEC_ (t : timestamp) (x : amount) (u : User)
| RedeemEC_ (t : timestamp) (x : amount) (u : User).

Definition exec_op (op : Operation) (st : State) : State :=
  match op with
  | MintSC t x u => mintSC t x u st
  | RedeemSC t x u => redeemSC t x u st
  | MintEC t x u => mintEC t x u st
  | RedeemEC t x u => redeemEC t x u st
  end.

Definition exec_p_op (pop : POperation) (st : State) : State :=
  match pop with
  | MintSC_ t x u => mintSC_ t x u st
  | RedeemSC_ t x u => redeemSC_ t x u st
  | MintEC_ t x u => mintEC_ t x u st
  | RedeemEC_ t x u => redeemEC_ t x u st
  end.

Lemma update_holder_preserves_R :
  forall th u st,
    R_ (update_holder u th st) = R_ st.
Proof.
  intros th u st.
  unfold update_holder, remove_holder, add_holder.
  destruct (in_dec Nat.eq_dec u (H st));
  destruct (Rlt_dec 0 (get_B_SC u st));
  simpl;
  reflexivity.
Qed.

Lemma update_holder_preserves_N_SC :
  forall th u st,
    N_SC (update_holder u th st) = N_SC st.
Proof.
  intros th u st.
  unfold update_holder, remove_holder, add_holder.
  destruct (in_dec Nat.eq_dec u (H st));
  destruct (Rlt_dec 0 (get_B_SC u st));
  simpl;
  reflexivity.
Qed.

Lemma update_holder_preserves_N_EC :
  forall th u st,
    N_EC (update_holder u th st) = N_EC st.
Proof.
  intros th u st.
  unfold update_holder, remove_holder, add_holder.
  destruct (in_dec Nat.eq_dec u (H st));
  destruct (Rlt_dec 0 (get_B_SC u st));
  simpl;
  reflexivity.
Qed.

Lemma update_holder_preserves_q :
  forall tr th u st,
    q tr (update_holder u th st) = q tr st.
Proof.
  intros tr th u st.
  unfold q.
  rewrite (update_holder_preserves_R th u st).
  rewrite (update_holder_preserves_N_SC th u st).
  reflexivity.
Qed.

Lemma update_holder_preserves_P_redeem_SC :
  forall tr th u st,
    P_redeem_SC tr (update_holder u th st) =
    P_redeem_SC tr st.
Proof.
  intros tr th u st.
  unfold P_redeem_SC.
  rewrite (update_holder_preserves_q tr th u st).
  rewrite (update_holder_preserves_R th u st).
  rewrite (update_holder_preserves_N_SC th u st).
  reflexivity.
Qed.

Lemma update_holder_preserves_L :
  forall tr th u st,
    L tr (update_holder u th st) = L tr st.
Proof.
  intros tr th u st.
  unfold L.
  rewrite (update_holder_preserves_N_SC th u st).
  rewrite (update_holder_preserves_P_redeem_SC tr th u st).
  reflexivity.
Qed.

Lemma update_holder_preserves_r :
  forall tr th u st,
    r tr (update_holder u th st) = r tr st.
Proof.
  intros tr th u st.
  unfold r.
  rewrite (update_holder_preserves_R th u st).
  rewrite (update_holder_preserves_L tr th u st).
  reflexivity.
Qed.

Lemma update_holder_preserves_B_SC :
  forall t h u st,
    get_B_SC u (update_holder h t st) =
    get_B_SC u st.
Proof.
  intros t h u st.
  unfold update_holder, add_holder, remove_holder.
  destruct (Rlt_dec 0 (get_B_SC h st));
  destruct (in_dec Nat.eq_dec h (H st));
  simpl; reflexivity.
Qed.

(** * Some helper lemmas *)

Lemma Rmin_mono_l' :
  forall a b c : R,
    a <= b ->
    Rmin a c <= Rmin b c.
Proof.
  intros a b c Hab.
  unfold Rmin.
  destruct (Rle_dec a c);
  destruct (Rle_dec b c);
  lra.
Qed.

(** * Some accounting lemmas *)

Lemma P_target_SC_pos :
  forall t, 0 < P_target_SC t.
Proof.
  intros t.
  unfold P_target_SC, X_PC_BC.
  apply oracle_pos.
Qed.

Lemma P_mint_SC_pos :
  forall t, 0 < P_mint_SC t.
Proof.
  intros t.
  unfold P_mint_SC.
  apply P_target_SC_pos.
Qed.

Lemma q_lt_supcrit_implies_R_div_supcrit_lt_target_liability :
  forall t st,
    0 < N_SC st ->
    q t st < r_supcrit ->
    R_ st / r_supcrit < N_SC st * P_target_SC t.
Proof.
  intros t st H_N_SC_pos H_q_lt.

  pose proof (P_target_SC_pos t) as H_P_pos.
  pose proof r_supcrit_gt_1 as H_s_gt_1.

  set (NP := N_SC st * P_target_SC t) in *.

  assert (H_NP_pos : 0 < NP).
  {
    unfold NP.
    apply Rmult_lt_0_compat; assumption.
  }

  unfold q in H_q_lt.
  fold NP in H_q_lt.

  apply Rmult_lt_reg_r with (r := r_supcrit).
  - lra.
  - replace ((R_ st / r_supcrit) * r_supcrit) with (R_ st).
    2:{ field; lra. }

    apply Rmult_lt_reg_r with (r := / NP).
    + apply Rinv_0_lt_compat.
      exact H_NP_pos.
    + replace (R_ st * / NP) with (R_ st / NP).
      2:{ unfold Rdiv; ring. }

      replace ((NP * r_supcrit) * / NP) with r_supcrit.
      2:{ field; lra. }

      exact H_q_lt.
Qed.

Lemma q_ge_supcrit_implies_target_liability_le_R_div_supcrit :
  forall t st,
    0 < N_SC st ->
    r_supcrit <= q t st ->
    N_SC st * P_target_SC t <= R_ st / r_supcrit.
Proof.
  intros t st H_N_SC_pos H_q_ge.

  pose proof (P_target_SC_pos t) as H_P_pos.
  pose proof r_supcrit_gt_1 as H_s_gt_1.

  set (NP := N_SC st * P_target_SC t) in *.

  assert (H_NP_pos : 0 < NP).
  {
    unfold NP.
    apply Rmult_lt_0_compat; assumption.
  }

  unfold q in H_q_ge.
  fold NP in H_q_ge.

  apply Rmult_le_reg_r with (r := r_supcrit).
  - lra.
  - replace ((R_ st / r_supcrit) * r_supcrit) with (R_ st).
    2:{ field; lra. }

    apply Rmult_le_reg_r with (r := / NP).
    + apply Rinv_0_lt_compat.
      exact H_NP_pos.
    + replace ((NP * r_supcrit) * / NP) with r_supcrit.
      2:{ field; lra. }

      replace (R_ st * / NP) with (R_ st / NP).
      2:{ unfold Rdiv; ring. }

      exact H_q_ge.
Qed.

Lemma L_eq_R_div_r_supcrit_emergency :
  forall t st,
    0 < N_SC st ->
    q t st < r_supcrit ->
    L t st = R_ st / r_supcrit.
Proof.
  intros t st H_N_SC_pos H_q_lt.
  pose proof r_supcrit_gt_1 as H_s_gt_1.

  unfold L, P_redeem_SC.
  destruct (Rlt_dec (q t st) r_supcrit) as [Hbranch | Hbranch].
  - field; nra.
  - lra.
Qed.

Lemma L_eq_min_supply_target_R_div_r_supcrit :
  forall t st,
    0 < N_SC st ->
    L t st = Rmin (N_SC st * P_mint_SC t) (R_ st / r_supcrit).
Proof.
  intros t st H_N_SC_pos.

  destruct (Rlt_dec (q t st) r_supcrit) as [H_q_lt | H_q_not_lt].
  - rewrite (L_eq_R_div_r_supcrit_emergency t st H_N_SC_pos H_q_lt).
    symmetry.
    apply Rmin_right.
    unfold P_mint_SC.
    apply Rlt_le.
    apply q_lt_supcrit_implies_R_div_supcrit_lt_target_liability;
      assumption.

  - unfold L, P_redeem_SC.
    destruct (Rlt_dec (q t st) r_supcrit) as [Hbad | Hbranch].
    + lra.
    + unfold P_mint_SC.
      symmetry.
      apply Rmin_left.
      apply q_ge_supcrit_implies_target_liability_le_R_div_supcrit.
      * exact H_N_SC_pos.
      * lra.
Qed.

Lemma L_le_R_div_r_supcrit :
  forall t st,
    0 < N_SC st ->
    L t st <= R_ st / r_supcrit.
Proof.
  intros t st H_N_SC_pos.
  rewrite (L_eq_min_supply_target_R_div_r_supcrit t st H_N_SC_pos).
  apply Rmin_r.
Qed.

Lemma E_lower_bound :
  forall t st,
    0 < N_SC st ->
    ((r_supcrit - 1) / r_supcrit) * R_ st <= E t st.
Proof.
  intros t st H_N_SC_pos.

  pose proof (L_le_R_div_r_supcrit t st H_N_SC_pos) as H_L_le.
  pose proof r_supcrit_gt_1 as H_s_gt_1.

  unfold E.

  replace (((r_supcrit - 1) / r_supcrit) * R_ st)
    with (R_ st - R_ st / r_supcrit).
  - lra.
  - field; lra.
Qed.

Lemma no_insolvency :
  forall t st,
    0 < R_ st ->
    0 < N_SC st ->
    0 <= E t st.
Proof.
  intros t st H_R_pos H_N_SC_pos.

  pose proof (E_lower_bound t st H_N_SC_pos) as H_E_lb.
  pose proof r_supcrit_gt_1 as H_s_gt_1.

  assert (H_floor_nonneg :
    0 <= ((r_supcrit - 1) / r_supcrit) * R_ st).
  {
    unfold Rdiv.
    apply Rmult_le_pos.
    - apply Rmult_le_pos.
      + lra.
      + apply Rlt_le.
        apply Rinv_0_lt_compat.
        lra.
    - lra.
  }

  lra.
Qed.

Lemma E_pos :
  forall t st,
    0 < R_ st ->
    0 < N_SC st ->
    0 < E t st.
Proof.
  intros t st H_R_pos H_N_SC_pos.

  pose proof (E_lower_bound t st H_N_SC_pos) as H_E_lb.
  pose proof r_supcrit_gt_1 as H_s_gt_1.

  assert (H_floor_pos :
    0 < ((r_supcrit - 1) / r_supcrit) * R_ st).
  {
    unfold Rdiv.
    apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat.
      + lra.
      + apply Rinv_0_lt_compat.
        lra.
    - exact H_R_pos.
  }

  lra.
Qed.

Lemma P_EC_pos :
  forall t st,
    0 < R_ st ->
    0 < N_SC st ->
    0 < N_EC st ->
    0 < P_EC t st.
Proof.
  intros t st H_R_pos H_N_SC_pos H_N_EC_pos.

  unfold P_EC, Rdiv.
  apply Rmult_lt_0_compat.
  - apply E_pos; assumption.
  - apply Rinv_0_lt_compat.
    exact H_N_EC_pos.
Qed.

Lemma L_pos :
  forall t st,
    0 < R_ st ->
    0 < N_SC st ->
    0 < L t st.
Proof.
  intros t st H_R_pos H_N_SC_pos.

  rewrite (L_eq_min_supply_target_R_div_r_supcrit t st H_N_SC_pos).
  unfold Rmin, P_mint_SC.

  pose proof (P_target_SC_pos t) as H_P_pos.
  pose proof r_supcrit_gt_1 as H_s_gt_1.

  destruct (Rle_dec (N_SC st * P_target_SC t) (R_ st / r_supcrit)).
  - apply Rmult_lt_0_compat; assumption.
  - unfold Rdiv.
    apply Rmult_lt_0_compat.
    + exact H_R_pos.
    + apply Rinv_0_lt_compat.
      lra.
Qed.

Lemma r_eq_r_supcrit_emergency :
  forall t st,
    0 < R_ st ->
    0 < N_SC st ->
    q t st < r_supcrit ->
    r t st = r_supcrit.
Proof.
  intros t st H_R_pos H_N_SC_pos H_q_lt.

  unfold r.
  rewrite (L_eq_R_div_r_supcrit_emergency t st H_N_SC_pos H_q_lt).

  pose proof r_supcrit_gt_1 as H_s_gt_1.
  field; lra.
Qed.

Lemma r_ge_r_supcrit :
  forall t st,
    0 < R_ st ->
    0 < N_SC st ->
    r_supcrit <= r t st.
Proof.
  intros t st H_R_pos H_N_SC_pos.

  pose proof (L_le_R_div_r_supcrit t st H_N_SC_pos) as H_L_le.
  pose proof (L_pos t st H_R_pos H_N_SC_pos) as H_L_pos.
  pose proof r_supcrit_gt_1 as H_s_gt_1.

  unfold r.

  apply Rmult_le_reg_r with (r := L t st).
  - exact H_L_pos.
  - replace ((R_ st / L t st) * L t st) with (R_ st).
    2:{ field; lra. }

    assert (H_sL_le_R : r_supcrit * L t st <= R_ st).
    {
      apply Rle_trans with (r2 := r_supcrit * (R_ st / r_supcrit)).
      - apply Rmult_le_compat_l.
        + lra.
        + exact H_L_le.
      - replace (r_supcrit * (R_ st / r_supcrit)) with (R_ st).
        + lra.
        + field; lra.
    }

    lra.
Qed.

(** * Redemption lemmas
    Here we prove some lemmas about invariants of the protocol and triggered redemptions.
 *)

(** ** Stability fee does not decrease the ratio
    We prove that if R is kept constant, and N_SC decreases, the ratio does not decrease.
    So we have "stability fee does not decrease the ratio."
 *)

Lemma L_nondecrease_with_supply :
  forall t st st',
    R_ st' = R_ st ->
    0 < R_ st ->
    0 < N_SC st' ->
    N_SC st' <= N_SC st ->
    L t st' <= L t st.
Proof.
  intros t st st' HR HRpos HN' Hle.
  assert (HN : 0 < N_SC st) by lra.
  rewrite (L_eq_min_supply_target_R_div_r_supcrit t st' HN').
  rewrite (L_eq_min_supply_target_R_div_r_supcrit t st HN).
  rewrite HR.
  apply Rmin_mono_l'.
  apply Rmult_le_compat_r.
  - apply Rlt_le.
    apply P_mint_SC_pos.
  - exact Hle.
Qed.

Lemma supply_decrease_ratio_nondecrease :
  forall t st st',
    R_ st' = R_ st ->
    0 < R_ st ->
    0 < N_SC st' ->
    N_SC st' <= N_SC st ->
    r t st <= r t st'.
Proof.
  intros t st st' HR HRpos HN' Hle.
  assert (HN : 0 < N_SC st) by lra.
  assert (HRpos' : 0 < R_ st') by lra.
  pose proof
    (L_nondecrease_with_supply t st st' HR HRpos HN' Hle)
    as HLle.
  pose proof (L_pos t st HRpos HN) as HLpos.
  pose proof (L_pos t st' HRpos' HN') as HLpos'.
  unfold r, Rdiv.
  rewrite HR.
  apply Rmult_le_compat_l.
  - lra.
  - apply Rinv_le_contravar; lra.
Qed.

Lemma Phi_does_not_decrease_ratio :
  forall t u st,
    0 < R_ st ->
    0 < N_SC st ->
    0 <= get_B_SC u st ->
    get_B_SC u st <= N_SC st ->
    r t st <= r t (st <| N_SC := N_SC st - Phi t u st |>).
Proof.
  intros t u st HR HN HB Hbound.
  apply supply_decrease_ratio_nondecrease.
  - reflexivity.
  - exact HR.
  - simpl.
    pose proof (Phi_lt_supply t u st HN Hbound) as Hfee.
    lra.
  - simpl.
    pose proof
      (Phi_nonneg_if_balance_nonneg u t st HB)
      as Hfee.
    lra.
Qed.


(* A successful balance guard implies nonnegativity of the original balance:
   the balance after the stability fee is B times a positive exponential. *)
Lemma balance_nonneg_of_fee_guard :
  forall t u st,
    0 <= get_B_SC u st - Phi t u st ->
    0 <= get_B_SC u st.
Proof.
  intros t u st Hguard.
  unfold Phi in Hguard.
  destruct (Rle_dec (t - getR u (T st)) 0).
  - lra.
  - pose proof
      (exp_pos
        (- stability_fee t st *
          ((t - getR u (T st)) / seconds_per_day))) as Hexp.
    nra.
Qed.

Lemma SC_redemption_accounting :
  forall t st x u,
    0 < R_ st ->
    0 < N_SC st ->
    0 <= x ->
    0 <= Phi t u st ->
    0 < N_SC st - Phi t u st - x ->
    0 < R_ st - x * P_redeem_SC t st * (1 - f) /\
    R_ st * (N_SC st - Phi t u st - x) <=
      (R_ st - x * P_redeem_SC t st * (1 - f)) * N_SC st.
Proof.
  intros t st x u HR HN Hx Hphi Hafter.
  pose proof (L_pos t st HR HN) as HL.
  pose proof (E_pos t st HR HN) as HE.
  unfold E in HE.
  assert (Hdiscount : 1 - f <= 1).
  {
    destruct (proj2_sig f_) as [Hf0 [Hf1 Htotal]].
    unfold f; lra.
  }
  assert (Hpaid :
    N_SC st * (P_redeem_SC t st * (1 - f)) <= R_ st).
  {
    assert (Hle : L t st * (1 - f) <= L t st).
    {
      replace (L t st) with (L t st * 1) at 2 by ring.
      apply Rmult_le_compat_l; lra.
    }
    unfold L in Hle, HE.
    nra.
  }
  assert (Hpaid_x :
    x * (N_SC st * (P_redeem_SC t st * (1 - f))) <=
      x * R_ st).
  { apply Rmult_le_compat_l; assumption. }
  assert (Hphi_R : 0 <= R_ st * Phi t u st).
  { apply Rmult_le_pos; lra. }
  assert (Hcross :
    R_ st * (N_SC st - Phi t u st - x) <=
      (R_ st - x * P_redeem_SC t st * (1 - f)) * N_SC st)
    by nra.
  split.
  - apply Rmult_lt_reg_r with (r := N_SC st).
    + exact HN.
    + rewrite Rmult_0_l.
      assert (Hleft : 0 < R_ st * (N_SC st - Phi t u st - x)).
      { apply Rmult_lt_0_compat; assumption. }
      lra.
  - exact Hcross.
Qed.

Lemma r_eq_q_nonemergency :
  forall t st,
    r_supcrit <= q t st ->
    r t st = q t st.
Proof.
  intros t st Hq.
  unfold r, L, P_redeem_SC.
  destruct (Rlt_dec (q t st) r_supcrit); [lra | reflexivity].
Qed.

Lemma reserve_per_sc_nondecrease_implies_ratio_nondecrease :
  forall t st st',
    0 < R_ st ->
    0 < N_SC st ->
    0 < R_ st' ->
    0 < N_SC st' ->
    R_ st * N_SC st' <= R_ st' * N_SC st ->
    r t st <= r t st'.
Proof.
  intros t st st' HR HN HR' HN' Hcross.
  pose proof (P_target_SC_pos t) as HP.
  assert (HD : 0 < N_SC st * P_target_SC t).
  { apply Rmult_lt_0_compat; assumption. }
  assert (HD' : 0 < N_SC st' * P_target_SC t).
  { apply Rmult_lt_0_compat; assumption. }
  assert (Hq : q t st <= q t st').
  {
    unfold q.
    apply Rmult_le_reg_r with
      (r := (N_SC st * P_target_SC t) *
              (N_SC st' * P_target_SC t)).
    - apply Rmult_lt_0_compat; assumption.
    - replace
        ((R_ st / (N_SC st * P_target_SC t)) *
          ((N_SC st * P_target_SC t) *
            (N_SC st' * P_target_SC t)))
        with ((R_ st * N_SC st') * P_target_SC t)
        by (field; lra).
      replace
        ((R_ st' / (N_SC st' * P_target_SC t)) *
          ((N_SC st * P_target_SC t) *
            (N_SC st' * P_target_SC t)))
        with ((R_ st' * N_SC st) * P_target_SC t)
        by (field; lra).
      apply Rmult_le_compat_r; lra.
  }
  destruct (Rlt_dec (q t st) r_supcrit) as [Hemergency | Hnormal].
  - rewrite (r_eq_r_supcrit_emergency t st HR HN Hemergency).
    apply r_ge_r_supcrit; assumption.
  - assert (Hq0 : r_supcrit <= q t st) by lra.
    assert (Hq1 : r_supcrit <= q t st') by lra.
    rewrite (r_eq_q_nonemergency t st Hq0).
    rewrite (r_eq_q_nonemergency t st' Hq1).
    exact Hq.
Qed.

Lemma redeemSC__ratio_nondecrease :
  forall t st x u,
    0 < R_ st ->
    0 < N_SC st ->
    0 < x ->
    0 <= get_B_SC u st - Phi t u st - x ->
    0 < N_SC st - Phi t u st - x ->
    r t st <= r t (redeemSC_ t x u st).
Proof.
  intros t st x u HR HN Hx HB Hafter.
  assert (HB0 : 0 <= get_B_SC u st).
  { apply (balance_nonneg_of_fee_guard t u st); lra. }
  pose proof (Phi_nonneg_if_balance_nonneg u t st HB0) as Hphi.
  assert (Hx0 : 0 <= x) by lra.
  destruct (SC_redemption_accounting t st x u HR HN Hx0 Hphi Hafter)
    as [HR' Hcross].
  unfold redeemSC_.
  destruct (Rle_dec (N_SC st) 0) as [HbadN | HgoodN].
  { lra. }
  destruct (Rlt_dec x 0) as [Hbadx | Hgoodx].
  { lra. }
  destruct (Rlt_dec (get_B_SC u st - Phi t u st - x) 0)
    as [HbadB | HgoodB].
  { lra. }
  destruct (Rle_dec (N_SC st - Phi t u st - x) 0)
    as [HbadAfter | HgoodAfter].
  { lra. }
  rewrite update_holder_preserves_r.
  apply reserve_per_sc_nondecrease_implies_ratio_nondecrease;
    simpl; assumption.
Qed.


(** ** Primitive operations preserve positivity of N_EC, N_SC, R *)

Lemma p_op_preserve_N_SC_pos :
  forall st op,
    (forall u, get_B_SC u st <= N_SC st) ->
    N_SC st > 0 /\ N_EC st > 0 /\ R_ st > 0 ->
    N_SC (exec_p_op op st) > 0.
Proof.
  intros st op Hbound [HN [HE HR]].
  destruct op as [t x u | t x u | t x u | t x u];
    cbn [exec_p_op].

  - unfold mintSC_.
    destruct (Rle_dec x 0) as [Hxle | Hxgt].
    + exact HN.
    + rewrite update_holder_preserves_N_SC.
      simpl.
      pose proof (Phi_lt_supply t u st HN (Hbound u)) as Hfee.
      assert (Hnet : 0 < 1 - f - f_T).
      {
        destruct (proj2_sig f_) as [Hf0 [Hf1 Htotal]].
        unfold f, f_T.
        lra.
      }
      assert (Hmint :
        0 < x * (1 - f - f_T) / P_mint_SC t).
      {
        unfold Rdiv.
        apply Rmult_lt_0_compat.
        - apply Rmult_lt_0_compat; lra.
        - apply Rinv_0_lt_compat.
          apply P_mint_SC_pos.
      }
      lra.

  - unfold redeemSC_.
    destruct (Rle_dec (N_SC st) 0) as [Hbad | Hok].
    + exact HN.
    + destruct (Rlt_dec x 0) as [Hxneg | Hxnonneg].
      * exact HN.
      * destruct
          (Rlt_dec (get_B_SC u st - Phi t u st - x) 0)
          as [HBbad | HBok].
        -- exact HN.
        -- destruct
             (Rle_dec (N_SC st - Phi t u st - x) 0)
             as [HNbad | HNok].
           ++ exact HN.
           ++ rewrite update_holder_preserves_N_SC.
              simpl; lra.

  - unfold mintEC_.
    destruct (Rle_dec x 0); simpl; exact HN.

  - unfold redeemEC_.
    destruct (Rle_dec x 0) as [Hxle | Hxgt].
    + exact HN.
    + destruct (Rlt_dec (get_B_EC u st - x) 0) as [HBbad | HBok].
      * exact HN.
      * destruct (Rle_dec (N_EC st - x) 0);
          simpl; exact HN.
Qed.


Lemma p_op_preserve_N_EC_pos :
  forall st op,
    N_SC st > 0 /\ N_EC st > 0 /\ R_ st > 0 ->
    N_EC (exec_p_op op st) > 0.
Proof.
  intros st op [HN [HE HR]].
  destruct op as [t x u | t x u | t x u | t x u];
    cbn [exec_p_op].

  - unfold mintSC_.
    destruct (Rle_dec x 0) as [Hxle | Hxgt].
    + exact HE.
    + rewrite update_holder_preserves_N_EC.
      simpl; exact HE.

  - unfold redeemSC_.
    destruct (Rle_dec (N_SC st) 0) as [Hbad | Hok].
    + exact HE.
    + destruct (Rlt_dec x 0) as [Hxneg | Hxnonneg].
      * exact HE.
      * destruct
          (Rlt_dec (get_B_SC u st - Phi t u st - x) 0)
          as [HBbad | HBok].
        -- exact HE.
        -- destruct
             (Rle_dec (N_SC st - Phi t u st - x) 0)
             as [HNbad | HNok].
           ++ exact HE.
           ++ rewrite update_holder_preserves_N_EC.
              simpl; exact HE.

  - unfold mintEC_.
    destruct (Rle_dec x 0) as [Hxle | Hxgt].
    + exact HE.
    + simpl.
      pose proof (P_EC_pos t st HR HN HE) as HP.
      assert (Hnet : 0 < 1 - f - f_T).
      {
        destruct (proj2_sig f_) as [Hf0 [Hf1 Htotal]].
        unfold f, f_T.
        lra.
      }
      assert (Hmint :
        0 < x * (1 - f - f_T) / P_EC t st).
      {
        unfold Rdiv.
        apply Rmult_lt_0_compat.
        - apply Rmult_lt_0_compat; lra.
        - apply Rinv_0_lt_compat.
          exact HP.
      }
      lra.

  - unfold redeemEC_.
    destruct (Rle_dec x 0) as [Hxle | Hxgt].
    + exact HE.
    + destruct (Rlt_dec (get_B_EC u st - x) 0) as [HBbad | HBok].
      * exact HE.
      * destruct (Rle_dec (N_EC st - x) 0) as [HEbad | HEok];
          simpl; lra.
Qed.


Lemma L_nonneg :
  forall t st,
    0 < R_ st ->
    0 < N_SC st ->
    0 <= L t st.
Proof.
  intros t st HR HN.
  apply Rlt_le.
  apply L_pos; assumption.
Qed.

Lemma p_op_preserve_R_pos :
  forall st op,
    N_SC st > 0 /\ N_EC st > 0 /\ R_ st > 0 ->
    (R_ (exec_p_op op st)) > 0.
Proof.
  intros st op [HN [HE HR]].
  destruct op as [t x u | t x u | t x u | t x u];
    cbn [exec_p_op].
  - unfold mintSC_.
    destruct (Rle_dec x 0) as [Hskip | Hmint].
    + exact HR.
    + rewrite update_holder_preserves_R.
      simpl.
      assert (Hnet : 0 < 1 - f_T).
      {
        destruct (proj2_sig f_T_) as [Hfee0 Hfee1].
        unfold f_T; lra.
      }
      assert (Hdeposit : 0 < x * (1 - f_T)).
      { apply Rmult_lt_0_compat; lra. }
      lra.
  - unfold redeemSC_.
    destruct (Rle_dec (N_SC st) 0) as [HbadN | HgoodN].
    + exact HR.
    + destruct (Rlt_dec x 0) as [Hbadx | Hgoodx].
      * exact HR.
      * destruct (Rlt_dec (get_B_SC u st - Phi t u st - x) 0)
          as [HbadB | HgoodB].
        -- exact HR.
        -- destruct (Rle_dec (N_SC st - Phi t u st - x) 0)
             as [HbadAfter | HgoodAfter].
           ++ exact HR.
           ++ rewrite update_holder_preserves_R.
              simpl.
              assert (HB0 : 0 <= get_B_SC u st).
              { apply (balance_nonneg_of_fee_guard t u st); lra. }
              pose proof (Phi_nonneg_if_balance_nonneg u t st HB0)
                as Hphi.
              assert (Hx : 0 <= x) by lra.
              assert (Hafter : 0 < N_SC st - Phi t u st - x) by lra.
              pose proof
                (SC_redemption_accounting t st x u HR HN Hx Hphi Hafter)
                as [HR' Hcross].
              exact HR'.
  - unfold mintEC_.
    destruct (Rle_dec x 0) as [Hskip | Hmint].
    + exact HR.
    + simpl.
      assert (Hnet : 0 < 1 - f_T).
      {
        destruct (proj2_sig f_T_) as [Hfee0 Hfee1].
        unfold f_T; lra.
      }
      assert (Hdeposit : 0 < x * (1 - f_T)).
      { apply Rmult_lt_0_compat; lra. }
      lra.
  - unfold redeemEC_.
    destruct (Rle_dec x 0) as [Hskip | Hredeem].
    + exact HR.
    + destruct (Rlt_dec (get_B_EC u st - x) 0)
        as [HbadB | HgoodB].
      * exact HR.
      * destruct (Rle_dec (N_EC st - x) 0)
          as [HbadAfter | HgoodAfter].
        -- exact HR.
        -- simpl.
           pose proof (P_EC_pos t st HR HN HE) as HP.
           pose proof (L_pos t st HR HN) as HL.
           assert (Hprice : N_EC st * P_EC t st = E t st).
           { unfold P_EC; field; lra. }
           assert (Hdiscount : 1 - f <= 1).
           {
             destruct (proj2_sig f_) as [Hf0 [Hf1 Htotal]].
             unfold f; lra.
           }
           assert (Hpaid :
             x * P_EC t st * (1 - f) <= x * P_EC t st).
           {
             replace (x * P_EC t st)
               with (x * P_EC t st * 1) at 2 by ring.
             apply Rmult_le_compat_l.
             - apply Rmult_le_pos; lra.
             - exact Hdiscount.
           }
           assert (Hxprice : x * P_EC t st <= E t st).
           {
             rewrite <- Hprice.
             apply Rmult_le_compat_r; lra.
           }
           unfold E in Hxprice.
           lra.
Qed.

Lemma exec_p_op_preserves_pos_R_SC_EC :
  forall op st,
    0 < N_SC st /\ 0 < N_EC st /\ 0 < R_ st ->
    (forall u, get_B_SC u st <= N_SC st) ->
    0 < N_SC (exec_p_op op st) /\
    0 < N_EC (exec_p_op op st) /\
    0 < R_ (exec_p_op op st).
Proof.
  intros op st [HN [HE HR]] Hbound.
  split.
  - apply p_op_preserve_N_SC_pos; [exact Hbound | repeat split; lra].
  - split.
    + apply p_op_preserve_N_EC_pos; repeat split; lra.
    + apply p_op_preserve_R_pos; repeat split; lra.
Qed.

(* SC redemption has its own supply guard and needs no global balance bound. *)
Lemma redeemSC__preserves_pos_R_SC_EC :
  forall t x u st,
    0 < N_SC st /\ 0 < N_EC st /\ 0 < R_ st ->
    0 < N_SC (redeemSC_ t x u st) /\
    0 < N_EC (redeemSC_ t x u st) /\
    0 < R_ (redeemSC_ t x u st).
Proof.
  intros t x u st [HN [HE HR]].
  split.
  - unfold redeemSC_.
    destruct (Rle_dec (N_SC st) 0) as [HbadN | HgoodN].
    + exact HN.
    + destruct (Rlt_dec x 0) as [Hbadx | Hgoodx].
      * exact HN.
      * destruct (Rlt_dec (get_B_SC u st - Phi t u st - x) 0)
          as [HbadB | HgoodB].
        -- exact HN.
        -- destruct (Rle_dec (N_SC st - Phi t u st - x) 0)
             as [HbadAfter | HgoodAfter].
           ++ exact HN.
           ++ rewrite update_holder_preserves_N_SC; simpl; lra.
  - split.
    + change (N_EC (exec_p_op (RedeemSC_ t x u) st) > 0).
      apply p_op_preserve_N_EC_pos; repeat split; lra.
    + change (R_ (exec_p_op (RedeemSC_ t x u) st) > 0).
      apply p_op_preserve_R_pos; repeat split; lra.
Qed.

Lemma triggerRedemptions_aux_preserves_pos_R_SC_EC :
  forall t hs st,
    0 < N_SC st /\ 0 < N_EC st /\ 0 < R_ st ->
    0 < N_SC (triggerRedemptions_aux t hs st) /\
    0 < N_EC (triggerRedemptions_aux t hs st) /\
    0 < R_ (triggerRedemptions_aux t hs st).
Proof.
  intros t hs.
  induction hs as [| h hs IH]; intros st Hpos.
  - exact Hpos.
  - cbn [triggerRedemptions_aux].
    destruct (Rlt_dec (q t st) r_crit) as [Hcritical | Hsafe].
    + apply IH.
      apply redeemSC__preserves_pos_R_SC_EC.
      exact Hpos.
    + exact Hpos.
Qed.

Lemma triggerRedemptions_preserves_pos_R_SC_EC :
  forall t st,
    0 < N_SC st /\ 0 < N_EC st /\ 0 < R_ st ->
    0 < N_SC (triggerRedemptions t st) /\
    0 < N_EC (triggerRedemptions t st) /\
    0 < R_ (triggerRedemptions t st).
Proof.
  intros t st Hpos.
  unfold triggerRedemptions.
  apply triggerRedemptions_aux_preserves_pos_R_SC_EC; exact Hpos.
Qed.

Lemma trigger_if_critical_preserves_pos_R_SC_EC :
  forall t st,
    0 < N_SC st /\ 0 < N_EC st /\ 0 < R_ st ->
    0 < N_SC (trigger_if_critical t st) /\
    0 < N_EC (trigger_if_critical t st) /\
    0 < R_ (trigger_if_critical t st).
Proof.
  intros t st Hpos.
  unfold trigger_if_critical.
  destruct (Rlt_dec (q t st) r_crit).
  - apply triggerRedemptions_preserves_pos_R_SC_EC; exact Hpos.
  - exact Hpos.
Qed.


(** Triggered redemptions *)

Lemma P_redeem_SC_le_P_target_SC :
  forall t st,
    0 < N_SC st ->
    P_redeem_SC t st <= P_target_SC t.
Proof.
  intros t st HN.

  apply Rmult_le_reg_l with (r := N_SC st).
  - exact HN.

  - change (L t st <= N_SC st * P_target_SC t).

    rewrite (L_eq_min_supply_target_R_div_r_supcrit
               t st HN).

    unfold P_mint_SC.
    apply Rmin_l.
Qed.

Lemma y_rem_den_pos :
  forall t st,
    0 < N_SC st ->
    0 <
      r_crit * P_target_SC t
      - P_redeem_SC t st * (1 - f).
Proof.
  intros t st HN.

  pose proof
    (P_redeem_SC_le_P_target_SC t st HN)
    as Hprice.

  pose proof (P_target_SC_pos t) as Htarget.
  pose proof r_crit_gt_1 as Hcrit.

  destruct (proj2_sig f_) as [Hf0 [Hf1 _]].

  assert (Hdiscount : 0 <= 1 - f <= 1).
  {
    unfold f.
    lra.
  }

  destruct Hdiscount as [Hnonneg Hone].

  assert (Hpaid :
    P_redeem_SC t st * (1 - f) <= P_target_SC t).
  {
    eapply Rle_trans
      with (r2 := P_target_SC t * (1 - f)).

    - apply Rmult_le_compat_r; assumption.

    - replace (P_target_SC t)
        with (P_target_SC t * 1) at 2 by ring.

      apply Rmult_le_compat_l; lra.
  }

  assert (Hcritprice :
    P_target_SC t < r_crit * P_target_SC t).
  {
    replace (P_target_SC t)
      with (1 * P_target_SC t) at 1 by ring.

    apply Rmult_lt_compat_r; assumption.
  }

  lra.
Qed.

Definition sum_B_SC (hs : UserSet) (st : State) : amount :=
  fold_right Rplus 0
    (map (fun h => get_B_SC h st) hs).

Definition SC_supply_invariant (hs : UserSet) (st : State) : Prop :=
  N_SC st = sum_B_SC hs st.

Lemma sum_B_SC_cons :
  forall h hs st,
    sum_B_SC (h :: hs) st =
      get_B_SC h st + sum_B_SC hs st.
Proof.
  reflexivity.
Qed.

Lemma head_balance_le_supply :
  forall h hs st,
    SC_supply_invariant (h :: hs) st ->
    (forall u, In u (h :: hs) -> 0 < get_B_SC u st) ->
    get_B_SC h st <= N_SC st.
Proof.
  intros h hs st Hsum Hpos.

  (* a sum of nonnegative balances is nonnegative *)
  assert (Hnonneg :
    forall xs,
      (forall u, In u xs -> 0 <= get_B_SC u st) ->
      0 <= sum_B_SC xs st).
  {
    intro xs.
    induction xs as [|a xs IH]; intro Hxs.

    - unfold sum_B_SC.
      simpl.
      lra.

    - rewrite sum_B_SC_cons.

      assert (Ha : 0 <= get_B_SC a st).
      {
        apply Hxs.
        simpl; auto.
      }

      assert (Hrest :
        forall u, In u xs -> 0 <= get_B_SC u st).
      {
        intros u Hu.
        apply Hxs.
        simpl; auto.
      }

      specialize (IH Hrest).
      lra.
  }

  (* apply it to the tail *)
  assert (Htail : 0 <= sum_B_SC hs st).
  {
    apply Hnonneg.
    intros u Hu.
    apply Rlt_le.
    apply Hpos.
    simpl; right; exact Hu.
  }

  unfold SC_supply_invariant in Hsum.
  rewrite sum_B_SC_cons in Hsum.

  lra.
Qed.

Lemma head_balance_lt_supply :
  forall h h' hs st,
    SC_supply_invariant (h :: h' :: hs) st ->
    (forall u,
        In u (h :: h' :: hs) ->
        0 < get_B_SC u st) ->
    get_B_SC h st < N_SC st.
Proof.
  intros h h' hs st Hsum Hpos.

  assert (Hh' : 0 < get_B_SC h' st).
  {
    apply Hpos.
    simpl; auto.
  }

  assert (Hnonneg :
    forall xs,
      (forall u, In u xs -> 0 <= get_B_SC u st) ->
      0 <= sum_B_SC xs st).
  {
    intros xs.
    induction xs as [|a xs IH]; intros Hxs.
    - unfold sum_B_SC; simpl; lra.
    - rewrite sum_B_SC_cons.

      assert (Ha : 0 <= get_B_SC a st).
      {
        apply Hxs.
        simpl; auto.
      }

      assert (Htail : 0 <= sum_B_SC xs st).
      {
        apply IH.
        intros u Hu.
        apply Hxs.
        simpl; auto.
      }

      lra.
  }

  assert (Htail : 0 <= sum_B_SC hs st).
  {
    apply Hnonneg.
    intros u Hu.
    apply Rlt_le.
    apply Hpos.
    simpl; auto.
  }

  unfold SC_supply_invariant in Hsum.
  rewrite sum_B_SC_cons in Hsum.
  rewrite sum_B_SC_cons in Hsum.
  lra.
Qed.

(* If the current holder can supply the requried stablecoin to be redeemed,
   this one redemption repairs q to r_crit *)

Lemma redeem_y_rem_recovers_q :
  forall t st u,
    0 < R_ st ->
    0 < N_SC st ->
    q t st < r_crit ->
    y_rem t u st <= get_B_SC u st - Phi t u st ->
    0 < N_SC st - Phi t u st - y_rem t u st ->
    r_crit <= q t (redeemSC_ t (y_rem t u st) u st).
Proof.
  intros t st u H_R H_N H_q H_bal H_N_after.

  pose proof (P_target_SC_pos t) as H_Pt.
  pose proof (y_rem_den_pos t st H_N) as H_den.

  destruct
    (Rle_dec
       (r_crit * (N_SC st - Phi t u st) * P_target_SC t - R_ st)
       0)
    as [H_num_le | H_num_gt].

  - (* Phi alone is already enough. *)

    assert (Hy : y_rem t u st = 0).
    {
      unfold y_rem.
      destruct
        (Rle_dec
           (r_crit * (N_SC st - Phi t u st) * P_target_SC t - R_ st)
           0).
      - reflexivity.
      - lra.
    }

    rewrite Hy in H_bal, H_N_after |- *.

    unfold redeemSC_.

    destruct (Rle_dec (N_SC st) 0) as [HNbad | HNok].
    { lra. }

    destruct (Rlt_dec 0 0) as [Hybad | Hyok].
    { lra. }

    destruct
      (Rlt_dec (get_B_SC u st - Phi t u st - 0) 0)
      as [HBbad | HBok].
    { lra. }

    destruct
      (Rle_dec (N_SC st - Phi t u st - 0) 0)
      as [HN'bad | HN'ok].
    { lra. }

    rewrite update_holder_preserves_q.
    simpl.
    unfold q.

    assert (H_D_pos :
      0 < (N_SC st - Phi t u st) * P_target_SC t).
    {
      apply Rmult_lt_0_compat.
      - lra.
      - exact H_Pt.
    }

    apply Rmult_le_reg_r
      with (r := (N_SC st - Phi t u st) * P_target_SC t).
    + exact H_D_pos.
    + simpl.
      field_simplify.
      * lra.
      * lra.

  - (* positive y_rem: redeeming exactly it reaches r_crit. *)

    assert (Hy :
      y_rem t u st =
        (r_crit * (N_SC st - Phi t u st) * P_target_SC t - R_ st) /
        (r_crit * P_target_SC t -
           P_redeem_SC t st * (1 - f))).
    {
      unfold y_rem.
      destruct
        (Rle_dec
           (r_crit * (N_SC st - Phi t u st) * P_target_SC t - R_ st)
           0).
      - lra.
      - reflexivity.
    }

    assert (Hy_pos : 0 < y_rem t u st).
    {
      rewrite Hy.
      unfold Rdiv.
      apply Rmult_lt_0_compat.
      - lra. 
      - apply Rinv_0_lt_compat.
        exact H_den.
    }

    assert (Hy_den :
      y_rem t u st *
        (r_crit * P_target_SC t -
         P_redeem_SC t st * (1 - f))
      =
      r_crit * (N_SC st - Phi t u st) * P_target_SC t
        - R_ st).
    {
      rewrite Hy.
      field.
      lra.
    }

    assert (H_exact :
      R_ st -
        y_rem t u st * P_redeem_SC t st * (1 - f)
      =
      r_crit *
        (N_SC st - Phi t u st - y_rem t u st) *
        P_target_SC t).
    {
      nra.
    }

    unfold redeemSC_.

    destruct (Rle_dec (N_SC st) 0) as [HNbad | HNok].
    { lra. }

    destruct (Rlt_dec (y_rem t u st) 0) as [Hybad | Hyok].
    { lra. }

    destruct
      (Rlt_dec
         (get_B_SC u st - Phi t u st - y_rem t u st) 0)
      as [HBbad | HBok].
    { lra. }

    destruct
      (Rle_dec
         (N_SC st - Phi t u st - y_rem t u st) 0)
      as [HN'bad | HN'ok].
    { lra. }

    rewrite update_holder_preserves_q.
    simpl.
    unfold q.

    assert (H_D_pos :
      0 <
        (N_SC st - Phi t u st - y_rem t u st) *
        P_target_SC t).
    {
      apply Rmult_lt_0_compat.
      - exact H_N_after.
      - exact H_Pt.
    }

    rewrite H_exact.

    simpl.
    field_simplify; lra.    
Qed.

(*
  y_rem < N - \Phi <->
  R > (N - \Phi) * P_redeem_SC (1 - f)
  (N - \Phi) *  P_redeem_SC (1 - f) <= N * P_redeem_SC = L, so < R.
 
*)
Lemma y_rem_lt_remaining_supply :
  forall t u st,
    0 < R_ st ->
    0 < N_SC st ->
    0 < get_B_SC u st ->
    get_B_SC u st <= N_SC st ->
    y_rem t u st < N_SC st - Phi t u st.
Proof.
  intros t u st H_R H_N H_B_pos H_B_le_N.

  assert (H_B_nonneg : 0 <= get_B_SC u st) by lra.
  pose proof
    (Phi_nonneg_if_balance_nonneg u t st H_B_nonneg)
    as H_Phi_nonneg.
  pose proof (Phi_lt_balance u t st H_B_pos) as H_Phi_lt_B.
  assert (H_Phi_lt_N : Phi t u st < N_SC st) by lra.
  pose proof (y_rem_den_pos t st H_N) as H_den.
  pose proof (L_pos t st H_R H_N) as H_L_pos.
  pose proof (L_le_R_div_r_supcrit t st H_N) as H_L_le.
  pose proof r_supcrit_gt_1 as H_s_gt_1.

  assert (H_remaining_pos :
    0 < N_SC st - Phi t u st).
  {
    lra.
  }

  assert (H_Predeem_pos :
    0 < P_redeem_SC t st).
  {
    unfold L in H_L_pos.
    nra.
  }

  assert (H_one_minus_f_nonneg :
    0 <= 1 - f).
  {
    pose proof (proj2_sig f_) as [Hf0 [Hf1 Hf2]].
    unfold f.
    lra.
  }

  assert (H_one_minus_f_le_1 :
    1 - f <= 1).
  {
    pose proof (proj2_sig f_) as [Hf0 [Hf1 Hf2]].
    unfold f.
    lra.
  }

  (* first show L < R *)
  assert (H_R_div_supcrit_lt_R :
    R_ st / r_supcrit < R_ st).
  {
    apply Rmult_lt_reg_r with (r := r_supcrit).
    - lra.
    - replace ((R_ st / r_supcrit) * r_supcrit)
        with (R_ st).
      + replace (R_ st) with (R_ st * 1) at 1 by ring.
        apply Rmult_lt_compat_l; lra.
      + field; lra.
  }

  assert (H_L_lt_R :
    L t st < R_ st).
  {
    lra.
  }

  (* the reserve paid by redeeming all post-fee supply is < R *)
  assert (H_paid_le_L :
    (N_SC st - Phi t u st)
      * P_redeem_SC t st * (1 - f)
    <= L t st).
  {
    unfold L.

    assert (H1 :
      (N_SC st - Phi t u st) * P_redeem_SC t st
      <=
      N_SC st * P_redeem_SC t st).
    {
      apply Rmult_le_compat_r.
      - lra.
      - lra.
    }

    assert (H2 :
      (N_SC st - Phi t u st)
        * P_redeem_SC t st * (1 - f)
      <=
      (N_SC st - Phi t u st)
        * P_redeem_SC t st).
    {
      replace
        ((N_SC st - Phi t u st) * P_redeem_SC t st)
        with
        (((N_SC st - Phi t u st) * P_redeem_SC t st) * 1)
        at 2 by ring.

      apply Rmult_le_compat_l.
      - apply Rmult_le_pos; lra.
      - exact H_one_minus_f_le_1.
    }

    lra.
  }

  assert (H_paid_lt_R :
    (N_SC st - Phi t u st)
      * P_redeem_SC t st * (1 - f)
    < R_ st).
  {
    lra.
  }

  unfold y_rem.

  destruct
    (Rle_dec
      (r_crit * (N_SC st - Phi t u st) * P_target_SC t
       - R_ st)
      0)
    as [H_num_nonpos | H_num_pos].

  - (* y_rem = 0 *)
    lra.

  - (* y_rem = num / den *)
    apply Rmult_lt_reg_r with
      (r :=
        r_crit * P_target_SC t
        - P_redeem_SC t st * (1 - f)).
    + exact H_den.

    + field_simplify; try lra.
Qed.

Lemma redeemSC__preserves_other_balance :
  forall t x h u st,
    u <> h ->
    get_B_SC u (redeemSC_ t x h st) =
    get_B_SC u st.
Proof.
  intros t x h u st Hneq.
  unfold redeemSC_.

  destruct (Rle_dec (N_SC st) 0).
  { reflexivity. }

  destruct (Rlt_dec x 0).
  { reflexivity. }

  destruct
    (Rlt_dec (get_B_SC h st - Phi t h st - x) 0).
  { reflexivity. }

  destruct
    (Rle_dec (N_SC st - Phi t h st - x) 0).
  { reflexivity. }

  rewrite update_holder_preserves_B_SC.
  simpl.

  unfold get_B_SC, getR, setR.
  simpl.
  rewrite UMFacts.add_neq_o by congruence.
  reflexivity.
Qed.


Lemma exhaust_holder_R_pos :
  forall t h h' hs st,
    0 < R_ st ->
    0 < N_SC st ->
    SC_supply_invariant (h :: h' :: hs) st ->
    (forall u,
        In u (h :: h' :: hs) ->
        0 < get_B_SC u st) ->
    0 < R_
      (redeemSC_ t
        (get_B_SC h st - Phi t h st) h st).
Proof.
  intros t h h' hs st HR HN Hsum Hpos.

  assert (HB : 0 < get_B_SC h st).
  {
    apply Hpos.
    simpl; auto.
  }

  pose proof
    (head_balance_lt_supply h h' hs st Hsum Hpos)
    as HB_lt_N.

  pose proof (Phi_lt_balance h t st HB) as HPhi_lt_B.
  assert (HBnonneg : 0 <= get_B_SC h st) by lra.
  pose proof
    (Phi_nonneg_if_balance_nonneg h t st HBnonneg)
    as HPhi_nonneg.

  set (y := get_B_SC h st - Phi t h st).

  assert (Hy : 0 < y).
  {
    unfold y; lra.
  }

  assert (HN_after :
    0 < N_SC st - Phi t h st - y).
  {
    unfold y; lra.
  }

  (* redemption price is positive. *)
  assert (HP : 0 < P_redeem_SC t st).
  {
    pose proof (L_pos t st HR HN) as HL.
    unfold L in HL.

    apply Rmult_lt_reg_l with (r := N_SC st).
    - exact HN.
    - rewrite Rmult_0_r.
      exact HL.
  }

  (* the protocol fee cannot exceed 100%. *)
  assert (Hfee : 0 <= 1 - f <= 1).
  {
    destruct (proj2_sig f_) as [Hf0 [Hf1 _]].
    unfold f.
    lra.
  }

  destruct Hfee as [Hfee_nonneg Hfee_le_1].

  (* the redemption payout cannot exceed liabilities. *)
  assert (Hpaid_le_L :
    y * P_redeem_SC t st * (1 - f) <= L t st).
  {
    assert (Hy_le_N : y <= N_SC st).
    {
      unfold y; lra.
    }

    assert (Hpaid_le_yP :
      y * P_redeem_SC t st * (1 - f)
      <= y * P_redeem_SC t st).
    {
      replace (y * P_redeem_SC t st)
        with (y * P_redeem_SC t st * 1) at 2 by ring.

      apply Rmult_le_compat_l.
      - apply Rmult_le_pos; lra.
      - exact Hfee_le_1.
    }

    assert (HyP_le_L :
      y * P_redeem_SC t st <= L t st).
    {
      unfold L.
      apply Rmult_le_compat_r; lra.
    }

    lra.
  }

  
  pose proof (E_pos t st HR HN) as HE.
  unfold E in HE.

  unfold redeemSC_.

  destruct (Rle_dec (N_SC st) 0);
  destruct (Rlt_dec y 0); 
  destruct
    (Rlt_dec (get_B_SC h st - Phi t h st - y) 0); 
  destruct
    (Rle_dec (N_SC st - Phi t h st - y) 0); try lra.
  unfold y in *.

  rewrite update_holder_preserves_R.
  simpl.

  lra.
Qed.

Lemma exhaust_holder_supply_update :
  forall t h h' hs st,
    SC_supply_invariant (h :: h' :: hs) st ->
    (forall u,
        In u (h :: h' :: hs) ->
        0 < get_B_SC u st) ->
    N_SC
      (redeemSC_ t
        (get_B_SC h st - Phi t h st) h st)
    =
    N_SC st - get_B_SC h st.
Proof.
  intros t h h' hs st Hsum Hpos.

  assert (HB : 0 < get_B_SC h st).
  {
    apply Hpos.
    simpl; auto.
  }

  pose proof
    (head_balance_lt_supply h h' hs st Hsum Hpos)
    as HB_lt_N.

  pose proof
    (Phi_lt_balance h t st HB)
    as HPhi_lt_B.

  assert (HN : 0 < N_SC st) by lra.

  set (y := get_B_SC h st - Phi t h st).

  assert (Hy : 0 < y).
  {
    unfold y.
    lra.
  }

  assert (Hbal :
    get_B_SC h st - Phi t h st - y = 0).
  {
    unfold y.
    ring.
  }

  assert (HN_after :
    0 < N_SC st - Phi t h st - y).
  {
    unfold y.
    lra.
  }

  unfold redeemSC_.

  destruct (Rle_dec (N_SC st) 0); 
  destruct (Rlt_dec y 0);
  destruct
    (Rlt_dec
      (get_B_SC h st - Phi t h st - y) 0);
  destruct
    (Rle_dec (N_SC st - Phi t h st - y) 0); try lra.

  rewrite update_holder_preserves_N_SC.
  simpl.
  unfold y.
  lra.
Qed.


Lemma exhaust_holder_N_SC_pos :
  forall t h h' hs st,
    SC_supply_invariant (h :: h' :: hs) st ->
    (forall u,
        In u (h :: h' :: hs) ->
        0 < get_B_SC u st) ->
    0 < N_SC
      (redeemSC_ t
        (get_B_SC h st - Phi t h st) h st).
Proof.
  intros t h h' hs st Hsum Hpos.

  rewrite
    (exhaust_holder_supply_update
       t h h' hs st Hsum Hpos).

  pose proof
    (head_balance_lt_supply h h' hs st Hsum Hpos)
    as Hlt.

  lra.
Qed.

Lemma exhaust_holder_supply_invariant :
  forall t h h' hs st,
    SC_supply_invariant (h :: h' :: hs) st ->
    NoDup (h :: h' :: hs) ->
    (forall u,
        In u (h :: h' :: hs) ->
        0 < get_B_SC u st) ->
    SC_supply_invariant
      (h' :: hs)
      (redeemSC_ t
        (get_B_SC h st - Phi t h st) h st).
Proof.
  intros t h h' hs st Hsum Hnodup Hpos.

  set (y := get_B_SC h st - Phi t h st).
  set (st' := redeemSC_ t y h st).

  (* exhausting h removes exactly its original balance
     from the total supply *)
  assert (HN :
    N_SC st' = N_SC st - get_B_SC h st).
  {
    unfold st', y.
    eapply exhaust_holder_supply_update.
    apply Hsum.
    apply Hpos.
  }

  (* since the holder list has no duplicates,
     h does not occur in the tail *)
  assert (Hnotin : ~ In h (h' :: hs)).
  {
    inversion Hnodup.
    assumption.
  }

  (* the sum of any list not containing h is unchanged *)
  assert (Htail :
    forall xs,
      ~ In h xs ->
      sum_B_SC xs st' = sum_B_SC xs st).
  {
    induction xs as [|u xs IH]; intro Hnot.

    - reflexivity.

    - assert (Hneq : u <> h).
      {
        intro Heq.
        apply Hnot.
        subst u.
        simpl; auto.
      }

      assert (Hnot' : ~ In h xs).
      {
        intro Hin.
        apply Hnot.
        simpl; auto.
      }

      rewrite !sum_B_SC_cons.

      assert (HB :
        get_B_SC u st' = get_B_SC u st).
      {
        unfold st', y.
        apply redeemSC__preserves_other_balance.
        exact Hneq.
      }

      rewrite HB.
      rewrite (IH Hnot').
      reflexivity.
  }

  specialize (Htail (h' :: hs) Hnotin).

  unfold SC_supply_invariant in *.
  rewrite HN.
  rewrite Htail.
  rewrite sum_B_SC_cons in Hsum.
  lra.
Qed.

Lemma exhaust_holder_preserves_invariants :
  forall t h h' hs st,
    0 < R_ st ->
    0 < N_SC st ->
    SC_supply_invariant (h :: h' :: hs) st ->
    NoDup (h :: h' :: hs) ->
    (forall u,
        In u (h :: h' :: hs) ->
        0 < get_B_SC u st) ->
    let y := get_B_SC h st - Phi t h st in
    let st' := redeemSC_ t y h st in
      0 < R_ st' /\
      0 < N_SC st' /\
      SC_supply_invariant (h' :: hs) st' /\
      NoDup (h' :: hs) /\
      (forall u,
          In u (h' :: hs) ->
          0 < get_B_SC u st').
Proof.
  intros t h h' hs st HR HN Hsum Hnodup Hpos.
  cbn zeta.

  assert (Hnotin : ~ In h (h' :: hs)).
  {
    inversion Hnodup.
    assumption.
  }

  repeat split.

  - (* reserves remain positive *)
    eapply exhaust_holder_R_pos; try auto.
    apply Hsum. apply Hpos.
    
  - (* stablecoin supply remains positive *)
    eapply exhaust_holder_N_SC_pos; try auto.
    apply Hsum. apply Hpos.
  
  - (* the remaining balances sum to the remaining supply *)
    eapply exhaust_holder_supply_invariant; try auto.    
  
  - (* the remaining holder list has no duplicates *)
    inversion Hnodup.
    assumption.

  - (* every remaining holder still has a positive balance *)
    intros u Hu.

    assert (Hneq : u <> h).
    {
      intro Heq.x
      subst u.
      apply Hnotin.
      exact Hu.
    }

    rewrite redeemSC__preserves_other_balance.
    + apply Hpos.
      simpl.
      right.
      exact Hu.
    + exact Hneq.
Qed.

Lemma triggerRedemptions_aux_done :
  forall t hs st,
    r_crit <= q t st ->
    triggerRedemptions_aux t hs st = st.
Proof.
  intros t hs st Hq.
  destruct hs as [|h hs].
  - reflexivity.
  - simpl.
    destruct (Rlt_dec (q t st) r_crit).
    + lra.
    + reflexivity.
Qed.

Lemma triggerRedemptions_aux_recovers_q :
  forall t hs st,
    0 < R_ st ->
    0 < N_SC st ->
    q t st < r_crit ->
    SC_supply_invariant hs st ->
    NoDup hs ->
    (forall u, In u hs -> 0 < get_B_SC u st) ->
    r_crit <= q t (triggerRedemptions_aux t hs st).
Proof.
  intros t hs.
  induction hs as [|h hs IH];
    intros st H_R H_N H_q H_supply H_nodup H_pos.

  - (* no holders but positive supply: impossible. *)
    unfold SC_supply_invariant, sum_B_SC in H_supply.
    simpl in H_supply.
    lra.

  - simpl.
    
    destruct (Rlt_dec (q t st) r_crit) as [H_lt_crit | H_not_lt].
    2: lra.

    assert (H_B_le_N :
      get_B_SC h st <= N_SC st).
    {
      apply head_balance_le_supply with (hs := hs).
      - exact H_supply.
      - exact H_pos.
    }

    assert (H_y_lt_supply :
      y_rem t h st < N_SC st - Phi t h st).
    {
      apply y_rem_lt_remaining_supply.
      - exact H_R.
      - exact H_N.
      - apply H_pos.
        simpl; auto.
      - exact H_B_le_N.
    }

    destruct
      (Rle_dec
         (y_rem t h st)
         (get_B_SC h st - Phi t h st))
      as [H_cover | H_not_cover].

    + (* h can supply the entire required redemption. *)
      rewrite Rmin_left by exact H_cover.

      assert (H_N_after :
        0 <
          N_SC st
          - Phi t h st
          - y_rem t h st).
      {
        lra.
      }

      assert (H_recovered :
        r_crit <=
          q t
            (redeemSC_ t (y_rem t h st) h st)).
      {
        apply redeem_y_rem_recovers_q.
        - exact H_R.
        - exact H_N.
        - exact H_q.
        - exact H_cover.
        - exact H_N_after.
      }

      rewrite triggerRedemptions_aux_done.
      * exact H_recovered.
      * exact H_recovered.

    + (* h cannot cover y_rem: exhaust h and continue. *)
      assert (H_avail_lt :
        get_B_SC h st - Phi t h st
        < y_rem t h st).
      {
        lra.
      }

      rewrite Rmin_right by lra.

      destruct hs as [|h' hs'].

      * (* h was the final holder: contradiction. *)
        unfold SC_supply_invariant, sum_B_SC in H_supply.
        simpl in H_supply.
        simpl.
        lra.

      * (* At least one holder remains. *)
        assert (H_nodup_tail : NoDup (h' :: hs')).
        {
          inversion H_nodup.
          assumption.
        }

        pose proof
          (exhaust_holder_preserves_invariants
             t h h' hs' st
             H_R H_N
             H_supply H_nodup H_pos)
          as H_pres.

        destruct H_pres as
          [H_R'
            [H_N'
              [H_supply' [H_nodup' H_pos']]]].

        set (st' :=
          redeemSC_ t
            (get_B_SC h st - Phi t h st)
            h st) in *.

        destruct (Rlt_dec (q t st') r_crit)
          as [H_still_critical | H_recovered].

        -- (* still below critical: recurse *)
           apply IH.
           ++ exact H_R'.
           ++ exact H_N'.
           ++ exact H_still_critical.
           ++ exact H_supply'.
           ++ exact H_nodup_tail.
           ++ exact H_pos'.

        -- (* this exhaustion already recovered q *)
           rewrite triggerRedemptions_aux_done.
           ++ lra.
           ++ lra.
Qed.

Theorem triggerRedemptions_recovers_q :
  forall t st,
    0 < R_ st ->
    0 < N_SC st ->
    q t st < r_crit ->
    SC_supply_invariant (H st) st ->
    NoDup (H st) ->
    (forall u,
        In u (H st) ->
        0 < get_B_SC u st) ->
    r_crit <= q t (triggerRedemptions t st).
Proof.
  intros t st H_R H_N H_q H_supply H_nodup H_pos.
  unfold triggerRedemptions.
  apply triggerRedemptions_aux_recovers_q; auto.
Qed.

(** * Stability Theorems
    In the paper we adapt some lemmas from Minimal Djed to Tectonic,
    which we formalize here.
 *)

(** TODO: adapt all lemmas from the Tectonic paper *)

Definition SC_balance_invariant (st : State) : Prop :=
  (forall u, 0 <= get_B_SC u st) /\
  (forall hs, NoDup hs -> sum_B_SC hs st <= N_SC st).

Lemma getR_setR_eq :
  forall u x m, getR u (setR u x m) = x.
Proof.
  intros u x m.
  unfold getR, setR.
  rewrite UMFacts.add_eq_o by reflexivity.
  reflexivity.
Qed.

Lemma getR_setR_neq :
  forall u v x m,
    u <> v -> getR u (setR v x m) = getR u m.
Proof.
  intros u v x m Hneq.
  unfold getR, setR.
  rewrite UMFacts.add_neq_o by congruence.
  reflexivity.
Qed.

Lemma sum_B_SC_ext :
  forall hs st st',
    (forall u, In u hs -> get_B_SC u st' = get_B_SC u st) ->
    sum_B_SC hs st' = sum_B_SC hs st.
Proof.
  intros hs.
  induction hs as [| h hs IH]; intros st st' Hsame.
  - reflexivity.
  - rewrite !sum_B_SC_cons.
    rewrite (Hsame h) by (simpl; auto).
    rewrite (IH st st').
    + reflexivity.
    + intros u Hu; apply Hsame; simpl; auto.
Qed.

Lemma sum_B_SC_update_in :
  forall hs st st' u delta,
    NoDup hs ->
    In u hs ->
    get_B_SC u st' = get_B_SC u st + delta ->
    (forall v, v <> u -> get_B_SC v st' = get_B_SC v st) ->
    sum_B_SC hs st' = sum_B_SC hs st + delta.
Proof.
  intros hs.
  induction hs as [| h hs IH]; intros st st' u delta Hnd Hin Hself Hother.
  - inversion Hin.
  - inversion Hnd as [| h0 hs0 Hnot Htail]; subst.
    destruct (Nat.eq_dec h u) as [Heq | Hneq].
    + subst h.
      assert (Htail_eq : sum_B_SC hs st' = sum_B_SC hs st).
      {
        apply sum_B_SC_ext.
        intros v Hv.
        apply Hother.
        intro Heq; subst v; contradiction.
      }
      rewrite !sum_B_SC_cons, Hself, Htail_eq.
      ring.
    + assert (Hin_tail : In u hs).
      { simpl in Hin; destruct Hin as [Heq | Hin]; [congruence | exact Hin]. }
      rewrite !sum_B_SC_cons.
      rewrite (Hother h Hneq).
      rewrite (IH st st' u delta Htail Hin_tail Hself Hother).
      ring.
Qed.

Lemma SC_balance_invariant_bound :
  forall st,
    SC_balance_invariant st ->
    forall u, get_B_SC u st <= N_SC st.
Proof.
  intros st [Hnonneg Hsum] u.
  assert (Hnd : NoDup [u]).
  { constructor; [simpl; tauto | constructor]. }
  pose proof (Hsum [u] Hnd) as Hbound.
  change (get_B_SC u st + 0 <= N_SC st) in Hbound.
  lra.
Qed.

Lemma SC_balance_invariant_update :
  forall st st' u delta,
    SC_balance_invariant st ->
    N_SC st' = N_SC st + delta ->
    get_B_SC u st' = get_B_SC u st + delta ->
    (forall v, v <> u -> get_B_SC v st' = get_B_SC v st) ->
    0 <= get_B_SC u st' ->
    SC_balance_invariant st'.
Proof.
  intros st st' u delta [HB Hsum] HN Hself Hother Hnew.
  split.
  - intros v.
    destruct (Nat.eq_dec v u) as [Heq | Hneq].
    + subst v; exact Hnew.
    + rewrite (Hother v Hneq); apply HB.
  - intros hs Hnd.
    destruct (in_dec Nat.eq_dec u hs) as [Hin | Hnot].
    + rewrite (sum_B_SC_update_in hs st st' u delta Hnd Hin Hself Hother).
      rewrite HN.
      pose proof (Hsum hs Hnd); lra.
    + assert (Hnd_u : NoDup (u :: hs)).
      { constructor; assumption. }
      pose proof (Hsum (u :: hs) Hnd_u) as Hbound.
      rewrite sum_B_SC_cons in Hbound.
      assert (Hsame : sum_B_SC hs st' = sum_B_SC hs st).
      {
        apply sum_B_SC_ext.
        intros v Hv; apply Hother.
        intro Heq; subst v; contradiction.
      }
      rewrite Hsame, HN.
      lra.
Qed.

Lemma SC_balance_invariant_same :
  forall st st',
    SC_balance_invariant st ->
    N_SC st' = N_SC st ->
    (forall u, get_B_SC u st' = get_B_SC u st) ->
    SC_balance_invariant st'.
Proof.
  intros st st' [HB Hsum] HN Hsame.
  split.
  - intros u; rewrite Hsame; apply HB.
  - intros hs Hnd.
    rewrite HN.
    rewrite (sum_B_SC_ext hs st st').
    + apply Hsum; exact Hnd.
    + intros u Hu; apply Hsame.
Qed.

Lemma balance_after_fee_nonneg :
  forall t u st,
    0 <= get_B_SC u st ->
    0 <= get_B_SC u st - Phi t u st.
Proof.
  intros t u st HB.
  unfold Phi.
  destruct (Rle_dec (t - getR u (T st)) 0).
  - lra.
  - pose proof
      (exp_pos
        (- stability_fee t st *
          ((t - getR u (T st)) / seconds_per_day))) as Hexp.
    nra.
Qed.

Lemma mintSC__preserves_SC_balance_invariant :
  forall t x u st,
    SC_balance_invariant st ->
    SC_balance_invariant (mintSC_ t x u st).
Proof.
  intros t x u st Hinv.
  unfold mintSC_.
  destruct (Rle_dec x 0) as [Hskip | Hmint].
  - exact Hinv.
  - apply (SC_balance_invariant_update st _ u
      (- Phi t u st + x * (1 - f - f_T) / P_mint_SC t)).
    + exact Hinv.
    + rewrite update_holder_preserves_N_SC; simpl; ring.
    + rewrite update_holder_preserves_B_SC.
      change
        (getR u (setR u
          (get_B_SC u st - Phi t u st +
            x * (1 - f - f_T) / P_mint_SC t) (B_SC st)) =
          get_B_SC u st +
            (- Phi t u st + x * (1 - f - f_T) / P_mint_SC t)).
      rewrite getR_setR_eq; ring.
    + intros v Hneq.
      rewrite update_holder_preserves_B_SC.
      change
        (getR v (setR u
          (get_B_SC u st - Phi t u st +
            x * (1 - f - f_T) / P_mint_SC t) (B_SC st)) =
          getR v (B_SC st)).
      apply getR_setR_neq; exact Hneq.
    + rewrite update_holder_preserves_B_SC.
      change
        (0 <= getR u (setR u
          (get_B_SC u st - Phi t u st +
            x * (1 - f - f_T) / P_mint_SC t) (B_SC st))).
      rewrite getR_setR_eq.
      destruct Hinv as [HB Hsum].
      pose proof (balance_after_fee_nonneg t u st (HB u)) as Hremaining.
      assert (Hnet : 0 < 1 - f - f_T).
      {
        destruct (proj2_sig f_) as [Hf0 [Hf1 Htotal]].
        unfold f, f_T; lra.
      }
      assert (Hamount : 0 < x * (1 - f - f_T) / P_mint_SC t).
      {
        unfold Rdiv.
        apply Rmult_lt_0_compat.
        - apply Rmult_lt_0_compat; lra.
        - apply Rinv_0_lt_compat; apply P_mint_SC_pos.
      }
      lra.
Qed.

Lemma redeemSC__preserves_SC_balance_invariant :
  forall t x u st,
    SC_balance_invariant st ->
    SC_balance_invariant (redeemSC_ t x u st).
Proof.
  intros t x u st Hinv.
  unfold redeemSC_.
  destruct (Rle_dec (N_SC st) 0) as [HbadN | HgoodN].
  { exact Hinv. }
  destruct (Rlt_dec x 0) as [Hbadx | Hgoodx].
  { exact Hinv. }
  destruct (Rlt_dec (get_B_SC u st - Phi t u st - x) 0)
    as [HbadB | HgoodB].
  { exact Hinv. }
  destruct (Rle_dec (N_SC st - Phi t u st - x) 0)
    as [HbadAfter | HgoodAfter].
  { exact Hinv. }
  apply (SC_balance_invariant_update st _ u (- Phi t u st - x)).
  - exact Hinv.
  - rewrite update_holder_preserves_N_SC; simpl; ring.
  - rewrite update_holder_preserves_B_SC.
    change
      (getR u (setR u (get_B_SC u st - Phi t u st - x) (B_SC st)) =
        get_B_SC u st + (- Phi t u st - x)).
    rewrite getR_setR_eq; ring.
  - intros v Hneq.
    rewrite update_holder_preserves_B_SC.
    change
      (getR v (setR u (get_B_SC u st - Phi t u st - x) (B_SC st)) =
        getR v (B_SC st)).
    apply getR_setR_neq; exact Hneq.
  - rewrite update_holder_preserves_B_SC.
    change
      (0 <= getR u (setR u (get_B_SC u st - Phi t u st - x) (B_SC st))).
    rewrite getR_setR_eq; lra.
Qed.

Lemma exec_p_op_preserves_SC_balance_invariant :
  forall op st,
    SC_balance_invariant st ->
    SC_balance_invariant (exec_p_op op st).
Proof.
  intros op st Hinv.
  destruct op as [t x u | t x u | t x u | t x u];
    cbn [exec_p_op].
  - apply mintSC__preserves_SC_balance_invariant; exact Hinv.
  - apply redeemSC__preserves_SC_balance_invariant; exact Hinv.
  - unfold mintEC_.
    destruct (Rle_dec x 0).
    + exact Hinv.
    + apply (SC_balance_invariant_same st); [exact Hinv | reflexivity |].
      intros v; reflexivity.
  - unfold redeemEC_.
    destruct (Rle_dec x 0).
    { exact Hinv. }
    destruct (Rlt_dec (get_B_EC u st - x) 0).
    { exact Hinv. }
    destruct (Rle_dec (N_EC st - x) 0).
    { exact Hinv. }
    apply (SC_balance_invariant_same st); [exact Hinv | reflexivity |].
    intros v; reflexivity.
Qed.

Lemma triggerRedemptions_aux_preserves_SC_balance_invariant :
  forall t hs st,
    SC_balance_invariant st ->
    SC_balance_invariant (triggerRedemptions_aux t hs st).
Proof.
  intros t hs.
  induction hs as [| h hs IH]; intros st Hinv.
  - exact Hinv.
  - cbn [triggerRedemptions_aux].
    destruct (Rlt_dec (q t st) r_crit).
    + apply IH; apply redeemSC__preserves_SC_balance_invariant; exact Hinv.
    + exact Hinv.
Qed.

Lemma triggerRedemptions_preserves_SC_balance_invariant :
  forall t st,
    SC_balance_invariant st ->
    SC_balance_invariant (triggerRedemptions t st).
Proof.
  intros t st Hinv.
  unfold triggerRedemptions.
  apply triggerRedemptions_aux_preserves_SC_balance_invariant; exact Hinv.
Qed.

Lemma trigger_if_critical_preserves_SC_balance_invariant :
  forall t st,
    SC_balance_invariant st ->
    SC_balance_invariant (trigger_if_critical t st).
Proof.
  intros t st Hinv.
  unfold trigger_if_critical.
  destruct (Rlt_dec (q t st) r_crit).
  - apply triggerRedemptions_preserves_SC_balance_invariant; exact Hinv.
  - exact Hinv.
Qed.

Lemma exec_op_preserves_pos_R_SC_EC :
  forall op st,
    0 < N_SC st /\ 0 < N_EC st /\ 0 < R_ st ->
    SC_balance_invariant st ->
    0 < N_SC (exec_op op st) /\
    0 < N_EC (exec_op op st) /\
    0 < R_ (exec_op op st).
Proof.
  intros op st Hpos Hinv.
  destruct op as [t x u | t x u | t x u | t x u];
    cbn [exec_op].
  - unfold mintSC.
    pose proof (trigger_if_critical_preserves_pos_R_SC_EC t st Hpos) as Hpos'.
    pose proof (trigger_if_critical_preserves_SC_balance_invariant t st Hinv)
      as Hinv'.
    destruct (Rlt_dec (q t (trigger_if_critical t st)) r_supcrit).
    + exact Hpos'.
    + change
        (0 < N_SC (exec_p_op (MintSC_ t x u) (trigger_if_critical t st)) /\
         0 < N_EC (exec_p_op (MintSC_ t x u) (trigger_if_critical t st)) /\
         0 < R_ (exec_p_op (MintSC_ t x u) (trigger_if_critical t st))).
      apply exec_p_op_preserves_pos_R_SC_EC.
      * exact Hpos'.
      * apply SC_balance_invariant_bound; exact Hinv'.
  - unfold redeemSC.
    destruct (Rlt_dec (q t st) r_supcrit).
    + exact Hpos.
    + apply redeemSC__preserves_pos_R_SC_EC; exact Hpos.
  - unfold mintEC.
    pose proof (trigger_if_critical_preserves_pos_R_SC_EC t st Hpos) as Hpos'.
    pose proof (trigger_if_critical_preserves_SC_balance_invariant t st Hinv)
      as Hinv'.
    destruct (Rlt_dec (q t (trigger_if_critical t st)) r_supcrit).
    + exact Hpos'.
    + change
        (0 < N_SC (exec_p_op (MintEC_ t x u) (trigger_if_critical t st)) /\
         0 < N_EC (exec_p_op (MintEC_ t x u) (trigger_if_critical t st)) /\
         0 < R_ (exec_p_op (MintEC_ t x u) (trigger_if_critical t st))).
      apply exec_p_op_preserves_pos_R_SC_EC.
      * exact Hpos'.
      * apply SC_balance_invariant_bound; exact Hinv'.
  - unfold redeemEC.
    pose proof (trigger_if_critical_preserves_pos_R_SC_EC t st Hpos) as Hpos'.
    pose proof (trigger_if_critical_preserves_SC_balance_invariant t st Hinv)
      as Hinv'.
    destruct (Rlt_dec (q t (trigger_if_critical t st)) r_supcrit).
    + exact Hpos'.
    + change
        (0 < N_SC (exec_p_op (RedeemEC_ t x u) (trigger_if_critical t st)) /\
         0 < N_EC (exec_p_op (RedeemEC_ t x u) (trigger_if_critical t st)) /\
         0 < R_ (exec_p_op (RedeemEC_ t x u) (trigger_if_critical t st))).
      apply exec_p_op_preserves_pos_R_SC_EC.
      * exact Hpos'.
      * apply SC_balance_invariant_bound; exact Hinv'.
Qed.

Lemma exec_op_preserves_SC_balance_invariant :
  forall op st,
    SC_balance_invariant st ->
    SC_balance_invariant (exec_op op st).
Proof.
  intros op st Hinv.
  destruct op as [t x u | t x u | t x u | t x u];
    cbn [exec_op].
  - unfold mintSC.
    pose proof (trigger_if_critical_preserves_SC_balance_invariant t st Hinv)
      as Hinv'.
    destruct (Rlt_dec (q t (trigger_if_critical t st)) r_supcrit).
    + exact Hinv'.
    + apply mintSC__preserves_SC_balance_invariant; exact Hinv'.
  - unfold redeemSC.
    destruct (Rlt_dec (q t st) r_supcrit).
    + exact Hinv.
    + apply redeemSC__preserves_SC_balance_invariant; exact Hinv.
  - unfold mintEC.
    pose proof (trigger_if_critical_preserves_SC_balance_invariant t st Hinv)
      as Hinv'.
    destruct (Rlt_dec (q t (trigger_if_critical t st)) r_supcrit).
    + exact Hinv'.
    + change (SC_balance_invariant
        (exec_p_op (MintEC_ t x u) (trigger_if_critical t st))).
      apply exec_p_op_preserves_SC_balance_invariant; exact Hinv'.
  - unfold redeemEC.
    pose proof (trigger_if_critical_preserves_SC_balance_invariant t st Hinv)
      as Hinv'.
    destruct (Rlt_dec (q t (trigger_if_critical t st)) r_supcrit).
    + exact Hinv'.
    + change (SC_balance_invariant
        (exec_p_op (RedeemEC_ t x u) (trigger_if_critical t st))).
      apply exec_p_op_preserves_SC_balance_invariant; exact Hinv'.
Qed.


Lemma init_state_SC_balance :
  forall u,
    get_B_SC u init_state =
      if Nat.eq_dec u init_user then 1 else 0.
Proof.
  intros u.
  change
    (getR u (setR init_user 1 (UserMap.empty amount)) =
      if Nat.eq_dec u init_user then 1 else 0).
  destruct (Nat.eq_dec u init_user) as [Heq | Hneq].
  - subst u; apply getR_setR_eq.
  - rewrite getR_setR_neq by exact Hneq.
    unfold getR.
    rewrite UMFacts.empty_o.
    reflexivity.
Qed.

Lemma sum_B_SC_init_without :
  forall hs,
    ~ In init_user hs ->
    sum_B_SC hs init_state = 0.
Proof.
  intros hs.
  induction hs as [| h hs IH]; intros Hnot.
  - reflexivity.
  - rewrite sum_B_SC_cons, init_state_SC_balance.
    destruct (Nat.eq_dec h init_user) as [Heq | Hneq].
    + subst h; exfalso; apply Hnot; simpl; auto.
    + rewrite IH.
      * ring.
      * intro Hin; apply Hnot; simpl; auto.
Qed.

Lemma sum_B_SC_init_bound :
  forall hs,
    NoDup hs ->
    sum_B_SC hs init_state <= 1.
Proof.
  intros hs.
  induction hs as [| h hs IH]; intros Hnd.
  - change (0 <= 1); lra.
  - inversion Hnd as [| h0 hs0 Hnot Htail]; subst.
    rewrite sum_B_SC_cons, init_state_SC_balance.
    destruct (Nat.eq_dec h init_user) as [Heq | Hneq].
    + subst h.
      rewrite sum_B_SC_init_without by exact Hnot.
      lra.
    + pose proof (IH Htail); lra.
Qed.

Lemma init_state_SC_balance_invariant :
  SC_balance_invariant init_state.
Proof.
  split.
  - intros u; rewrite init_state_SC_balance.
    destruct (Nat.eq_dec u init_user); lra.
  - intros hs Hnd.
    change (sum_B_SC hs init_state <= 1).
    apply sum_B_SC_init_bound; exact Hnd.
Qed.

(* TODO: possibly change *)
Inductive reachable : State -> Prop :=
| reachable_init : reachable init_state
| reachable_step : forall st op,
    reachable st -> reachable (exec_op op st).

Theorem reachable_SC_balance_invariant :
  forall st, reachable st -> SC_balance_invariant st.
Proof.
  intros st Hreach.
  induction Hreach as [| st op Hreach IH].
  - apply init_state_SC_balance_invariant.
  - apply exec_op_preserves_SC_balance_invariant; exact IH.
Qed.

Lemma B_SC_nonneg :
  forall u st, reachable st -> 0 <= get_B_SC u st.
Proof.
  intros u st Hreach.
  destruct (reachable_SC_balance_invariant st Hreach) as [HB Hsum].
  apply HB.
Qed.
