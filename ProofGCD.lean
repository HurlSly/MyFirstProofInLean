import data.nat.basic
open nat

theorem GcdM : ∀ a b : nat, ∃ g : nat, g ∣ a ∧ g ∣ b ∧ ∀ h : nat, h ∣ a ∧ h ∣ b → h ∣ g :=
begin
  intro a,

  -- As we will prove this by Strong Induction, we state the strong induction hypotheses
  have StrongInductionHyp : ∀ n : nat, (∀ a < n, ∀ b : nat, (∃ g : nat, g ∣ a ∧ g ∣ b ∧ ∀ h : nat, h ∣ a ∧ h ∣ b → h ∣ g)) → 
                  (∀ b : nat, ∃ g : nat, g ∣ n ∧ g ∣ b ∧ ∀ h : nat, h ∣ n ∧ h ∣ b → h ∣ g) :=
  begin
    intros n HypRec b,
    cases n with n,
    
    -- n = 0 case
    use b,
    split,
    use 0,
    simp,
    split,
    use 1,
    simp,
    intros h hz,
    cases hz,
    assumption,
    
    -- n > 0 case
    have T := mod_lt b (zero_lt_succ n),
    have Y := HypRec (b % n.succ) T n.succ,
    cases Y with g,
    use g,

    cases Y_h with gbns temp,
    cases temp with gns maxi,

    split,
    assumption,
    split,
    
    have M := mod_add_div' b n.succ,
    cases gbns with r gbns,
    cases gns with s gns,
    rw gbns at M,
    rw gns at M,
    rw ← mul_assoc at M,
    rw mul_comm _ g at M,
    rw mul_assoc at M,
    rw ← mul_add at M,
    use (r + b / (g * s) * s),
    rw eq_comm at M,
    assumption,

    intros h hns,
    cases hns with hns1 hns2,
    have X : h ∣ b % n.succ := (dvd_mod_iff hns1).mpr hns2,
    exact maxi h (and.intro X hns1),
  end,

  exact nat.strong_induction_on a StrongInductionHyp,
end

lemma notnot : ∀ A : Prop, ¬¬(A ∨ ¬A) :=
begin
  intros A H,
  have nA : ¬A :=
  begin
    intro a,
    exact H ((or.intro_left ¬A) a),
  end,

  exact H ((or.intro_right A) nA),
end

theorem ExcludedMiddleDoubleNeg : (∀ P : Prop, P ∨ ¬P) ↔ (∀ P : Prop, ¬¬P → P) :=
begin
  split,
  intros porp P nnp,
  cases porp P with p np,
  assumption,
  exfalso,
  exact nnp np,  
  
  intros porp P,
  exact porp (P ∨ ¬P) (notnot P),
end

theorem AnotA : ∀ A : Prop, ¬(A ↔ ¬A) :=
begin
  intros A H,
  cases H with H1 H2,
  apply notnot A,
  intro AornA,
  cases AornA with a na,
  exact H1 a a,
  exact na (H2 na),
end