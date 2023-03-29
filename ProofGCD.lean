import data.real.basic
import data.nat.prime
open nat

lemma le_exist : ∀ a b : nat, a ≤ b ↔ ∃ c : nat, a + c = b :=
begin
  intros a b,
  split,
  intros ab,
  induction a with n Ind,
  have y := zero_add b,
  use b,
  exact y,

  have nlen := le_of_eq (refl n),
  have x := le_succ_of_le nlen,
  have Z := le_trans x ab,
  have H := Ind Z,
  cases H with h,
  induction h with k,
  rw add_zero at H_h,
  rw H_h,
  exfalso,
  rw H_h at ab,
  rw succ_eq_add_one at ab,
  exact nat.lt_asymm ab ab,
  
  rw add_succ at H_h,
  rw ← succ_add at H_h,
  use k,
  exact H_h,
  
  intro eab,
  cases eab with k,
  revert b,
  induction k with n Ind,
  intros a ap,
  rw add_zero at ap,
  rw ap,
  
  intro b,
  intro anb,
  cases b with m,
  rw add_succ at anb,
  exfalso,
  exact succ_ne_zero (a + n) anb,

  rw add_succ at anb,
  have y := succ.inj anb,
  have z := Ind m y,
  have Z := le_succ m,
  exact le_trans z Z,
end

theorem GcdM : ∀ a b : nat, b ≤ a → ∃ g : nat, g ∣ a ∧ g ∣ b ∧ ∀ h : nat, h ∣ a ∧ h ∣ b → h ∣ g :=
begin
  intro a,

  -- As we will prove this by Strong Induction, we state the strong induction hypotheses
  have Hsr : ∀ n : nat, (∀ a < n, ∀ b : nat, (b ≤ a → ∃ g : nat, g ∣ a ∧ g ∣ b ∧ ∀ h : nat, h ∣ a ∧ h ∣ b → h ∣ g)) → 
                  (∀ b : nat, b ≤ n  → ∃ g : nat, g ∣ n ∧ g ∣ b ∧ ∀ h : nat, h ∣ n ∧ h ∣ b → h ∣ g) :=
  begin
    -- Proof of the strong induction hypothesis

    intro n,
    intro HypRec,
    intro b,
    intro bn,

    --We have to check the cases b = 0 separately, because n - b wouldn't be less than n in this case
    cases b with b,
    
    -- b = 0 case : just use n as g
    use n,
    split,
    use 1,
    simp,
    split,
    use 0,
    simp,
    intro h,
    intro hh,
    cases hh,
    exact hh_left,

    -- b > 0 case
    -- We define c = n - b.succ
    have k := (le_exist b.succ n).1 bn,
    cases k with c K,

    -- Separation of b.succ <= c and c <= b.succ
    have u := le_total b.succ c,
    cases u,

    --Verifiying that c < n so that we can use HypRec
    have c_lt_n : c < n :=
    begin
      rw add_comm at K,
      rw ← add_one at K,
      rw add_comm b 1 at K,
      rw ← add_assoc at K,
      have w := Exists.intro b K,
      have z := (le_exist (c + 1) n).2 w,
      exact z,
    end,

    -- HypRec gives us a g which is gcd(b.succ, c)
    have G := HypRec c c_lt_n b.succ u,
    cases G with g G, -- extraction of g from its existence
    use g,
    
    -- Separation of the 3 conditions of gcd
    cases G with Gc temp,
    cases temp with Gbs Gmaxi,
    
    split,
    
    -- Verification that g ∣ n, using b.succ + c = n, knowing that g ∣ b.succ and g ∣ c
    cases Gc with r,
    rw Gc_h at K,
    cases Gbs with s,
    rw Gbs_h at K,
    rw ← mul_add at K,
    use (s + r),
    rw eq_comm at K,
    exact K,
    
    split,
    
    -- Verification that g ∣ b.succ, trivial
    exact Gbs,
    
    --Verification that g is the max possible.
    intro h,
    intro hdiv,
    cases hdiv with hdivn hdivmsucc,
    cases hdivn with k,
    rw hdivn_h at K,
    cases hdivmsucc with l,
    rw hdivmsucc_h at K,
  
    -- As we cannot use minus as we work in nat, we have to prove that l ≤ k. So we begin by proving h * l ≤ h * k
    have hl_le_hk := (le_exist (h * l) (h * k)).2 (Exists.intro c K),
    
    -- We will use that we can simplify h * l ≤ h * k if h ≠ 0 
    cases h,
    -- For h = 0
    exfalso,
    rw zero_mul at hdivmsucc_h,
    have q := succ_ne_zero b,
    exact q hdivmsucc_h,
    -- For h > 0
    have temp := (mul_le_mul_left (ne_zero.pos (succ h))).1 hl_le_hk,
    have l_le_k := (le_exist l k).1 temp,
    -- Extraction of o = k - l 
    cases l_le_k with o,
    rw eq_comm at l_le_k_h,
    rw l_le_k_h at K,
    rw mul_add at K,
    have q := add_left_cancel K,
    have hsdc : h.succ ∣ c := Exists.intro o q,
    have hsdms := Exists.intro l hdivmsucc_h,
    -- Use of recurrence property
    exact Gmaxi h.succ (and.intro hsdc hsdms),
    
    -- Second case : c <= b.succ. It's essentially the same as the first case, so I do not comment it.
    cases c with C,
    use n,
    split,
    use 1,
    simp,
    
    split,
    
    rw add_zero at K,
    rw K,
    rw add_zero at K,
    intro h,
    intro hn,
    cases hn,
    exact hn_left,
    rw add_succ at K,
    rw add_comm at K,
    rw ← add_succ at K,
    rw add_comm at K,
    have msltn := (le_exist b.succ.succ n).2 (Exists.intro C K),
    have maxi := HypRec b.succ msltn C.succ u,
    cases maxi with g,
    use g,
    cases maxi_h,
    split,
    cases maxi_h_right with ab ac,
    rw succ_add at K,
    rw ← add_succ at K,
    cases ab with k,
    cases maxi_h_left with l,
    rw ab_h at K,
    rw maxi_h_left_h at K,
    rw ← mul_add at K,
    use (l + k),
    rw eq_comm at K,
    assumption,
    split,
    assumption,
    
    intro h,
    intro hnhms,
    cases hnhms,
    cases maxi_h_right with gcs mini,
    rw succ_add at K,
    rw ← add_succ at K,
    cases hnhms_left with r R,
    have hdms := hnhms_right,
    cases hnhms_right with u mshu,
    rw mshu at K,
    rw R at K,
    cases h with hp,
    exfalso,
    rw zero_mul at R,
    rw R at msltn,
    have k := zero_lt_succ b.succ,
    exact le_lt_antisymm msltn k,

    have temp := (le_exist (hp.succ * u) (hp.succ * r)).2 (Exists.intro C.succ K),
    have ztz := (mul_le_mul_left (ne_zero.pos (succ hp))).1 temp,
    have urt := (le_exist u r).1 ztz,
    cases urt with U,
    rw eq_comm at urt_h,
    rw urt_h at K,
    rw mul_add at K,
    have qw := add_left_cancel K,
    have hpc : hp.succ ∣ C.succ := Exists.intro U qw,
    exact mini hp.succ (and.intro hdms hpc),
  end,

  exact nat.strong_induction_on a Hsr,
end
