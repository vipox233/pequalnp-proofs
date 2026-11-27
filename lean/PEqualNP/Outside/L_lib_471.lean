import Mathlib

namespace PEqualNP.Outside.L_lib_471

private abbrev K := ZMod 2

private def pull {a b : ℕ} (f : Fin a → Fin b) : (Fin b → K) →ₗ[K] (Fin a → K) where
  toFun x := x ∘ f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def idx {n : ℕ} (hn : 0 < n) (t i : ℕ) : Fin n :=
  ⟨(t+i)%n, Nat.mod_lt _ hn⟩

private def win {n k : ℕ} (hn : 0 < n) (t : ℕ) : (Fin n → K) →ₗ[K] (Fin k → K) :=
  pull (fun i => idx hn t i.val)

private def Good {n k : ℕ} (hn : 0 < n) (c : (Fin k → K) →ₗ[K] (Fin n → K)) : Prop :=
  ∀ t, Function.Bijective ((win (k := k) hn t).comp c)

private lemma piRank (n : ℕ) : Module.finrank K (Fin n → K) = n := by simp

private lemma idx_add {n : ℕ} (hn : 0 < n) (t : ℕ) (i : Fin n) :
    idx hn t i.val = (⟨t % n, Nat.mod_lt _ hn⟩ : Fin n) + i := by
  ext
  exact (Nat.mod_add_mod t n i.val).symm

private lemma into_window {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) (t : ℕ) (p : Fin n) :
    (∃ i : Fin k, p = idx hn t i.val) ∨ ∃ i : Fin (n-k), p = idx hn (t+k) i.val := by
  have : NeZero n := ⟨by omega⟩
  let a : Fin n := ⟨t%n, Nat.mod_lt _ hn⟩
  let z := p - a
  have hz : p = idx hn t z.val := by
    rw [idx_add]
    change p = a + (p-a)
    rw [add_comm, sub_add_cancel]
  by_cases h : z.val < k
  · exact Or.inl ⟨⟨z.val,h⟩,hz⟩
  · refine Or.inr ⟨⟨z.val-k, by have := z.isLt; omega⟩,?_⟩
    refine hz.trans ?_
    apply Fin.ext
    change (t+z.val)%n = (t+k+(z.val-k))%n
    congr 1
    omega

private def dot (n : ℕ) : LinearMap.BilinForm K (Fin n → K) := dotProductBilin K K

private lemma dot_nd (n : ℕ) : (dot n).Nondegenerate := by
  constructor
  · intro x hx
    funext i
    have h := hx (Pi.single i 1)
    change dotProduct x (Pi.single i 1) = 0 at h
    simpa [dotProduct_single] using h
  · intro y hy
    funext i
    have h := hy (Pi.single i 1)
    change dotProduct (Pi.single i 1) y = 0 at h
    simpa [single_dotProduct] using h

-- Orthogonality to codewords prescribed on the complementary window
-- detects each coordinate of a dual word that vanishes on its window.
private lemma dual_good {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n)
    {c : (Fin k → K) →ₗ[K] (Fin n → K)} (hc : Good hn c) :
    ∃ b : (Fin (n-k) → K) →ₗ[K] (Fin n → K), Good hn b := by
  let W := LinearMap.range c
  let V := (dot n).orthogonal W
  have hci : Function.Injective c := fun x y h => (hc 0).1
    (congrArg (win (k := k) hn 0) h)
  have hw : Module.finrank K W = k := by
    rw [← (LinearEquiv.ofInjective c hci).finrank_eq, piRank]
  have hv : Module.finrank K V = n-k := by
    rw [LinearMap.BilinForm.finrank_orthogonal (dot_nd n), piRank, hw]
  have H (t : ℕ) : Function.Bijective ((win (k := n-k) hn t).comp V.subtype) := by
    let f := (win (k := n-k) hn t).comp V.subtype
    have hdim : Module.finrank K V = Module.finrank K (Fin (n-k) → K) := by rw [hv, piRank]
    have hi : Function.Injective f := by
      apply (LinearMap.ker_eq_bot).1
      rw [LinearMap.ker_eq_bot']
      intro y hy
      apply Subtype.ext
      funext p
      let s := t + (n-k)
      rcases into_window hn (k := n-k) (by omega) t p with ⟨j,hp⟩ | ⟨j,hp⟩
      · rw [hp]
        exact congrFun hy j
      · have hsz : n-(n-k) = k := by omega
        obtain ⟨x,hx⟩ := (hc s).2 (fun i => (Pi.single p 1 : Fin n → K) (idx hn s i.val))
        have horth := (LinearMap.BilinForm.mem_orthogonal_iff.mp y.property) (c x)
          (LinearMap.mem_range_self c x)
        change dotProduct (c x) y.val = 0 at horth
        suffices hh : dotProduct (c x) y.val = dotProduct (Pi.single p 1) y.val by
          rw [hh, single_dotProduct, one_mul] at horth
          exact horth
        apply Finset.sum_congr rfl
        intro q _
        rcases into_window hn (k := n-k) (by omega) t q with ⟨i,hq⟩ | ⟨i,hq⟩
        · have hz : y.val q = 0 := by rw [hq]; exact congrFun hy i
          simp [hz]
        · rw [hq]
          exact congrArg (· * y.val (idx hn s i.val)) (congrFun hx (Fin.cast hsz i))
    exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩
  let e := LinearEquiv.ofBijective _ (H 0)
  refine ⟨V.subtype.comp e.symm.toLinearMap, fun t => ?_⟩
  exact (H t).comp e.symm.bijective

-- Duplicate the first block of width k. New windows are rotations of
-- that block or copies of cyclic windows in the old word.
private lemma double_good {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    {c : (Fin k → K) →ₗ[K] (Fin n → K)} (hc : Good (by omega) c) :
    ∃ b : (Fin k → K) →ₗ[K] (Fin (n+k) → K), Good (by omega) b := by
  have hn : 0 < n := by omega
  have hnk : 0 < n+k := by omega
  let f (p : Fin (n+k)) : Fin n :=
    if h : p.val < k then ⟨p.val, by omega⟩ else ⟨p.val-k, by have := p.isLt; omega⟩
  refine ⟨(pull f).comp c, ?_⟩
  suffices H : ∀ t < n+k, Function.Bijective ((win (k := k) hnk t).comp ((pull f).comp c)) by
    intro t
    convert H (t%(n+k)) (Nat.mod_lt _ hnk) using 1
    ext x i
    change c x (f (idx hnk t i.val)) = c x (f (idx hnk (t%(n+k)) i.val))
    simp [idx, Nat.mod_add_mod]
  intro t ht
  by_cases h : t < k
  · have : NeZero k := ⟨by omega⟩
    let rot : Fin k → Fin k := fun i => (⟨t,h⟩ : Fin k) + i
    have hr : Function.Bijective (fun (x : Fin k → K) => x ∘ rot) := by
      let e : Equiv.Perm (Fin k) := Equiv.addLeft (⟨t,h⟩ : Fin k)
      exact (Equiv.arrowCongr e.symm (Equiv.refl K)).bijective
    have he (i : Fin k) : f (idx hnk t i.val) = idx hn 0 (rot i).val := by
      have hi := i.isLt
      have hti : t + i.val < n+k := by omega
      simp only [idx, Nat.mod_eq_of_lt hti, Nat.zero_add, f]
      have hev : (rot i).val = (t+i.val)%k := rfl
      have hm : (t+i.val)%k < n := by have := Nat.mod_lt (t+i.val) hk; omega
      simp only [hev, Nat.mod_eq_of_lt hm]
      split <;> rename_i hh
      · apply Fin.ext
        exact (Nat.mod_eq_of_lt hh).symm
      · apply Fin.ext
        exact ((Nat.mod_eq_sub_mod (by omega : k ≤ t+i.val)).trans (Nat.mod_eq_of_lt (by omega))).symm
    convert hr.comp (hc 0) using 1
    ext x i
    exact congrArg (c x) (he i)
  · have he (i : Fin k) : f (idx hnk t i.val) = idx hn (t-k) i.val := by
      have hi := i.isLt
      have hti : t+i.val < 2*(n+k) := by omega
      by_cases hh : t+i.val < n+k
      · simp only [idx, Nat.mod_eq_of_lt hh, f, dite_eq_right (show ¬ t+i.val < k by omega)]
        apply Fin.ext
        change t+i.val-k = (t-k+i.val)%n
        rw [Nat.mod_eq_of_lt (by omega : t-k+i.val < n)]
        omega
      · have hm : (t+i.val)%(n+k) = t+i.val-(n+k) :=
          (Nat.mod_eq_sub_mod (by omega : n+k ≤ t+i.val)).trans (Nat.mod_eq_of_lt (by omega))
        have hm' : (t-k+i.val)%n = t-k+i.val-n :=
          (Nat.mod_eq_sub_mod (by omega : n ≤ t-k+i.val)).trans (Nat.mod_eq_of_lt (by omega))
        simp only [idx, hm, hm', f, dite_eq_left (show t+i.val-(n+k)<k by omega)]
        apply Fin.ext
        change t+i.val-(n+k) = t-k+i.val-n
        omega
    convert hc (t-k) using 1
    ext x i
    exact congrArg (c x) (he i)

private def Feasible (n k : ℕ) : Prop :=
  ∃ (hn : 0 < n) (c : (Fin k → K) →ₗ[K] (Fin n → K)), Good hn c

private lemma exists_good (n : ℕ) : ∀ k, 0 < k → k ≤ n → Feasible n k := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro k hk hkn
    by_cases h : n = k
    · subst n
      have : NeZero k := ⟨by omega⟩
      refine ⟨hk, LinearMap.id, fun t => ?_⟩
      let e : Equiv.Perm (Fin k) := Equiv.addLeft (⟨t%k,Nat.mod_lt _ hk⟩ : Fin k)
      convert (Equiv.arrowCongr e.symm (Equiv.refl K)).bijective using 1
      ext x i
      exact congrArg x (idx_add hk t i)
    · by_cases h₂ : k ≤ n-k
      · obtain ⟨_,c,hc⟩ := ih (n-k) (by omega) k hk h₂
        obtain ⟨b,hb⟩ := double_good hk h₂ hc
        have he : n-k+k = n := by omega
        exact he ▸ (show Feasible (n-k+k) k from ⟨by omega,b,hb⟩)
      · have hl : 0 < n-k := by omega
        have hle : n-k ≤ k := by omega
        obtain ⟨_,c,hc⟩ := ih k (by omega) (n-k) hl hle
        obtain ⟨b,hb⟩ := double_good hl hle hc
        have he : k+(n-k) = n := by omega
        have H : Feasible n (n-k) :=
          (congrArg (fun m => Feasible m (n-k)) he).mp ⟨by omega,b,hb⟩
        obtain ⟨hn,b,hb⟩ := H
        obtain ⟨a,ha⟩ := dual_good hn (Nat.sub_le n k) hb
        have he' : n-(n-k) = k := by omega
        exact he' ▸ (show Feasible n (n-(n-k)) from ⟨hn,a,ha⟩)


private theorem lower_survives {d : Nat} {ρ : Type*}
    (step : (Fin (d+1) → Bool) → ρ → Fin (d+1) → Bool)
    (hstep : ∀ s r (i : Fin d), step s r i.castSucc = s i.succ)
    (rows : List ρ) (x : Fin (d+1) → Bool) (i : Fin (d+1))
    (hi : i.val + rows.length < d+1) :
    rows.foldl step x i = x ⟨i.val + rows.length, hi⟩ := by
  induction rows generalizing x with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.foldl_cons]
    have hj : i.val + rows.length < d := by simp only [List.length_cons] at hi; omega
    rw [ih (step x r) (by omega)]
    exact hstep x r ⟨i.val + rows.length, hj⟩

private theorem lower_necessity (d L : Nat)
    (target : Fin (d+1) → Bool)
    (h : ∃ (taps : Fin L → Fin d → Bool) (bias : Fin L → Bool),
      ∀ x : Fin (d+1) → Bool,
      (List.finRange L).foldl (fun s row =>
        let z : Fin d → Bool := fun j => s j.succ
        let feedback := (List.finRange d).foldl
          (fun acc bit => xor acc (taps row bit && z bit)) (xor (s 0) (bias row))
        Fin.snoc (α := fun _ : Fin (d+1) => Bool) z feedback) x =
          (fun pos => xor (x pos) (target pos))) :
    d+1 ≤ L ∨ (L = 0 ∧ ∀ coord, target coord = false) := by
  rcases h with ⟨taps, bias, h⟩
  by_cases hlong : d+1 ≤ L
  · exact Or.inl hlong
  right
  by_cases hz : L = 0
  · subst L
    refine ⟨rfl, fun coord => ?_⟩
    simpa using congrFun (h (fun _ => false)) coord |>.symm
  let step (s : Fin (d+1) → Bool) (row : Fin L) : Fin (d+1) → Bool :=
    let z : Fin d → Bool := fun j => s j.succ
    let feedback := (List.finRange d).foldl
      (fun acc bit => xor acc (taps row bit && z bit)) (xor (s 0) (bias row))
    Fin.snoc (α := fun _ : Fin (d+1) => Bool) z feedback
  have hs (s : Fin (d+1) → Bool) (r : Fin L) (i : Fin d) :
      step s r i.castSucc = s i.succ := by simp [step]
  have hidx : L < d+1 := by omega
  have he (x : Fin (d+1) → Bool) : x ⟨L, hidx⟩ = xor (x 0) (target 0) := by
    have hw := lower_survives step hs (List.finRange L) x 0 (by simpa using hidx)
    exact (by simpa using hw : (List.finRange L).foldl step x 0 = x ⟨L, hidx⟩).symm.trans
      (congrFun (h x) 0)
  have hf : target 0 = false := by simpa using (he (fun _ => false)).symm
  have hp := he (fun i => decide (i.val = L))
  simp [hf, Ne.symm hz] at hp

private theorem lower_zero (d : Nat) (target : Fin (d+1) → Bool)
    (ht : ∀ coord, target coord = false) :
    ∃ (taps : Fin 0 → Fin d → Bool) (bias : Fin 0 → Bool),
      ∀ x : Fin (d+1) → Bool,
      (List.finRange 0).foldl (fun s row =>
        let z : Fin d → Bool := fun j => s j.succ
        let feedback := (List.finRange d).foldl
          (fun acc bit => xor acc (taps row bit && z bit)) (xor (s 0) (bias row))
        Fin.snoc (α := fun _ : Fin (d+1) => Bool) z feedback) x =
          (fun pos => xor (x pos) (target pos)) := by
  refine ⟨Fin.elim0, Fin.elim0, fun x => ?_⟩
  funext pos
  simp [ht]

private def asField (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem asField_injective : Function.Injective asField := by
  intro a b h
  cases a <;> cases b <;> simp_all [asField]

private def asBool (a : ZMod 2) : Bool := decide (a = 1)

@[local simp] private theorem asField_asBool (a : ZMod 2) : asField (asBool a) = a := by
  fin_cases a
  · change asField (asBool (0 : ZMod 2)) = 0
    decide
  · change asField (asBool (1 : ZMod 2)) = 1
    decide

@[local simp] private theorem asField_xor (a b : Bool) : asField (xor a b) = asField a + asField b := by
  cases a <;> cases b <;> decide

@[local simp] private theorem asField_and (a b : Bool) : asField (a && b) = asField a * asField b := by
  cases a <;> cases b <;> decide

private theorem parity {α : Type*} (l : List α) (a : Bool) (g : α → Bool) :
    asField (l.foldl (fun acc i => xor acc (g i)) a) =
      asField a + (l.map fun i => asField (g i)).sum := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih => simp [ih, add_assoc]

private theorem fold_windows {S : Type*} (step : S → Nat → S) (s : Nat → S)
    (hs : ∀ a, step (s a) a = s (a+1)) (n a : Nat) :
    (List.finRange n).foldl (fun x i => step x (a + i.val)) (s a) = s (a+n) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ, List.foldl_cons, List.foldl_map]
    simp only [Fin.val_zero, Nat.add_zero, hs, Fin.val_succ]
    simpa only [Nat.add_right_comm a, Nat.add_assoc] using ih (a+1)

private theorem row_expansion {d : Nat} (f : (Fin (d+1) → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (h : f (Pi.single 0 1) = 1) (v : Fin (d+1) → ZMod 2) :
    f v = v 0 + ∑ j : Fin d, f (Pi.single j.succ 1) * v j.succ := by
  have hv : (∑ j : Fin (d+1), v j • (Pi.single j (1 : ZMod 2))) = v := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply, mul_ite]
  calc
    f v = f (∑ j : Fin (d+1), v j • Pi.single j 1) := congrArg f hv.symm
    _ = ∑ j : Fin (d+1), v j * f (Pi.single j 1) := by simp
    _ = _ := by simp [Fin.sum_univ_succ, h, mul_comm]

/-- A code with bijective cyclic windows gives all requested affine rows. -/
private theorem rows_of_code {d L : Nat} (hw : d+1 ≤ L)
    (code : (Fin (d+1) → ZMod 2) →ₗ[ZMod 2] (Fin L → ZMod 2))
    (hc : ∀ a, Function.Bijective ((win (k := d+1) (by omega : 0 < L) a).comp code))
    (target : Fin (d+1) → Bool) :
    ∃ (taps : Fin L → Fin d → Bool) (bias : Fin L → Bool),
      ∀ x : Fin (d+1) → Bool,
        (List.finRange L).foldl (fun s row =>
          let z : Fin d → Bool := fun j => s j.succ
          let feedback := (List.finRange d).foldl
            (fun acc bit => xor acc (taps row bit && z bit)) (xor (s 0) (bias row))
          Fin.snoc (α := fun _ : Fin (d+1) => Bool) z feedback) x =
        (fun pos => xor (x pos) (target pos)) := by
  classical
  let hL : 0 < L := by omega
  let E (a : Nat) := LinearEquiv.ofBijective ((win (k := d+1) hL a).comp code) (hc a)
  let coord (p : Nat) : Fin L := ⟨p % L, Nat.mod_lt _ hL⟩
  let f (a : Nat) : (Fin (d+1) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    (LinearMap.proj (coord (a+d+1))).comp (code.comp (E a).symm.toLinearMap)
  have eval (a : Nat) (u : Fin (d+1) → ZMod 2) (i : Fin (d+1)) :
      E a u i = code u (coord (a+i.val)) := rfl
  have feedback (a : Nat) (u : Fin (d+1) → ZMod 2) :
      f a (E a u) = code u (coord (a+d+1)) := by
    change code ((E a).symm (E a u)) _ = _
    rw [LinearEquiv.symm_apply_apply]
  have first (a : Nat) : f a (Pi.single 0 1) = 1 := by
    let u := (E a).symm (Pi.single 0 1)
    have hu : E a u = Pi.single 0 1 := (E a).apply_symm_apply _
    by_contra h
    have hz : f a (Pi.single 0 1) = 0 := by
      generalize f a (Pi.single 0 1) = z at h ⊢
      fin_cases z
      · rfl
      · exact False.elim (h rfl)
    have hv : E (a+1) u = 0 := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [eval, Fin.val_last, Nat.add_right_comm] using (feedback a u).symm.trans (hu ▸ hz)
      · have hj := congrFun hu j.succ
        simp only [eval, Fin.val_succ, Pi.single_apply, Fin.succ_ne_zero, ite_false] at hj
        simpa only [eval, Pi.zero_apply, Fin.val_castSucc, Nat.add_assoc, Nat.add_comm 1] using hj
    have h0 : u = 0 := (E (a+1)).injective (hv.trans ((E (a+1)).map_zero).symm)
    have he := congrFun hu 0
    simp [h0] at he
  let δ (p : Nat) : ZMod 2 :=
    if h : L ≤ p ∧ p-L < d+1 then asField (target ⟨p-L, h.2⟩) else 0
  let biasF (a : Nat) := δ (a+d+1) - f a (fun i => δ (a+i.val))
  let step (s : Fin (d+1) → Bool) (a : Nat) : Fin (d+1) → Bool :=
    let z : Fin d → Bool := fun j => s j.succ
    Fin.snoc (α := fun _ : Fin (d+1) => Bool) z
      ((List.finRange d).foldl (fun acc j => xor acc (asBool (f a (Pi.single j.succ 1)) && z j))
        (xor (s 0) (asBool (biasF a))))
  refine ⟨fun row j => asBool (f row.val (Pi.single j.succ 1)),
    fun row => asBool (biasF row.val), ?_⟩
  intro x
  let u := (E 0).symm (fun i => asField (x i))
  have hx (i : Fin (d+1)) : code u (coord i.val) = asField (x i) := by
    have he := congrFun ((E 0).apply_symm_apply (fun i => asField (x i))) i
    simpa [eval, u] using he
  let seq (p : Nat) := code u (coord p) + δ p
  let s (a : Nat) (i : Fin (d+1)) := asBool (seq (a+i.val))
  have hs (a : Nat) : step (s a) a = s (a+1) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · apply asField_injective
      change asField (Fin.snoc (α := fun _ : Fin (d+1) => Bool) _ _ (Fin.last d)) = _
      rw [Fin.snoc_last, parity]
      simp only [asField_xor, asField_and, asField_asBool, s, Fin.val_zero, Nat.add_zero,
        Fin.val_last, Fin.val_succ]
      have hsum : ((List.finRange d).map fun j => f a (Pi.single j.succ 1) *
          seq (a+(j.val+1))).sum = ∑ j : Fin d, f a (Pi.single j.succ 1) * seq (a+(j.val+1)) := by
        rw [← List.sum_toFinset, List.toFinset_finRange]
        exact List.nodup_finRange d
      rw [hsum, add_right_comm]
      have hf : f a (fun i => seq (a+i.val)) = seq (a+d+1) - biasF a := by
        change f a (E a u + (fun i => δ (a+i.val))) = _
        rw [map_add, feedback]
        dsimp [seq, biasF]
        abel
      have hlinear : f a (fun i => seq (a+i.val)) =
          seq a + ∑ j : Fin d, f a (Pi.single j.succ 1) * seq (a+(j.val+1)) := by
        simpa only [Fin.val_zero, Nat.add_zero, Fin.val_succ] using
          row_expansion (f a) (first a) (fun i => seq (a+i.val))
      rw [← hlinear, hf, sub_add_cancel, show a+d+1 = a+1+d by omega]
    · change Fin.snoc (α := fun _ : Fin (d+1) => Bool) _ _ j.castSucc = _
      rw [Fin.snoc_castSucc]
      change asBool (seq (a+j.succ.val)) = asBool (seq (a+1+j.castSucc.val))
      rw [show a+j.succ.val = a+1+j.castSucc.val by simp; omega]
  have hstart : s 0 = x := by
    funext i
    apply asField_injective
    have hi : i.val < L := lt_of_lt_of_le i.isLt hw
    simp [s, seq, δ, not_le.mpr hi, hx]
  have hend : s L = fun pos => xor (x pos) (target pos) := by
    funext i
    apply asField_injective
    have hδ : δ (L+i.val) = asField (target i) := by
      have hp : L ≤ L+i.val ∧ L+i.val-L < d+1 := by omega
      have hi : (⟨L+i.val-L, hp.2⟩ : Fin (d+1)) = i := by
        apply Fin.ext
        exact Nat.add_sub_cancel_left L i.val
      simp only [δ, dite_eq_left hp, hi]
    have hcoord : coord (L+i.val) = coord i.val := by
      apply Fin.ext
      simp [coord, Nat.add_comm L]
    simp only [s, asField_asBool, seq, asField_xor, hδ, hcoord, hx]
  change (List.finRange L).foldl (fun s i => step s i.val) x = _
  simpa [hstart, hend] using fold_windows step s hs L 0

end PEqualNP.Outside.L_lib_471

theorem PEqualNP.Outside.L_lib_471 :
  ∀ (d L : Nat),
    let w := d+1
    let State := Fin w → Bool
    ∀ target : State,
      (∃ (taps : Fin L → Fin d → Bool) (bias : Fin L → Bool), ∀ x : State,
        (List.finRange L).foldl (fun (s : State) row =>
          let z : Fin d → Bool := fun j => s j.succ
          let feedback := (List.finRange d).foldl
            (fun acc bit => xor acc (taps row bit && z bit)) (xor (s 0) (bias row))
          Fin.snoc (α := fun _ : Fin w => Bool) z feedback) x =
            (fun pos => xor (x pos) (target pos))) ↔
        w ≤ L ∨ (L = 0 ∧ ∀ coord, target coord = false) := by
  intro d L
  dsimp only
  intro target
  constructor
  · exact PEqualNP.Outside.L_lib_471.lower_necessity d L target
  · rintro (hw | ⟨rfl, ht⟩)
    · obtain ⟨_, c, hc⟩ := PEqualNP.Outside.L_lib_471.exists_good L (d+1) (by omega) hw
      exact PEqualNP.Outside.L_lib_471.rows_of_code hw c hc target
    · exact PEqualNP.Outside.L_lib_471.lower_zero d target ht
