import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_262_aux

private def b2z (b : Bool) : ZMod 2 :=
  if b then 1 else 0

private lemma b2z_xor (a b : Bool) : b2z (a ^^ b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

private lemma xor_eq_iff_b2z (a b c : Bool) : ((a ^^ b) = c) ↔ b2z a + b2z b = b2z c := by
  cases a <;> cases b <;> cases c <;> decide

private lemma bool_clause_of_xor (a b p s : Bool) (h : (a ^^ b) = s) (ha : a = p) :
    b = (p ^^ s) := by
  subst ha
  cases a <;> cases b <;> cases s <;> simp_all

private lemma bool_not_xor_not (a b : Bool) : (!a ^^ !b) = (a ^^ b) := by
  cases a <;> cases b <;> decide

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

private lemma zmod2_cast_eq_zero_iff_even (k : ℕ) : (k : ZMod 2) = 0 ↔ Even k := by
  rw [ZMod.natCast_eq_zero_iff, even_iff_two_dvd]

private lemma zmod2_cast_eq_one_iff_odd (k : ℕ) : (k : ZMod 2) = 1 ↔ Odd k := by
  rcases Nat.even_or_odd k with hev | hodd
  · have hz : (k : ZMod 2) = 0 := (zmod2_cast_eq_zero_iff_even k).2 hev
    have hnot : ¬ Odd k := Nat.not_odd_iff_even.2 hev
    simp [hz, hnot]
  · obtain ⟨t, rfl⟩ := hodd
    have h1 : ((2 * t + 1 : ℕ) : ZMod 2) = 1 := by
      push_cast
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_mul, zero_add]
    exact ⟨fun _ => ⟨t, rfl⟩, fun _ => h1⟩

private def inc {n m : ℕ} (left right : Fin m → Fin n) (e : Fin m) (v : Fin n) : ZMod 2 :=
  (if left e = v then 1 else 0) + (if right e = v then 1 else 0)

private lemma sum_inc_mul {n m : ℕ} (left right : Fin m → Fin n)
    (e : Fin m) (X : Fin n → ZMod 2) :
    ∑ v : Fin n, inc left right e v * X v = X (left e) + X (right e) := by
  simp only [inc, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

private lemma sum_inc_over_finset {n m : ℕ} (left right : Fin m → Fin n)
    (D : Finset (Fin m)) (v : Fin n) :
    ∑ e ∈ D, inc left right e v =
      (((D.filter (fun e => left e = v)).card +
        (D.filter (fun e => right e = v)).card : ℕ) : ZMod 2) := by
  simp only [inc, Finset.sum_add_distrib, Nat.cast_add, Finset.sum_boole]

private lemma sum_b2z_over_finset {m : ℕ} (sign : Fin m → Bool) (D : Finset (Fin m)) :
    ∑ e ∈ D, b2z (sign e) = ((D.filter (fun e => sign e = true)).card : ZMod 2) := by
  simp only [b2z, Finset.sum_boole]

private lemma backwards_dir (n m : ℕ) (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (w : Fin m → ℕ) (K : ℕ) (D : Finset (Fin m))
    (hodd : Odd ((D.filter (fun e => sign e = true)).card))
    (heven : ∀ v : Fin n, Even ((D.filter (fun e => left e = v)).card +
      (D.filter (fun e => right e = v)).card))
    (hwt : 2 * D.sum w ≤ K) :
    ∃ H : Finset (Fin m × Bool),
      (¬ ∃ x : Fin n → Bool, ∀ p ∈ H, x (left p.1) = p.2 →
        x (right p.1) = (p.2 ^^ sign p.1)) ∧
      H.sum (fun p => w p.1) ≤ K := by
  let H : Finset (Fin m × Bool) := D ×ˢ (Finset.univ : Finset Bool)
  refine ⟨H, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    have hedge : ∀ e ∈ D, b2z (x (left e)) + b2z (x (right e)) = b2z (sign e) := by
      intro e he
      have hp : (e, x (left e)) ∈ H := Finset.mem_product.2 ⟨he, Finset.mem_univ _⟩
      have hr : x (right e) = (x (left e) ^^ sign e) := hx (e, x (left e)) hp rfl
      rw [hr, b2z_xor, ← add_assoc, zmod2_add_self, zero_add]
    have hsum1 : ∑ e ∈ D, (b2z (x (left e)) + b2z (x (right e))) = 1 := by
      rw [Finset.sum_congr rfl hedge, sum_b2z_over_finset]
      exact (zmod2_cast_eq_one_iff_odd _).2 hodd
    have hsum0 : ∑ e ∈ D, (b2z (x (left e)) + b2z (x (right e))) = 0 := by
      calc ∑ e ∈ D, (b2z (x (left e)) + b2z (x (right e)))
          = ∑ e ∈ D, ∑ v : Fin n, inc left right e v * b2z (x v) := by
              refine Finset.sum_congr rfl fun e _ => (sum_inc_mul left right e (fun v => b2z (x v))).symm
        _ = ∑ v : Fin n, (∑ e ∈ D, inc left right e v) * b2z (x v) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun v _ => (Finset.sum_mul D _ _).symm
        _ = ∑ v : Fin n, 0 * b2z (x v) := by
              refine Finset.sum_congr rfl fun v _ => ?_
              rw [sum_inc_over_finset, (zmod2_cast_eq_zero_iff_even _).2 (heven v)]
        _ = 0 := by simp
    rw [hsum0] at hsum1
    exact absurd hsum1 (by decide)
  · have hsum : H.sum (fun p => w p.1) = 2 * D.sum w := by
      rw [Finset.sum_product]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, smul_eq_mul]
      rw [← Finset.mul_sum]
    omega

private lemma gf2_fredholm {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (a : ι → Fin n → ZMod 2) (s : ι → ZMod 2)
    (hunsat : ¬ ∃ X : Fin n → ZMod 2, ∀ i : ι, ∑ v : Fin n, a i v * X v = s i) :
    ∃ f : ι → ZMod 2,
      (∀ v : Fin n, ∑ i : ι, f i * a i v = 0) ∧
      ∑ i : ι, f i * s i = 1 := by
  let eval : (Fin n → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) :=
    { toFun := fun X i => ∑ v : Fin n, a i v * X v
      map_add' := fun X Y => by
        funext i
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c X => by
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        ring }
  let R : Submodule (ZMod 2) (ι → ZMod 2) := LinearMap.range eval
  have hsR : s ∉ R := by
    rintro ⟨X, hX⟩
    exact hunsat ⟨X, fun i => congrFun hX i⟩
  let q₀ : (ι → ZMod 2) ⧸ R := R.mkQ s
  have hq0 : q₀ ≠ 0 := by
    intro h0
    apply hsR
    exact (Submodule.Quotient.mk_eq_zero R).1 h0
  let S1 : Submodule (ZMod 2) ((ι → ZMod 2) ⧸ R) := Submodule.span (ZMod 2) {q₀}
  have hS1_mem : ∀ x ∈ S1, x = 0 ∨ x = q₀ := by
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · left; exact zero_smul _ _
    · right; exact one_smul _ _
  have h2q0 : q₀ + q₀ = 0 := by
    calc q₀ + q₀ = (1 : ZMod 2) • q₀ + (1 : ZMod 2) • q₀ := by simp
      _ = ((1 : ZMod 2) + 1) • q₀ := (add_smul 1 1 q₀).symm
      _ = (0 : ZMod 2) • q₀ := by congr 1
      _ = 0 := zero_smul _ _
  classical
  let φ : ↥S1 →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => if x.1 = 0 then 0 else 1
      map_add' := fun x y => by
        rcases hS1_mem x.1 x.2 with hx | hx <;> rcases hS1_mem y.1 y.2 with hy | hy
        · simp [hx, hy]
        · simp [hx, hy, hq0]
        · simp [hx, hy, hq0]
        · have hxy : (x + y).1 = 0 := by
            change x.1 + y.1 = 0
            rw [hx, hy, h2q0]
          simp only [hxy, hx, hy, hq0, ↓reduceIte]
          decide
      map_smul' := fun c x => by
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · simp
        · simp }
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl S1
  let L : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    (φ.comp (Submodule.projectionOnto S1 W hW)).comp R.mkQ
  have hL_eval : ∀ X : Fin n → ZMod 2, L (eval X) = 0 := by
    intro X
    have hmk : R.mkQ (eval X) = 0 :=
      (Submodule.Quotient.mk_eq_zero R).2 ⟨X, rfl⟩
    change φ (Submodule.projectionOnto S1 W hW (R.mkQ (eval X))) = 0
    rw [hmk, map_zero, map_zero]
  have hL_s : L s = 1 := by
    have hq0S : q₀ ∈ S1 := Submodule.subset_span (Set.mem_singleton q₀)
    have hproj : Submodule.projectionOnto S1 W hW q₀ = ⟨q₀, hq0S⟩ :=
      Submodule.projectionOnto_apply_left hW ⟨q₀, hq0S⟩
    change φ (Submodule.projectionOnto S1 W hW q₀) = 1
    rw [hproj]
    simp [φ, hq0]
  have hL_expand : ∀ y : ι → ZMod 2, L y = ∑ i : ι, L (Pi.single i 1) * y i := by
    intro y
    have hy : y = ∑ i : ι, y i • Pi.single i (1 : ZMod 2) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hy]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  refine ⟨fun i => L (Pi.single i 1), ?_, ?_⟩
  · intro v
    have h1 := hL_eval (Pi.single v 1)
    rw [hL_expand] at h1
    have hev : ∀ i : ι, eval (Pi.single v 1) i = a i v := by
      intro i
      change ∑ u : Fin n, a i u * (Pi.single v (1 : ZMod 2) : Fin n → ZMod 2) u = a i v
      simp [Pi.single_apply]
    simpa [hev] using h1
  · rw [← hL_expand s, hL_s]

private lemma single_deletion_unsat {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (H : Finset (Fin m × Bool))
    (hincomp : ¬ ∃ x : Fin n → Bool, ∀ p ∈ H, x (left p.1) = p.2 →
      x (right p.1) = (p.2 ^^ sign p.1))
    (p₀ : Fin m × Bool) :
    ¬ ∃ X : Fin n → ZMod 2, ∀ p ∈ H.erase p₀,
      ∑ v : Fin n, inc left right p.1 v * X v = b2z (sign p.1) := by
  rintro ⟨X, hX⟩
  let x0 : Fin n → Bool := fun v => decide (X v = 1)
  let x1 : Fin n → Bool := fun v => !(x0 v)
  have hb2z0 : ∀ v : Fin n, b2z (x0 v) = X v := by
    intro v
    rcases zmod2_eq_zero_or_one (X v) with h0 | h1
    · simp [b2z, x0, h0]
    · simp [b2z, x0, h1]
  have hxor0 : ∀ p ∈ H.erase p₀, (x0 (left p.1) ^^ x0 (right p.1)) = sign p.1 := by
    intro p hp
    have h1 := hX p hp
    rw [sum_inc_mul] at h1
    rw [xor_eq_iff_b2z, hb2z0, hb2z0]
    exact h1
  have hxor1 : ∀ p ∈ H.erase p₀, (x1 (left p.1) ^^ x1 (right p.1)) = sign p.1 := by
    intro p hp
    simp only [x1, bool_not_xor_not]
    exact hxor0 p hp
  by_cases h0 : x0 (left p₀.1) = p₀.2
  · apply hincomp
    refine ⟨x1, fun p hp hpl => ?_⟩
    by_cases hpp : p = p₀
    · subst hpp
      have hne : x1 (left p.1) ≠ p.2 := by
        simp only [x1, h0]
        cases p.2 <;> decide
      exact absurd hpl hne
    · exact bool_clause_of_xor _ _ _ _ (hxor1 p (Finset.mem_erase.2 ⟨hpp, hp⟩)) hpl
  · apply hincomp
    refine ⟨x0, fun p hp hpl => ?_⟩
    by_cases hpp : p = p₀
    · subst hpp
      exact absurd hpl h0
    · exact bool_clause_of_xor _ _ _ _ (hxor0 p (Finset.mem_erase.2 ⟨hpp, hp⟩)) hpl

private lemma full_unsat {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (H : Finset (Fin m × Bool))
    (hincomp : ¬ ∃ x : Fin n → Bool, ∀ p ∈ H, x (left p.1) = p.2 →
      x (right p.1) = (p.2 ^^ sign p.1)) :
    ¬ ∃ X : Fin n → ZMod 2, ∀ p ∈ H,
      ∑ v : Fin n, inc left right p.1 v * X v = b2z (sign p.1) := by
  rintro ⟨X, hX⟩
  let x0 : Fin n → Bool := fun v => decide (X v = 1)
  have hb2z0 : ∀ v : Fin n, b2z (x0 v) = X v := by
    intro v
    rcases zmod2_eq_zero_or_one (X v) with h0 | h1
    · simp [b2z, x0, h0]
    · simp [b2z, x0, h1]
  apply hincomp
  refine ⟨x0, fun p hp hpl => ?_⟩
  have h1 := hX p hp
  rw [sum_inc_mul] at h1
  have hxor : (x0 (left p.1) ^^ x0 (right p.1)) = sign p.1 := by
    rw [xor_eq_iff_b2z, hb2z0, hb2z0]
    exact h1
  exact bool_clause_of_xor _ _ _ _ hxor hpl

private lemma forwards_dir (n m : ℕ) (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (w : Fin m → ℕ) (K : ℕ) (H : Finset (Fin m × Bool))
    (hincomp : ¬ ∃ x : Fin n → Bool, ∀ p ∈ H, x (left p.1) = p.2 →
      x (right p.1) = (p.2 ^^ sign p.1))
    (hwt : H.sum (fun p => w p.1) ≤ K) :
    ∃ D : Finset (Fin m),
      (Odd ((D.filter (fun e => sign e = true)).card) ∧
        ∀ v : Fin n, Even ((D.filter (fun e => left e = v)).card +
          (D.filter (fun e => right e = v)).card)) ∧
      2 * D.sum w ≤ K := by
  classical
  let ι := { p : Fin m × Bool // p ∈ H }
  let isKer : (ι → ZMod 2) → Prop :=
    fun f => ∀ v : Fin n, ∑ q : ι, f q * inc left right q.1.1 v = 0
  let isOdd : (ι → ZMod 2) → Prop :=
    fun f => ∑ q : ι, f q * b2z (sign q.1.1) = 1
  let oddSet : Finset (ι → ZMod 2) := Finset.univ.filter (fun f => isKer f ∧ isOdd f)
  have hnonempty : oddSet.Nonempty := by
    have hunsat : ¬ ∃ X : Fin n → ZMod 2, ∀ q : ι,
        ∑ v : Fin n, inc left right q.1.1 v * X v = b2z (sign q.1.1) := by
      rintro ⟨X, hX⟩
      exact full_unsat left right sign H hincomp ⟨X, fun p hp => hX ⟨p, hp⟩⟩
    obtain ⟨f, hfk, hfo⟩ := gf2_fredholm (fun q : ι => inc left right q.1.1)
      (fun q : ι => b2z (sign q.1.1)) hunsat
    exact ⟨f, Finset.mem_filter.2 ⟨Finset.mem_univ _, hfk, hfo⟩⟩
  have hzero_avoid : ∀ q₀ : ι, ∃ f ∈ oddSet, f q₀ = 0 := by
    intro q₀
    let ι' := { p : Fin m × Bool // p ∈ H.erase q₀.1 }
    have hunsat : ¬ ∃ X : Fin n → ZMod 2, ∀ q : ι',
        ∑ v : Fin n, inc left right q.1.1 v * X v = b2z (sign q.1.1) := by
      rintro ⟨X, hX⟩
      exact single_deletion_unsat left right sign H hincomp q₀.1 ⟨X, fun p hp => hX ⟨p, hp⟩⟩
    obtain ⟨g, hgk, hgo⟩ := gf2_fredholm (fun q : ι' => inc left right q.1.1)
      (fun q : ι' => b2z (sign q.1.1)) hunsat
    let f : ι → ZMod 2 := fun q =>
      if hne : q.1 ≠ q₀.1 then g ⟨q.1, Finset.mem_erase.2 ⟨hne, q.2⟩⟩ else 0
    have hsum_eq : ∀ (h : Fin m × Bool → ZMod 2),
        ∑ q : ι, f q * h q.1 = ∑ q : ι', g q * h q.1 := by
      intro h
      calc ∑ q : ι, f q * h q.1
          = ∑ q ∈ Finset.univ.erase q₀, f q * h q.1 := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q₀)]
              simp [f]
        _ = ∑ q : ι', g q * h q.1 := by
              refine Finset.sum_bij
                (fun q hq => ⟨q.1, Finset.mem_erase.2 ⟨fun heq => (Finset.mem_erase.1 hq).1 (Subtype.ext heq), q.2⟩⟩)
                ?_ ?_ ?_ ?_
              · intro _ _
                exact Finset.mem_univ _
              · intro a _ b _ hab
                exact Subtype.ext (congrArg (Subtype.val : ι' → Fin m × Bool) hab)
              · intro b _
                have hbH : b.1 ∈ H := (Finset.mem_erase.1 b.2).2
                have hbne : b.1 ≠ q₀.1 := (Finset.mem_erase.1 b.2).1
                refine ⟨⟨b.1, hbH⟩, Finset.mem_erase.2 ⟨fun h => hbne (congrArg Subtype.val h),
                  Finset.mem_univ _⟩, ?_⟩
                exact Subtype.ext rfl
              · intro a ha
                have hne' : a ≠ q₀ := (Finset.mem_erase.1 ha).1
                simp [f, hne']
    refine ⟨f, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
    · intro v
      rw [hsum_eq (fun p => inc left right p.1 v)]
      exact hgk v
    · change ∑ q : ι, f q * b2z (sign q.1.1) = 1
      rw [hsum_eq (fun p => b2z (sign p.1))]
      exact hgo
    · simp [f]
  have hhalf : ∀ q : ι, 2 * (oddSet.filter (fun f => f q = 1)).card ≤ oddSet.card := by
    intro q
    obtain ⟨fq, hfq_mem, hfq0⟩ := hzero_avoid q
    by_cases hflip : ∃ d : ι → ZMod 2,
        isKer d ∧ (∑ r : ι, d r * b2z (sign r.1.1) = 0) ∧ d q = 1
    · obtain ⟨d, hdKer, hdEven, hdq⟩ := hflip
      have hcard_eq : (oddSet.filter (fun f => f q = 1)).card =
          (oddSet.filter (fun f => f q = 0)).card := by
        refine Finset.card_bij (fun f _ => f + d) ?_ ?_ ?_
        · intro f hf
          rw [Finset.mem_filter] at hf ⊢
          obtain ⟨hfo, hfq1⟩ := hf
          rw [Finset.mem_filter] at hfo ⊢
          refine ⟨⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
          · intro v
            simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
            rw [hfo.2.1 v, hdKer v, add_zero]
          · simp only [isOdd, Pi.add_apply, add_mul, Finset.sum_add_distrib]
            rw [hfo.2.2, hdEven, add_zero]
          · simp only [Pi.add_apply, hfq1, hdq]
            decide
        · intro f1 _ f2 _ h
          exact add_right_cancel h
        · intro g hg
          rw [Finset.mem_filter] at hg
          obtain ⟨hgo, hgq0⟩ := hg
          rw [Finset.mem_filter] at hgo
          refine ⟨g + d, ?_, ?_⟩
          · rw [Finset.mem_filter]
            refine ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
            · intro v
              simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
              rw [hgo.2.1 v, hdKer v, add_zero]
            · simp only [isOdd, Pi.add_apply, add_mul, Finset.sum_add_distrib]
              rw [hgo.2.2, hdEven, add_zero]
            · simp only [Pi.add_apply, hgq0, hdq, zero_add]
          · funext r
            simp only [Pi.add_apply, add_assoc, zmod2_add_self, add_zero]
      have hcompl : oddSet.filter (fun f => f q = 0) = oddSet.filter (fun f => ¬ f q = 1) := by
        ext f
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hf, h0⟩
          exact ⟨hf, by rw [h0]; decide⟩
        · rintro ⟨hf, hne⟩
          rcases zmod2_eq_zero_or_one (f q) with h0 | h1
          · exact ⟨hf, h0⟩
          · exact absurd h1 hne
      have htot := Finset.card_filter_add_card_filter_not (s := oddSet) (p := fun f => f q = 1)
      rw [← hcompl, ← hcard_eq] at htot
      omega
    · have hempty : oddSet.filter (fun f => f q = 1) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro f hf
        rw [Finset.mem_filter] at hf
        obtain ⟨hfo, hfq1⟩ := hf
        rw [Finset.mem_filter] at hfo hfq_mem
        apply hflip
        refine ⟨f + fq, ?_, ?_, ?_⟩
        · intro v
          simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
          rw [hfo.2.1 v, hfq_mem.2.1 v, add_zero]
        · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
          rw [hfo.2.2, hfq_mem.2.2]
          decide
        · simp only [Pi.add_apply, hfq1, hfq0, add_zero]
      rw [hempty, Finset.card_empty]
      omega
  let wt : (ι → ZMod 2) → ℕ := fun f => ∑ q : ι, if f q = 1 then w q.1.1 else 0
  have hsum_wt : 2 * ∑ f ∈ oddSet, wt f ≤ oddSet.card * K := by
    have h1 : 2 * ∑ f ∈ oddSet, wt f =
        ∑ q : ι, w q.1.1 * (2 * (oddSet.filter (fun f => f q = 1)).card) := by
      simp only [wt]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      ring
    have h2 : ∑ q : ι, w q.1.1 * (2 * (oddSet.filter (fun f => f q = 1)).card) ≤
        ∑ q : ι, w q.1.1 * oddSet.card := by
      refine Finset.sum_le_sum fun q _ => Nat.mul_le_mul_left _ (hhalf q)
    have h3 : ∑ q : ι, w q.1.1 * oddSet.card = oddSet.card * H.sum (fun p => w p.1) := by
      rw [← Finset.sum_mul, mul_comm]
      congr 1
      simpa [ι] using Finset.sum_attach H (fun p => w p.1)
    have h4 : oddSet.card * H.sum (fun p => w p.1) ≤ oddSet.card * K :=
      Nat.mul_le_mul_left _ hwt
    omega
  have hex_f : ∃ f ∈ oddSet, 2 * wt f ≤ K := by
    by_contra hall
    push Not at hall
    have hgt : oddSet.card * (K + 1) ≤ 2 * ∑ f ∈ oddSet, wt f := by
      rw [Finset.mul_sum]
      calc oddSet.card * (K + 1) = ∑ _f ∈ oddSet, (K + 1) := by
              rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ f ∈ oddSet, 2 * wt f := by
              refine Finset.sum_le_sum fun f hf => Nat.succ_le_of_lt (hall f hf)
    have hpos : 0 < oddSet.card := Finset.card_pos.2 hnonempty
    nlinarith
  obtain ⟨f, hf_mem, hf_wt⟩ := hex_f
  rw [Finset.mem_filter] at hf_mem
  obtain ⟨_, hfKer, hfOdd⟩ := hf_mem
  let d : Fin m → ZMod 2 := fun e =>
    (if h0 : (e, false) ∈ H then f ⟨(e, false), h0⟩ else 0) +
    (if h1 : (e, true) ∈ H then f ⟨(e, true), h1⟩ else 0)
  let D : Finset (Fin m) := Finset.univ.filter (fun e => d e = 1)
  have hproj : ∀ g : Fin m → ZMod 2, ∑ e ∈ D, g e = ∑ q : ι, f q * g q.1.1 := by
    intro g
    have hD : ∑ e ∈ D, g e = ∑ e : Fin m, d e * g e := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun e _ => ?_
      rcases zmod2_eq_zero_or_one (d e) with h0 | h1
      · simp [h0]
      · simp [h1]
    rw [hD]
    have hsplit : ∑ e : Fin m, d e * g e =
        ∑ p : Fin m × Bool, if hp : p ∈ H then f ⟨p, hp⟩ * g p.1 else 0 := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp only [d, add_mul, Fintype.sum_bool]
      rw [add_comm]
      congr 1
      · by_cases h0 : (e, false) ∈ H <;> simp
      · by_cases h1 : (e, true) ∈ H <;> simp
    rw [hsplit]
    have hattach : ∑ p : Fin m × Bool, (if hp : p ∈ H then f ⟨p, hp⟩ * g p.1 else 0) =
        ∑ p ∈ H.attach, f p * g p.1.1 := by
      calc ∑ p : Fin m × Bool, (if hp : p ∈ H then f ⟨p, hp⟩ * g p.1 else 0)
          = ∑ p ∈ Finset.univ.filter (fun p : Fin m × Bool => p ∈ H),
              if hp : p ∈ H then f ⟨p, hp⟩ * g p.1 else 0 := by
                rw [Finset.sum_filter]
                refine Finset.sum_congr rfl fun p _ => by by_cases hp : p ∈ H <;> simp [hp]
        _ = ∑ p ∈ H, if hp : p ∈ H then f ⟨p, hp⟩ * g p.1 else 0 := by
              congr 1
              ext p
              simp
        _ = ∑ p ∈ H.attach, f p * g p.1.1 := by
              rw [← Finset.sum_attach H (fun p => if hp : p ∈ H then f ⟨p, hp⟩ * g p.1 else 0)]
              refine Finset.sum_congr rfl fun p _ => by simp [p.2]
    rw [hattach]
    rfl
  refine ⟨D, ⟨?_, ?_⟩, ?_⟩
  · rw [← zmod2_cast_eq_one_iff_odd, ← sum_b2z_over_finset, hproj]
    exact hfOdd
  · intro v
    rw [← zmod2_cast_eq_zero_iff_even, ← sum_inc_over_finset, hproj]
    exact hfKer v
  · have hDle : D.sum w ≤ wt f := by
      have h1 : D.sum w = ∑ e : Fin m, if d e = 1 then w e else 0 := by
        rw [Finset.sum_filter]
      have h2 : ∑ e : Fin m, (if d e = 1 then w e else 0) ≤
          ∑ e : Fin m,
            ((if h0 : (e, false) ∈ H then (if f ⟨(e, false), h0⟩ = 1 then w e else 0) else 0) +
             (if h1 : (e, true) ∈ H then (if f ⟨(e, true), h1⟩ = 1 then w e else 0) else 0)) := by
        refine Finset.sum_le_sum fun e _ => ?_
        by_cases hde : d e = 1
        · simp only [hde, ↓reduceIte]
          by_cases h0 : (e, false) ∈ H <;> by_cases h1 : (e, true) ∈ H
          · simp only [h0, h1, ↓reduceDIte]
            rcases zmod2_eq_zero_or_one (f ⟨(e, false), h0⟩) with hf0 | hf0 <;>
            rcases zmod2_eq_zero_or_one (f ⟨(e, true), h1⟩) with hf1 | hf1
            · simp [d, h0, h1, hf0, hf1] at hde
            · simp [hf0, hf1]
            · simp [hf0, hf1]
            · simp [hf0, hf1]
          · simp only [h0, h1, ↓reduceDIte, add_zero]
            have hf0 : f ⟨(e, false), h0⟩ = 1 := by simpa [d, h0, h1] using hde
            simp [hf0]
          · simp only [h0, h1, ↓reduceDIte, zero_add]
            have hf1 : f ⟨(e, true), h1⟩ = 1 := by simpa [d, h0, h1] using hde
            simp [hf1]
          · simp [d, h0, h1] at hde
        · simp [hde]
      have h3 : ∑ e : Fin m,
            ((if h0 : (e, false) ∈ H then (if f ⟨(e, false), h0⟩ = 1 then w e else 0) else 0) +
             (if h1 : (e, true) ∈ H then (if f ⟨(e, true), h1⟩ = 1 then w e else 0) else 0)) =
          wt f := by
        have hprod : ∑ e : Fin m,
              ((if h0 : (e, false) ∈ H then (if f ⟨(e, false), h0⟩ = 1 then w e else 0) else 0) +
               (if h1 : (e, true) ∈ H then (if f ⟨(e, true), h1⟩ = 1 then w e else 0) else 0)) =
            ∑ p : Fin m × Bool, if hp : p ∈ H then (if f ⟨p, hp⟩ = 1 then w p.1 else 0) else 0 := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun e _ => ?_
          simp only [Fintype.sum_bool]
          rw [add_comm]
        rw [hprod]
        calc ∑ p : Fin m × Bool, (if hp : p ∈ H then (if f ⟨p, hp⟩ = 1 then w p.1 else 0) else 0)
            = ∑ p ∈ Finset.univ.filter (fun p : Fin m × Bool => p ∈ H),
                if hp : p ∈ H then (if f ⟨p, hp⟩ = 1 then w p.1 else 0) else 0 := by
                  rw [Finset.sum_filter]
                  refine Finset.sum_congr rfl fun p _ => by by_cases hp : p ∈ H <;> simp [hp]
          _ = ∑ p ∈ H, if hp : p ∈ H then (if f ⟨p, hp⟩ = 1 then w p.1 else 0) else 0 := by
                congr 1
                ext p
                simp
          _ = ∑ p ∈ H.attach, (if f p = 1 then w p.1.1 else 0) := by
                rw [← Finset.sum_attach H (fun p => if hp : p ∈ H then (if f ⟨p, hp⟩ = 1 then w p.1 else 0) else 0)]
                refine Finset.sum_congr rfl fun p _ => by simp [p.2]
          _ = wt f := rfl
      omega
    omega

end PEqualNP.Outside.L_pcx_262_aux

theorem PEqualNP.Outside.L_pcx_262 :
  ∀ (n m : ℕ) (left right : Fin m → Fin n) (sign : Fin m → Bool),
    let oddSet := fun D : Finset (Fin m) =>
      Odd ((D.filter (fun e => sign e = true)).card) ∧
      ∀ v : Fin n, Even ((D.filter (fun e => left e = v)).card +
        (D.filter (fun e => right e = v)).card)
    let compatible := fun H : Finset (Fin m × Bool) =>
      ∃ x : Fin n → Bool, ∀ p ∈ H, x (left p.1) = p.2 →
        x (right p.1) = (p.2 ^^ sign p.1)
    ∀ (w : Fin m → ℕ) (K : ℕ),
      (∃ H : Finset (Fin m × Bool), ¬ compatible H ∧ H.sum (fun p => w p.1) ≤ K) ↔
      ∃ D : Finset (Fin m), oddSet D ∧ 2*D.sum w ≤ K := by
  intro n m left right sign oddSet compatible w K
  constructor
  · rintro ⟨H, hincomp, hwt⟩
    exact PEqualNP.Outside.L_pcx_262_aux.forwards_dir n m left right sign w K H hincomp hwt
  · rintro ⟨D, ⟨hodd, heven⟩, hwt⟩
    exact PEqualNP.Outside.L_pcx_262_aux.backwards_dir n m left right sign w K D hodd heven hwt
