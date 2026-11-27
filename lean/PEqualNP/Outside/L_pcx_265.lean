import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_265_aux

private def b2z (b : Bool) : ZMod 2 :=
  if b then 1 else 0

private noncomputable def b2zPoly {n : ℕ} (b : Bool) : MvPolynomial (Fin n) (ZMod 2) :=
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

private lemma unsat_core_unit {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (H : Finset (Fin m × Bool))
    (hincomp : ¬ ∃ x : Fin n → Bool, ∀ p ∈ H, x (left p.1) = p.2 →
      x (right p.1) = (p.2 ^^ sign p.1)) :
    ∃ D : Finset (Fin m),
      (Odd ((D.filter (fun e => sign e = true)).card) ∧
        ∀ v : Fin n, Even ((D.filter (fun e => left e = v)).card +
          (D.filter (fun e => right e = v)).card)) ∧
      2 * D.card ≤ H.card := by
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
  let wt : (ι → ZMod 2) → ℕ := fun f => ∑ q : ι, if f q = 1 then 1 else 0
  have hsum_wt : 2 * ∑ f ∈ oddSet, wt f ≤ oddSet.card * H.card := by
    have h1 : 2 * ∑ f ∈ oddSet, wt f =
        ∑ q : ι, 2 * (oddSet.filter (fun f => f q = 1)).card := by
      simp only [wt]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    have h2 : ∑ q : ι, 2 * (oddSet.filter (fun f => f q = 1)).card ≤
        ∑ _q : ι, oddSet.card :=
      Finset.sum_le_sum fun q _ => hhalf q
    have h3 : ∑ _q : ι, oddSet.card = oddSet.card * H.card := by
      rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_coe, mul_comm]
    omega
  have hex_f : ∃ f ∈ oddSet, 2 * wt f ≤ H.card := by
    by_contra hall
    push Not at hall
    have hgt : oddSet.card * (H.card + 1) ≤ 2 * ∑ f ∈ oddSet, wt f := by
      rw [Finset.mul_sum]
      calc oddSet.card * (H.card + 1) = ∑ _f ∈ oddSet, (H.card + 1) := by
              rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ f ∈ oddSet, 2 * wt f :=
              Finset.sum_le_sum fun f hf => Nat.succ_le_of_lt (hall f hf)
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
              congr 1; ext p; simp
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
  · have hDle : D.card ≤ wt f := by
      have h1 : D.card = ∑ e : Fin m, if d e = 1 then 1 else 0 := by
        simp [D, Finset.sum_boole]
      have h2 : ∑ e : Fin m, (if d e = 1 then 1 else 0) ≤
          ∑ e : Fin m,
            ((if h0 : (e, false) ∈ H then (if f ⟨(e, false), h0⟩ = 1 then 1 else 0) else 0) +
             (if h1 : (e, true) ∈ H then (if f ⟨(e, true), h1⟩ = 1 then 1 else 0) else 0)) := by
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
            ((if h0 : (e, false) ∈ H then (if f ⟨(e, false), h0⟩ = 1 then 1 else 0) else 0) +
             (if h1 : (e, true) ∈ H then (if f ⟨(e, true), h1⟩ = 1 then 1 else 0) else 0)) =
          wt f := by
        have hprod : ∑ e : Fin m,
              ((if h0 : (e, false) ∈ H then (if f ⟨(e, false), h0⟩ = 1 then 1 else 0) else 0) +
               (if h1 : (e, true) ∈ H then (if f ⟨(e, true), h1⟩ = 1 then 1 else 0) else 0)) =
            ∑ p : Fin m × Bool, if hp : p ∈ H then (if f ⟨p, hp⟩ = 1 then 1 else 0) else 0 := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun e _ => ?_
          simp only [Fintype.sum_bool]
          rw [add_comm]
        rw [hprod]
        calc ∑ p : Fin m × Bool, (if hp : p ∈ H then (if f ⟨p, hp⟩ = 1 then 1 else 0) else 0)
            = ∑ p ∈ Finset.univ.filter (fun p : Fin m × Bool => p ∈ H),
                if hp : p ∈ H then (if f ⟨p, hp⟩ = 1 then 1 else 0) else 0 := by
                  rw [Finset.sum_filter]
                  refine Finset.sum_congr rfl fun p _ => by by_cases hp : p ∈ H <;> simp [hp]
          _ = ∑ p ∈ H, if hp : p ∈ H then (if f ⟨p, hp⟩ = 1 then 1 else 0) else 0 := by
                congr 1; ext p; simp
          _ = ∑ p ∈ H.attach, (if f p = 1 then 1 else 0) := by
                rw [← Finset.sum_attach H (fun p => if hp : p ∈ H then (if f ⟨p, hp⟩ = 1 then 1 else 0) else 0)]
                refine Finset.sum_congr rfl fun p _ => by simp [p.2]
          _ = wt f := rfl
      omega
    omega

private def IsTrail {n m : ℕ} (left right : Fin m → Fin n)
    (D : Finset (Fin m)) (k : ℕ) (v : ℕ → Fin n) (edge : ℕ → Fin m) : Prop :=
  (∀ j < k, edge j ∈ D) ∧
  (∀ j1 < k, ∀ j2 < k, edge j1 = edge j2 → j1 = j2) ∧
  (∀ j < k, (v j = left (edge j) ∧ v (j + 1) = right (edge j)) ∨
    (v j = right (edge j) ∧ v (j + 1) = left (edge j)))

private lemma trail_inc_sum {n m : ℕ} (left right : Fin m → Fin n)
    (D : Finset (Fin m)) (k : ℕ) (v : ℕ → Fin n) (edge : ℕ → Fin m)
    (ht : IsTrail left right D k v edge) (w : Fin n) :
    ∑ e ∈ (Finset.range k).image edge, inc left right e w =
      (if w = v 0 then 1 else 0) + (if w = v k then 1 else 0) := by
  induction k with
  | zero =>
    simp [zmod2_add_self]
  | succ k ih =>
    have htk : IsTrail left right D k v edge :=
      ⟨fun j hj => ht.1 j (Nat.lt_succ_of_lt hj),
       fun j1 h1 j2 h2 => ht.2.1 j1 (Nat.lt_succ_of_lt h1) j2 (Nat.lt_succ_of_lt h2),
       fun j hj => ht.2.2 j (Nat.lt_succ_of_lt hj)⟩
    have hnotmem : edge k ∉ (Finset.range k).image edge := by
      intro hm
      obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.1 hm
      have hjlt : j < k := Finset.mem_range.1 hj
      have := ht.2.1 j (Nat.lt_succ_of_lt hjlt) k (Nat.lt_succ_self k) hjeq
      omega
    rw [Finset.range_add_one, Finset.image_insert, Finset.sum_insert hnotmem, ih htk]
    have hstep : inc left right (edge k) w =
        (if w = v k then 1 else 0) + (if w = v (k + 1) then 1 else 0) := by
      rcases ht.2.2 k (Nat.lt_succ_self k) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [inc, h1, h2, eq_comm]
      · simp only [inc, ← h1, ← h2, eq_comm]
        rw [add_comm]
    rw [hstep]
    calc ((if w = v k then (1 : ZMod 2) else 0) + (if w = v (k + 1) then 1 else 0)) +
          ((if w = v 0 then 1 else 0) + (if w = v k then 1 else 0))
        = (if w = v 0 then 1 else 0) + (if w = v (k + 1) then 1 else 0) +
          ((if w = v k then 1 else 0) + (if w = v k then 1 else 0)) := by ring
      _ = (if w = v 0 then 1 else 0) + (if w = v (k + 1) then 1 else 0) := by
          rw [zmod2_add_self, add_zero]

private lemma oddSet_implies_negative {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool) :
    ∀ c : ℕ, ∀ D : Finset (Fin m), D.card ≤ c →
      Odd ((D.filter (fun e => sign e = true)).card) →
      (∀ v : Fin n, Even ((D.filter (fun e => left e = v)).card +
        (D.filter (fun e => right e = v)).card)) →
      ∃ k ≤ D.card,
        ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m), v 0 = v k ∧
          Odd (((Finset.range k).filter (fun j => sign (edge j) = true)).card) ∧
          ∀ j < k, (v j = left (edge j) ∧ v (j + 1) = right (edge j)) ∨
            (v j = right (edge j) ∧ v (j + 1) = left (edge j)) := by
  intro c
  induction c with
  | zero =>
    intro D hD hodd _
    have hempty : D = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hD)
    subst hempty
    simp at hodd
  | succ c ih =>
    intro D hD hodd heven
    have hDne : D.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      subst hempty
      simp at hodd
    obtain ⟨e₀, he₀⟩ := hDne
    have hex1 : ∃ v edge, IsTrail left right D 1 v edge := by
      refine ⟨fun j => if j = 0 then left e₀ else right e₀, fun _ => e₀, ?_, ?_, ?_⟩
      · intro j _; exact he₀
      · intro j1 h1 j2 h2 _; omega
      · intro j hj
        have hj0 : j = 0 := by omega
        subst hj0
        left; simp
    have hbound : ∀ k, (∃ v edge, IsTrail left right D k v edge) → k ≤ D.card := by
      rintro k ⟨v, edge, ht⟩
      have hsub : (Finset.range k).image edge ⊆ D := by
        intro e he
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 he
        exact ht.1 j (Finset.mem_range.1 hj)
      have hcard : ((Finset.range k).image edge).card = k := by
        rw [Finset.card_image_of_injOn, Finset.card_range]
        intro j1 h1 j2 h2 hEq
        exact ht.2.1 j1 (Finset.mem_range.1 h1) j2 (Finset.mem_range.1 h2) hEq
      rw [← hcard]
      exact Finset.card_le_card hsub
    classical
    let K := Nat.findGreatest (fun k => ∃ v edge, IsTrail left right D k v edge) D.card
    have hK_ge1 : 1 ≤ K :=
      Nat.le_findGreatest (hbound 1 hex1) hex1
    have hK_le : K ≤ D.card := Nat.findGreatest_le D.card
    have hK_ex : ∃ v edge, IsTrail left right D K v edge :=
      Nat.findGreatest_spec (P := fun k => ∃ v edge, IsTrail left right D k v edge) (hbound 1 hex1) hex1
    obtain ⟨v, edge, ht⟩ := hK_ex
    let E : Finset (Fin m) := (Finset.range K).image edge
    have hEsub : E ⊆ D := by
      intro e he
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 he
      exact ht.1 j (Finset.mem_range.1 hj)
    have hEcard : E.card = K := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro j1 h1 j2 h2 hEq
      exact ht.2.1 j1 (Finset.mem_range.1 h1) j2 (Finset.mem_range.1 h2) hEq
    have hclosed : v 0 = v K := by
      by_contra hne
      have hEdeg : ∑ e ∈ E, inc left right e (v K) = 1 := by
        rw [trail_inc_sum left right D K v edge ht (v K)]
        have hne' : v K ≠ v 0 := Ne.symm hne
        simp [hne']
      have hDdeg : ∑ e ∈ D, inc left right e (v K) = 0 := by
        rw [sum_inc_over_finset, (zmod2_cast_eq_zero_iff_even _).2 (heven (v K))]
      have hsdiff : ∑ e ∈ D \ E, inc left right e (v K) = 1 := by
        have hsplit := Finset.sum_sdiff hEsub (f := fun e => inc left right e (v K))
        rw [hEdeg, hDdeg] at hsplit
        have h1 : ∑ e ∈ D \ E, inc left right e (v K) =
            (∑ e ∈ D \ E, inc left right e (v K) + 1) + 1 := by
          rw [add_assoc, zmod2_add_self, add_zero]
        rw [h1, hsplit, zero_add]
      have hex_e : ∃ e' ∈ D \ E, inc left right e' (v K) ≠ 0 := by
        by_contra hall
        push Not at hall
        have h0 : ∑ e ∈ D \ E, inc left right e (v K) = 0 := Finset.sum_eq_zero hall
        rw [h0] at hsdiff
        exact absurd hsdiff (by decide)
      obtain ⟨e', he', hinc⟩ := hex_e
      have he'D : e' ∈ D := (Finset.mem_sdiff.1 he').1
      have he'E : e' ∉ E := (Finset.mem_sdiff.1 he').2
      have htouch : left e' = v K ∨ right e' = v K := by
        by_contra hno
        push Not at hno
        apply hinc
        simp [inc, hno.1, hno.2]
      let nextV : Fin n := if left e' = v K then right e' else left e'
      let v' : ℕ → Fin n := fun j => if j = K + 1 then nextV else v j
      let edge' : ℕ → Fin m := fun j => if j = K then e' else edge j
      have ht' : IsTrail left right D (K + 1) v' edge' := by
        refine ⟨?_, ?_, ?_⟩
        · intro j hj
          by_cases hjk : j = K
          · simp [edge', hjk, he'D]
          · simp [edge', hjk, ht.1 j (by omega)]
        · intro j1 h1 j2 h2 hEq
          by_cases h1k : j1 = K <;> by_cases h2k : j2 = K
          · omega
          · simp only [edge', h1k, h2k, ↓reduceIte] at hEq
            exact absurd (hEq ▸ Finset.mem_image.2 ⟨j2, Finset.mem_range.2 (by omega), rfl⟩) he'E
          · simp only [edge', h1k, h2k, ↓reduceIte] at hEq
            exact absurd (hEq.symm ▸ Finset.mem_image.2 ⟨j1, Finset.mem_range.2 (by omega), rfl⟩) he'E
          · simp only [edge', h1k, h2k, ↓reduceIte] at hEq
            exact ht.2.1 j1 (by omega) j2 (by omega) hEq
        · intro j hj
          by_cases hjk : j = K
          · subst hjk
            have hne1 : K ≠ K + 1 := by omega
            simp only [v', edge', hne1, ↓reduceIte]
            rcases htouch with hl | hr
            · left; exact ⟨hl.symm, by simp [nextV, hl]⟩
            · by_cases hl : left e' = v K
              · left; exact ⟨hl.symm, by simp [nextV, hl]⟩
              · right; exact ⟨hr.symm, by simp [nextV, hl]⟩
          · have h1 : j ≠ K + 1 := by omega
            have h2 : j + 1 ≠ K + 1 := by omega
            simp only [v', edge', h1, h2, hjk, ↓reduceIte]
            exact ht.2.2 j (by omega)
      have hK1_le : K + 1 ≤ D.card := hbound (K + 1) ⟨v', edge', ht'⟩
      have hK1_le_K : K + 1 ≤ K := Nat.le_findGreatest hK1_le ⟨v', edge', ht'⟩
      omega
    have hE_filter : (E.filter (fun e => sign e = true)).card =
        ((Finset.range K).filter (fun j => sign (edge j) = true)).card := by
      symm
      refine Finset.card_bij (fun j _ => edge j) ?_ ?_ ?_
      · intro j hj
        rw [Finset.mem_filter] at hj ⊢
        exact ⟨Finset.mem_image.2 ⟨j, hj.1, rfl⟩, hj.2⟩
      · intro j1 h1 j2 h2 hEq
        exact ht.2.1 j1 (Finset.mem_range.1 (Finset.mem_filter.1 h1).1)
          j2 (Finset.mem_range.1 (Finset.mem_filter.1 h2).1) hEq
      · intro e he
        rw [Finset.mem_filter] at he
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 he.1
        exact ⟨j, Finset.mem_filter.2 ⟨hj, he.2⟩, rfl⟩
    rcases Nat.even_or_odd ((E.filter (fun e => sign e = true)).card) with hEev | hEodd
    · let D' := D \ E
      have hD'card : D'.card ≤ c := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.2 hEsub, hEcard]
        omega
      have hD'odd : Odd ((D'.filter (fun e => sign e = true)).card) := by
        rw [← zmod2_cast_eq_one_iff_odd, ← sum_b2z_over_finset]
        have hsplit := Finset.sum_sdiff hEsub (f := fun e => b2z (sign e))
        have hD1 : ∑ e ∈ D, b2z (sign e) = 1 := by
          rw [sum_b2z_over_finset, (zmod2_cast_eq_one_iff_odd _).2 hodd]
        have hE0 : ∑ e ∈ E, b2z (sign e) = 0 := by
          rw [sum_b2z_over_finset, (zmod2_cast_eq_zero_iff_even _).2 hEev]
        rw [hD1, hE0, add_zero] at hsplit
        exact hsplit
      have hD'even : ∀ w : Fin n, Even ((D'.filter (fun e => left e = w)).card +
          (D'.filter (fun e => right e = w)).card) := by
        intro w
        rw [← zmod2_cast_eq_zero_iff_even, ← sum_inc_over_finset]
        have hsplit := Finset.sum_sdiff hEsub (f := fun e => inc left right e w)
        have hDw : ∑ e ∈ D, inc left right e w = 0 := by
          rw [sum_inc_over_finset, (zmod2_cast_eq_zero_iff_even _).2 (heven w)]
        have hEw : ∑ e ∈ E, inc left right e w = 0 := by
          rw [trail_inc_sum left right D K v edge ht w, ← hclosed, zmod2_add_self]
        rw [hDw, hEw, add_zero] at hsplit
        exact hsplit
      obtain ⟨k, hk, hneg⟩ := ih D' hD'card hD'odd hD'even
      exact ⟨k, le_trans hk (Finset.card_le_card Finset.sdiff_subset), hneg⟩
    · rw [hE_filter] at hEodd
      exact ⟨K, hK_le, v, edge, hclosed, hEodd, ht.2.2⟩

private def cl {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (e : Fin m) (a : Bool) : PEqualNP.ProofComplexity.Clause (Fin n) :=
  {(left e, !a), (right e, a ^^ sign e)}

private noncomputable def ax {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (e : Fin m) (a : Bool) : MvPolynomial (Fin n) (ZMod 2) :=
  PEqualNP.ProofComplexity.clausePoly (cl left right sign e a)

private noncomputable def litPoly {n : ℕ} (l : Fin n × Bool) : MvPolynomial (Fin n) (ZMod 2) :=
  if l.2 = true then 1 + MvPolynomial.X l.1 else MvPolynomial.X l.1

private lemma ax_eq_distinct {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (e : Fin m) (a : Bool) (hne : (left e, !a) ≠ (right e, a ^^ sign e)) :
    ax left right sign e a = litPoly (left e, !a) * litPoly (right e, a ^^ sign e) := by
  unfold ax PEqualNP.ProofComplexity.clausePoly cl litPoly
  rw [Finset.prod_pair hne]

private lemma ax_eq_same {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (e : Fin m) (a : Bool) (heq : (left e, !a) = (right e, a ^^ sign e)) :
    ax left right sign e a = litPoly (left e, !a) := by
  unfold ax PEqualNP.ProofComplexity.clausePoly cl litPoly
  rw [heq, Finset.pair_eq_singleton, Finset.prod_singleton]

private lemma zmod2_poly_add_self {n : ℕ} (p : MvPolynomial (Fin n) (ZMod 2)) : p + p = 0 := by
  ext s
  simp [zmod2_add_self]

private lemma ax_sum_pair {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (e : Fin m) :
    ax left right sign e false + ax left right sign e true =
      MvPolynomial.X (left e) + MvPolynomial.X (right e) + b2zPoly (sign e) := by
  by_cases huv : left e = right e
  · cases hs : sign e
    · have hne0 : (left e, !false) ≠ (right e, false ^^ sign e) := by simp [huv, hs]
      have hne1 : (left e, !true) ≠ (right e, true ^^ sign e) := by simp [huv, hs]
      rw [ax_eq_distinct _ _ _ e false hne0, ax_eq_distinct _ _ _ e true hne1]
      simp only [litPoly, huv, hs, b2zPoly, Bool.not_false, Bool.not_true,
        Bool.false_xor, Bool.true_xor, ↓reduceIte, Bool.false_eq_true, add_zero]
      rw [mul_comm (MvPolynomial.X (right e)) _, zmod2_poly_add_self, zmod2_poly_add_self]
    · have heq0 : (left e, !false) = (right e, false ^^ sign e) := by simp [huv, hs]
      have heq1 : (left e, !true) = (right e, true ^^ sign e) := by simp [huv, hs]
      rw [ax_eq_same _ _ _ e false heq0, ax_eq_same _ _ _ e true heq1]
      simp only [litPoly, huv, b2zPoly, Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true]
      rw [zmod2_poly_add_self, zero_add, add_assoc, zmod2_poly_add_self, add_zero]
  · have hne0 : (left e, !false) ≠ (right e, false ^^ sign e) := fun h => huv (congrArg Prod.fst h)
    have hne1 : (left e, !true) ≠ (right e, true ^^ sign e) := fun h => huv (congrArg Prod.fst h)
    rw [ax_eq_distinct _ _ _ e false hne0, ax_eq_distinct _ _ _ e true hne1]
    cases hs : sign e
    · simp only [litPoly, b2zPoly, Bool.not_false, Bool.not_true, Bool.false_xor,
        Bool.true_xor, ↓reduceIte, Bool.false_eq_true, add_zero]
      have h1 : ((1 : MvPolynomial (Fin n) (ZMod 2)) + MvPolynomial.X (left e)) * MvPolynomial.X (right e) +
          MvPolynomial.X (left e) * (1 + MvPolynomial.X (right e)) =
          MvPolynomial.X (left e) + MvPolynomial.X (right e) +
          (MvPolynomial.X (left e) * MvPolynomial.X (right e) +
            MvPolynomial.X (left e) * MvPolynomial.X (right e)) := by ring
      rw [h1, zmod2_poly_add_self, add_zero]
    · simp only [litPoly, b2zPoly, Bool.not_false, Bool.not_true, Bool.false_xor,
        Bool.true_xor, ↓reduceIte, Bool.false_eq_true]
      have h1 : ((1 : MvPolynomial (Fin n) (ZMod 2)) + MvPolynomial.X (left e)) * (1 + MvPolynomial.X (right e)) +
          MvPolynomial.X (left e) * MvPolynomial.X (right e) =
          MvPolynomial.X (left e) + MvPolynomial.X (right e) + 1 +
          (MvPolynomial.X (left e) * MvPolynomial.X (right e) +
            MvPolynomial.X (left e) * MvPolynomial.X (right e)) := by ring
      rw [h1, zmod2_poly_add_self, add_zero]

private lemma eval_litPoly {n : ℕ} (x : Fin n → Bool) (l : Fin n × Bool) :
    MvPolynomial.eval (fun v => b2z (x v)) (litPoly l) = 0 ↔ x l.1 = l.2 := by
  rcases l with ⟨v, s⟩
  cases s <;> cases hx : x v
  · simp [litPoly, b2z, hx]
  · simp [litPoly, b2z, hx]
  · simp [litPoly, b2z, hx]
  · simp only [litPoly, b2z, hx, ↓reduceIte, map_add, map_one, MvPolynomial.eval_X, iff_true]
    decide

private lemma eval_ax_eq_zero {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (x : Fin n → Bool) (e : Fin m) (a : Bool)
    (h : x (left e) = a → x (right e) = (a ^^ sign e)) :
    MvPolynomial.eval (fun v => b2z (x v)) (ax left right sign e a) = 0 := by
  by_cases hne : (left e, !a) = (right e, a ^^ sign e)
  · rw [ax_eq_same _ _ _ e a hne]
    rw [eval_litPoly]
    have hl : left e = right e := congrArg Prod.fst hne
    have hb : (!a) = (a ^^ sign e) := congrArg Prod.snd hne
    by_cases hxa : x (left e) = a
    · have hr := h hxa
      rw [← hl, hxa, ← hb] at hr
      cases a <;> simp at hr
    · cases a <;> cases hx : x (left e) <;> simp [hx] at hxa ⊢
  · rw [ax_eq_distinct _ _ _ e a hne, map_mul]
    by_cases hxa : x (left e) = a
    · have hr : x (right e) = (a ^^ sign e) := h hxa
      rw [(eval_litPoly x (right e, a ^^ sign e)).2 hr, mul_zero]
    · have hl : x (left e) = !a := by cases a <;> cases hx : x (left e) <;> simp_all
      rw [(eval_litPoly x (left e, !a)).2 hl, zero_mul]

private lemma totalDegree_litPoly_le {n : ℕ} (l : Fin n × Bool) :
    (litPoly l).totalDegree ≤ 1 := by
  rcases l with ⟨v, s⟩
  cases s
  · simp [litPoly, MvPolynomial.totalDegree_X]
  · simp only [litPoly, ↓reduceIte]
    exact le_trans (MvPolynomial.totalDegree_add 1 (MvPolynomial.X v))
      (by simp [MvPolynomial.totalDegree_X])

private lemma totalDegree_ax_le {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (e : Fin m) (a : Bool) :
    (ax left right sign e a).totalDegree ≤
      if left e = right e ∧ sign e = true then 1 else 2 := by
  by_cases hloop : left e = right e ∧ sign e = true
  · have heq : (left e, !a) = (right e, a ^^ sign e) := by
      rw [hloop.1, hloop.2]
      cases a <;> rfl
    rw [ax_eq_same _ _ _ e a heq]
    simp only [hloop, and_self, ↓reduceIte]
    exact totalDegree_litPoly_le _
  · simp only [hloop, ↓reduceIte]
    by_cases hne : (left e, !a) = (right e, a ^^ sign e)
    · rw [ax_eq_same _ _ _ e a hne]
      exact le_trans (totalDegree_litPoly_le _) (by omega)
    · rw [ax_eq_distinct _ _ _ e a hne]
      have h1 := MvPolynomial.totalDegree_mul (litPoly (left e, !a)) (litPoly (right e, a ^^ sign e))
      have h2 := totalDegree_litPoly_le (left e, !a)
      have h3 := totalDegree_litPoly_le (right e, a ^^ sign e)
      omega

private lemma coeff_ne_zero_le_totalDegree {n : ℕ} (p : MvPolynomial (Fin n) (ZMod 2))
    (s : Fin n →₀ ℕ) (h : p.coeff s ≠ 0) :
    s.sum (fun _ e => e) ≤ p.totalDegree := by
  have hmem : s ∈ p.support := MvPolynomial.mem_support_iff.2 h
  exact Finset.le_sup (f := fun t : Fin n →₀ ℕ => t.sum fun _ e => e) hmem

private lemma poly_coeff_add {n : ℕ} (p q : MvPolynomial (Fin n) (ZMod 2)) (s : Fin n →₀ ℕ) :
    (p + q).coeff s = p.coeff s + q.coeff s := by
  exact congrFun (congrArg DFunLike.coe (AddMonoidAlgebra.coeff_add p q)) s

private lemma totalDegree_boolAx_ge_two {n : ℕ} (v : Fin n) :
    2 ≤ (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v : MvPolynomial (Fin n) (ZMod 2)).totalDegree := by
  let s : Fin n →₀ ℕ := Finsupp.single v 2
  have hs : s.sum (fun _ e => e) = 2 := by
    simp [s]
  have hcoeff : (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v : MvPolynomial (Fin n) (ZMod 2)).coeff s ≠ 0 := by
    have hsq : (MvPolynomial.X v * MvPolynomial.X v : MvPolynomial (Fin n) (ZMod 2)) =
        MvPolynomial.monomial s 1 := by
      simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, mul_one, ← Finsupp.single_add, s]
    rw [poly_coeff_add, hsq, MvPolynomial.coeff_monomial, MvPolynomial.coeff_X]
    have hne : Finsupp.single v 1 ≠ s := by
      intro h
      have := congrFun (congrArg DFunLike.coe h) v
      simp [s] at this
    simp only [hne, ↓reduceIte, add_zero]
    decide
  have hle := coeff_ne_zero_le_totalDegree _ s hcoeff
  omega

private lemma totalDegree_litPoly_ge_one {n : ℕ} (l : Fin n × Bool) :
    1 ≤ (litPoly l).totalDegree := by
  rcases l with ⟨v, b⟩
  let s : Fin n →₀ ℕ := Finsupp.single v 1
  have hs : s.sum (fun _ e => e) = 1 := by simp [s]
  have hcoeff : (litPoly (v, b)).coeff s ≠ 0 := by
    have hne : (0 : Fin n →₀ ℕ) ≠ s := by
      intro h
      have := congrFun (congrArg DFunLike.coe h) v
      simp [s] at this
    cases b
    · simp only [litPoly, Bool.false_eq_true, ↓reduceIte, MvPolynomial.coeff_X, s, ↓reduceIte]
      decide
    · simp only [litPoly, ↓reduceIte]
      rw [poly_coeff_add, MvPolynomial.coeff_one, MvPolynomial.coeff_X]
      simp only [hne, ↓reduceIte, zero_add, s]
      decide
  have hle := coeff_ne_zero_le_totalDegree _ s hcoeff
  omega

private lemma totalDegree_litPoly_mul_distinct_ge_two {n : ℕ} (u v : Fin n) (huv : u ≠ v)
    (b1 b2 : Bool) :
    2 ≤ (litPoly (u, b1) * litPoly (v, b2)).totalDegree := by
  let s : Fin n →₀ ℕ := Finsupp.single u 1 + Finsupp.single v 1
  have hs : s.sum (fun _ e => e) = 2 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
  have hcoeff : (litPoly (u, b1) * litPoly (v, b2)).coeff s ≠ 0 := by
    have hXuv : (MvPolynomial.X u * MvPolynomial.X v : MvPolynomial (Fin n) (ZMod 2)) =
        MvPolynomial.monomial s 1 := by
      simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, mul_one, s]
    have hne0 : (0 : Fin n →₀ ℕ) ≠ s := by
      intro h
      have := congrFun (congrArg DFunLike.coe h) u
      simp [s] at this
      omega
    have hneu : Finsupp.single u 1 ≠ s := by
      intro h
      have := congrFun (congrArg DFunLike.coe h) v
      simp [s, huv] at this
    have hnev : Finsupp.single v 1 ≠ s := by
      intro h
      have := congrFun (congrArg DFunLike.coe h) u
      simp [s, huv.symm] at this
    have hc1 : (1 : MvPolynomial (Fin n) (ZMod 2)).coeff s = 0 := by
      rw [MvPolynomial.coeff_one]
      simp only [hne0, ↓reduceIte]
    have hcu : (MvPolynomial.X u : MvPolynomial (Fin n) (ZMod 2)).coeff s = 0 := by
      rw [MvPolynomial.coeff_X]
      simp only [hneu, ↓reduceIte]
    have hcv : (MvPolynomial.X v : MvPolynomial (Fin n) (ZMod 2)).coeff s = 0 := by
      rw [MvPolynomial.coeff_X]
      simp only [hnev, ↓reduceIte]
    have hcuv : (MvPolynomial.X u * MvPolynomial.X v : MvPolynomial (Fin n) (ZMod 2)).coeff s = 1 := by
      rw [hXuv, MvPolynomial.coeff_monomial]
      simp only [↓reduceIte]
    cases b1 <;> cases b2
    · simp only [litPoly, Bool.false_eq_true, ↓reduceIte, hcuv]
      decide
    · simp only [litPoly, Bool.false_eq_true, ↓reduceIte, mul_add, mul_one]
      rw [poly_coeff_add, hcu, hcuv, zero_add]
      decide
    · simp only [litPoly, Bool.false_eq_true, ↓reduceIte, add_mul, one_mul]
      rw [poly_coeff_add, hcv, hcuv, zero_add]
      decide
    · have hexp : ((1 : MvPolynomial (Fin n) (ZMod 2)) + MvPolynomial.X u) * (1 + MvPolynomial.X v) =
          1 + MvPolynomial.X u + MvPolynomial.X v + MvPolynomial.X u * MvPolynomial.X v := by ring
      simp only [litPoly, ↓reduceIte, hexp]
      rw [poly_coeff_add, poly_coeff_add, poly_coeff_add, hc1, hcu, hcv, hcuv, zero_add, zero_add, zero_add]
      decide
  have hle := coeff_ne_zero_le_totalDegree _ s hcoeff
  omega

private lemma totalDegree_ax_ge_one {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (e : Fin m) (a : Bool) :
    1 ≤ (ax left right sign e a).totalDegree := by
  by_cases huv : left e = right e
  · cases hs : sign e
    · have hne : (left e, !a) ≠ (right e, a ^^ sign e) := by
        rw [huv, hs]
        cases a <;> simp
      rw [ax_eq_distinct _ _ _ e a hne]
      have hprod : litPoly (left e, !a) * litPoly (right e, a ^^ sign e) =
          MvPolynomial.X (left e) * MvPolynomial.X (left e) + MvPolynomial.X (left e) := by
        rw [huv, hs]
        cases a
        · simp only [litPoly, Bool.not_false, Bool.false_xor, ↓reduceIte, Bool.false_eq_true]
          ring
        · simp only [litPoly, Bool.not_true, Bool.true_xor, Bool.not_false, ↓reduceIte, Bool.false_eq_true]
          ring
      rw [hprod]
      exact le_trans (by omega) (totalDegree_boolAx_ge_two (left e))
    · have heq : (left e, !a) = (right e, a ^^ sign e) := by
        rw [huv, hs]
        cases a <;> rfl
      rw [ax_eq_same _ _ _ e a heq]
      exact totalDegree_litPoly_ge_one _
  · have hne : (left e, !a) ≠ (right e, a ^^ sign e) := fun h => huv (congrArg Prod.fst h)
    rw [ax_eq_distinct _ _ _ e a hne]
    exact le_trans (by omega) (totalDegree_litPoly_mul_distinct_ge_two _ _ huv _ _)

private lemma totalDegree_ax_ge_two {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (e : Fin m) (a : Bool) (hnot : ¬ (left e = right e ∧ sign e = true)) :
    2 ≤ (ax left right sign e a).totalDegree := by
  by_cases huv : left e = right e
  · have hs : sign e = false := by
      cases h : sign e
      · rfl
      · exact absurd ⟨huv, h⟩ hnot
    have hne : (left e, !a) ≠ (right e, a ^^ sign e) := by
      rw [huv, hs]
      cases a <;> simp
    rw [ax_eq_distinct _ _ _ e a hne]
    have hprod : litPoly (left e, !a) * litPoly (right e, a ^^ sign e) =
        MvPolynomial.X (left e) * MvPolynomial.X (left e) + MvPolynomial.X (left e) := by
      rw [huv, hs]
      cases a
      · simp only [litPoly, Bool.not_false, Bool.false_xor, ↓reduceIte, Bool.false_eq_true]
        ring
      · simp only [litPoly, Bool.not_true, Bool.true_xor, Bool.not_false, ↓reduceIte, Bool.false_eq_true]
        ring
    rw [hprod]
    exact totalDegree_boolAx_ge_two (left e)
  · have hne : (left e, !a) ≠ (right e, a ^^ sign e) := fun h => huv (congrArg Prod.fst h)
    rw [ax_eq_distinct _ _ _ e a hne]
    exact totalDegree_litPoly_mul_distinct_ge_two _ _ huv _ _

private inductive StepTag (n m t : ℕ)
  | zero
  | ax (e : Fin m) (a : Bool)
  | bool (v : Fin n)
  | add (j k : Fin t)
  | mul (j : Fin t) (v : Fin n)

private def parents {n m t : ℕ} : StepTag n m t → Finset (Fin t)
  | .zero => ∅
  | .ax _ _ => ∅
  | .bool _ => ∅
  | .add j k => {j, k}
  | .mul j _ => {j}

private def isAxTag {n m t : ℕ} : StepTag n m t → Bool
  | .ax _ _ => true
  | _ => false

private def isAddTag {n m t : ℕ} : StepTag n m t → Bool
  | .add _ _ => true
  | _ => false

private def isMulTag {n m t : ℕ} : StepTag n m t → Bool
  | .mul _ _ => true
  | _ => false

private lemma parents_card_le {n m t : ℕ} (tag : StepTag n m t) :
    (parents tag).card ≤ if isAddTag tag then 2 else if isMulTag tag then 1 else 0 := by
  cases tag with
  | zero => simp [parents, isAddTag, isMulTag]
  | ax _ _ => simp [parents, isAddTag, isMulTag]
  | bool _ => simp [parents, isAddTag, isMulTag]
  | add j k =>
    simp only [parents, isAddTag, ↓reduceIte]
    exact Finset.card_le_two
  | mul j _ => simp [parents, isAddTag, isMulTag]

private lemma legal_forward {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (g : ℕ) (hgpos : 1 ≤ g)
    (hmin : ∀ k < g, ¬ ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m), v 0 = v k ∧
      Odd (((Finset.range k).filter (fun j => sign (edge j) = true)).card) ∧
      ∀ j < k, (v j = left (edge j) ∧ v (j + 1) = right (edge j)) ∨
        (v j = right (edge j) ∧ v (j + 1) = left (edge j)))
    (L d t : ℕ) (p : Fin t → MvPolynomial (Fin n) (ZMod 2))
    (htL : t ≤ L)
    (hroot : ∃ root, p root = 1)
    (hstep : ∀ i : Fin t, p i = 0 ∨ (∃ e a, p i = ax left right sign e a) ∨
      (∃ v : Fin n, p i = MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v) ∨
      (∃ j < i, ∃ k < i, p i = p j + p k) ∨
      (∃ j < i, ∃ v : Fin n, p i = MvPolynomial.X v * p j))
    (hdeg : ∀ i : Fin t, (p i).totalDegree ≤ d) :
    4 * g ≤ L + 1 ∧ (if g = 1 then 1 else 2) ≤ d := by
  classical
  obtain ⟨root, hroot_eq⟩ := hroot
  have h1ne0 : (1 : MvPolynomial (Fin n) (ZMod 2)) ≠ 0 := one_ne_zero
  have hd_bound : (if g = 1 then 1 else 2) ≤ d := by
    by_contra hlt
    push Not at hlt
    have hall0 : ∀ idx : ℕ, ∀ (hi : idx < t), p ⟨idx, hi⟩ = 0 := by
      intro idx
      induction idx using Nat.strong_induction_on with
      | ind idx ih =>
        intro hi
        rcases hstep ⟨idx, hi⟩ with h0 | ⟨e, a, hax⟩ | ⟨v, hbool⟩ | ⟨j, hj, k, hk, hadd⟩ | ⟨j, hj, v, hmul⟩
        · exact h0
        · have hde := hdeg ⟨idx, hi⟩
          rw [hax] at hde
          by_cases hg1 : g = 1
          · simp only [hg1, ↓reduceIte] at hlt
            have := totalDegree_ax_ge_one left right sign e a
            omega
          · simp only [hg1, ↓reduceIte] at hlt
            have hnot1 : ¬ (left e = right e ∧ sign e = true) := by
              rintro ⟨hlr, hst⟩
              have hg_gt1 : 1 < g := by omega
              apply hmin 1 hg_gt1
              refine ⟨fun _ => left e, fun _ => e, rfl, ?_, ?_⟩
              · simp [hst]
              · intro j hj
                left
                exact ⟨rfl, hlr⟩
            have := totalDegree_ax_ge_two left right sign e a hnot1
            omega
        · have hde := hdeg ⟨idx, hi⟩
          rw [hbool] at hde
          have := totalDegree_boolAx_ge_two v
          split_ifs at hlt <;> omega
        · rw [hadd, ih j.val hj j.isLt, ih k.val hk k.isLt, add_zero]
        · rw [hmul, ih j.val hj j.isLt, mul_zero]
    have h0 := hall0 root.val root.isLt
    rw [hroot_eq] at h0
    exact h1ne0 h0
  let tag : Fin t → StepTag n m t := fun i =>
    if _ : p i = 0 then .zero
    else if h2 : ∃ e a, p i = ax left right sign e a then
      .ax (Classical.choose h2) (Classical.choose (Classical.choose_spec h2))
    else if h3 : ∃ v : Fin n, p i = MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v then
      .bool (Classical.choose h3)
    else if h4 : ∃ j < i, ∃ k < i, p i = p j + p k then
      .add (Classical.choose h4) (Classical.choose (Classical.choose_spec h4).2)
    else if h5 : ∃ j < i, ∃ v : Fin n, p i = MvPolynomial.X v * p j then
      .mul (Classical.choose h5) (Classical.choose (Classical.choose_spec h5).2)
    else .zero
  have htag_lt : ∀ i : Fin t, ∀ u ∈ parents (tag i), u.val < i.val := by
    intro i u hu
    simp only [tag] at hu
    split_ifs at hu with h1 h2 h3 h4 h5
    · simp [parents] at hu
    · simp [parents] at hu
    · simp [parents] at hu
    · simp only [parents, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact (Classical.choose_spec h4).1
      · exact (Classical.choose_spec (Classical.choose_spec h4).2).1
    · simp only [parents, Finset.mem_singleton] at hu
      subst hu
      exact (Classical.choose_spec h5).1
    · simp [parents] at hu
  have htag_eq : ∀ i : Fin t,
      match tag i with
      | .zero => p i = 0
      | .ax e a => p i = ax left right sign e a
      | .bool v => p i = MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v
      | .add j k => p i = p j + p k
      | .mul j v => p i = MvPolynomial.X v * p j := by
    intro i
    simp only [tag]
    split_ifs with h1 h2 h3 h4 h5
    · exact h1
    · exact Classical.choose_spec (Classical.choose_spec h2)
    · exact Classical.choose_spec h3
    · exact (Classical.choose_spec (Classical.choose_spec h4).2).2
    · exact Classical.choose_spec (Classical.choose_spec h5).2
    · rcases hstep i with h | h | h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact absurd h h3
      · exact absurd h h4
      · exact absurd h h5
  let anc : Fin t → Finset (Fin t) :=
    WellFounded.fix (InvImage.wf (fun i : Fin t => i.val) wellFounded_lt) fun i rec =>
      insert i ((parents (tag i)).attach.biUnion fun u => rec u.1 (htag_lt i u.1 u.2))
  have hanc_eq : ∀ i : Fin t,
      anc i = insert i ((parents (tag i)).biUnion anc) := by
    intro i
    change WellFounded.fix _ _ i = _
    rw [WellFounded.fix_eq]
    congr 1
    ext x
    simp [anc]
  have hanc_self : ∀ i : Fin t, i ∈ anc i := by
    intro i
    rw [hanc_eq i]
    exact Finset.mem_insert_self i _
  have hanc_sub : ∀ i : Fin t, ∀ u ∈ parents (tag i), anc u ⊆ anc i := by
    intro i u hu x hx
    rw [hanc_eq i]
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨u, hu, hx⟩)
  have hanc_cover : ∀ idx : ℕ, ∀ (hi : idx < t),
      (anc ⟨idx, hi⟩).erase ⟨idx, hi⟩ ⊆ (anc ⟨idx, hi⟩).biUnion (fun w => parents (tag w)) := by
    intro idx
    induction idx using Nat.strong_induction_on with
    | ind idx ih =>
      intro hi x hx
      have hne : x ≠ ⟨idx, hi⟩ := (Finset.mem_erase.1 hx).1
      have hmem : x ∈ anc ⟨idx, hi⟩ := (Finset.mem_erase.1 hx).2
      rw [hanc_eq ⟨idx, hi⟩] at hmem
      have hmem' : x ∈ (parents (tag ⟨idx, hi⟩)).biUnion anc :=
        (Finset.mem_insert.1 hmem).resolve_left hne
      obtain ⟨u, hu, hxu⟩ := Finset.mem_biUnion.1 hmem'
      by_cases hxu_eq : x = u
      · subst hxu_eq
        exact Finset.mem_biUnion.2 ⟨⟨idx, hi⟩, hanc_self ⟨idx, hi⟩, hu⟩
      · have hx_er : x ∈ (anc u).erase u := Finset.mem_erase.2 ⟨hxu_eq, hxu⟩
        have hult : u.val < idx := htag_lt ⟨idx, hi⟩ u hu
        have hx_cov := ih u.val hult u.isLt hx_er
        obtain ⟨w, hw, hxw⟩ := Finset.mem_biUnion.1 hx_cov
        exact Finset.mem_biUnion.2 ⟨w, hanc_sub ⟨idx, hi⟩ u hu hw, hxw⟩
  let S : Finset (Fin t) := anc root
  let H : Finset (Fin m × Bool) :=
    S.biUnion fun i => match tag i with
      | .ax e a => {(e, a)}
      | _ => ∅
  have hsound : ∀ idx : ℕ, ∀ (hi : idx < t), ⟨idx, hi⟩ ∈ S →
      ∀ x : Fin n → Bool,
        (∀ q ∈ H, x (left q.1) = q.2 → x (right q.1) = (q.2 ^^ sign q.1)) →
        MvPolynomial.eval (fun v => b2z (x v)) (p ⟨idx, hi⟩) = 0 := by
    intro idx
    induction idx using Nat.strong_induction_on with
    | ind idx ih =>
      intro hi hmem x hx
      have hspec := htag_eq ⟨idx, hi⟩
      cases htag : tag ⟨idx, hi⟩ with
      | zero =>
        rw [htag] at hspec
        simp [hspec]
      | ax e a =>
        rw [htag] at hspec
        rw [hspec]
        have hq : (e, a) ∈ H := by
          refine Finset.mem_biUnion.2 ⟨⟨idx, hi⟩, hmem, ?_⟩
          simp [htag]
        exact eval_ax_eq_zero left right sign x e a (hx (e, a) hq)
      | bool v =>
        rw [htag] at hspec
        rw [hspec]
        simp only [map_add, map_mul, MvPolynomial.eval_X]
        cases x v <;> decide
      | add j k =>
        rw [htag] at hspec
        have hjpar : j ∈ parents (tag ⟨idx, hi⟩) := by simp [htag, parents]
        have hkpar : k ∈ parents (tag ⟨idx, hi⟩) := by simp [htag, parents]
        have hjlt : j.val < idx := htag_lt ⟨idx, hi⟩ j hjpar
        have hklt : k.val < idx := htag_lt ⟨idx, hi⟩ k hkpar
        have hjS : j ∈ S := by
          have hsub : anc ⟨idx, hi⟩ ⊆ S := by
            have htrans : ∀ r : ℕ, ∀ (hr : r < t), ∀ a ∈ anc ⟨r, hr⟩, anc a ⊆ anc ⟨r, hr⟩ := by
              intro r
              induction r using Nat.strong_induction_on with
              | ind r ihr =>
                intro hr a ha
                rw [hanc_eq ⟨r, hr⟩] at ha
                rcases Finset.mem_insert.1 ha with rfl | ha'
                · exact fun _ h => h
                · obtain ⟨u, hu, hau⟩ := Finset.mem_biUnion.1 ha'
                  have hult := htag_lt ⟨r, hr⟩ u hu
                  exact Finset.Subset.trans (ihr u.val hult u.isLt a hau) (hanc_sub ⟨r, hr⟩ u hu)
            exact htrans root.val root.isLt ⟨idx, hi⟩ hmem
          exact hsub (hanc_sub ⟨idx, hi⟩ j hjpar (hanc_self j))
        have hkS : k ∈ S := by
          have htrans : ∀ r : ℕ, ∀ (hr : r < t), ∀ a ∈ anc ⟨r, hr⟩, anc a ⊆ anc ⟨r, hr⟩ := by
            intro r
            induction r using Nat.strong_induction_on with
            | ind r ihr =>
              intro hr a ha
              rw [hanc_eq ⟨r, hr⟩] at ha
              rcases Finset.mem_insert.1 ha with rfl | ha'
              · exact fun _ h => h
              · obtain ⟨u, hu, hau⟩ := Finset.mem_biUnion.1 ha'
                have hult := htag_lt ⟨r, hr⟩ u hu
                exact Finset.Subset.trans (ihr u.val hult u.isLt a hau) (hanc_sub ⟨r, hr⟩ u hu)
          exact htrans root.val root.isLt ⟨idx, hi⟩ hmem (hanc_sub ⟨idx, hi⟩ k hkpar (hanc_self k))
        rw [hspec, map_add, ih j.val hjlt j.isLt hjS x hx, ih k.val hklt k.isLt hkS x hx, add_zero]
      | mul j v =>
        rw [htag] at hspec
        have hjpar : j ∈ parents (tag ⟨idx, hi⟩) := by simp [htag, parents]
        have hjlt : j.val < idx := htag_lt ⟨idx, hi⟩ j hjpar
        have hjS : j ∈ S := by
          have htrans : ∀ r : ℕ, ∀ (hr : r < t), ∀ a ∈ anc ⟨r, hr⟩, anc a ⊆ anc ⟨r, hr⟩ := by
            intro r
            induction r using Nat.strong_induction_on with
            | ind r ihr =>
              intro hr a ha
              rw [hanc_eq ⟨r, hr⟩] at ha
              rcases Finset.mem_insert.1 ha with rfl | ha'
              · exact fun _ h => h
              · obtain ⟨u, hu, hau⟩ := Finset.mem_biUnion.1 ha'
                have hult := htag_lt ⟨r, hr⟩ u hu
                exact Finset.Subset.trans (ihr u.val hult u.isLt a hau) (hanc_sub ⟨r, hr⟩ u hu)
          exact htrans root.val root.isLt ⟨idx, hi⟩ hmem (hanc_sub ⟨idx, hi⟩ j hjpar (hanc_self j))
        rw [hspec, map_mul, ih j.val hjlt j.isLt hjS x hx, mul_zero]
  have hincomp : ¬ ∃ x : Fin n → Bool, ∀ q ∈ H,
      x (left q.1) = q.2 → x (right q.1) = (q.2 ^^ sign q.1) := by
    rintro ⟨x, hx⟩
    have h0 := hsound root.val root.isLt (hanc_self root) x hx
    rw [hroot_eq, map_one] at h0
    exact absurd h0 (by decide)
  obtain ⟨D, ⟨hDodd, hDeven⟩, hDcard⟩ := unsat_core_unit left right sign H hincomp
  obtain ⟨k, hkD, hnegk⟩ := oddSet_implies_negative left right sign D.card D le_rfl hDodd hDeven
  have hgk : g ≤ k := by
    by_contra hlt
    exact hmin k (by omega) hnegk
  have hHcard : H.card ≤ (S.filter (fun i => isAxTag (tag i))).card := by
    have h1 : H.card ≤ ∑ i ∈ S,
        (match tag i with | .ax e a => ({(e, a)} : Finset (Fin m × Bool)) | _ => ∅).card :=
      Finset.card_biUnion_le
    have h2 : ∑ i ∈ S, (match tag i with | .ax e a => ({(e, a)} : Finset (Fin m × Bool)) | _ => ∅).card =
        (S.filter (fun i => isAxTag (tag i))).card := by
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      cases tag i <;> simp [isAxTag]
    omega
  have hS_er : S.card - 1 ≤
      2 * (S.filter (fun i => isAddTag (tag i))).card +
      (S.filter (fun i => isMulTag (tag i))).card := by
    have h1 : S.card - 1 = (S.erase root).card := by
      rw [Finset.card_erase_of_mem (hanc_self root)]
    have h2 : (S.erase root).card ≤ (S.biUnion (fun w => parents (tag w))).card :=
      Finset.card_le_card (hanc_cover root.val root.isLt)
    have h3 : (S.biUnion (fun w => parents (tag w))).card ≤ ∑ w ∈ S, (parents (tag w)).card :=
      Finset.card_biUnion_le
    have h4 : ∑ w ∈ S, (parents (tag w)).card ≤
        ∑ w ∈ S, (if isAddTag (tag w) then 2 else if isMulTag (tag w) then 1 else 0) :=
      Finset.sum_le_sum fun w _ => parents_card_le (tag w)
    have h5 : ∑ w ∈ S, (if isAddTag (tag w) then 2 else if isMulTag (tag w) then 1 else 0) =
        2 * (S.filter (fun i => isAddTag (tag i))).card +
        (S.filter (fun i => isMulTag (tag i))).card := by
      rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      cases tag w <;> simp [isAddTag, isMulTag]
    omega
  have hS_part : (S.filter (fun i => isAxTag (tag i))).card +
      (S.filter (fun i => isAddTag (tag i))).card +
      (S.filter (fun i => isMulTag (tag i))).card ≤ S.card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have hle : ∑ i ∈ S, ((if isAxTag (tag i) = true then 1 else 0) +
        (if isAddTag (tag i) = true then 1 else 0) +
        (if isMulTag (tag i) = true then 1 else 0)) ≤ ∑ _i ∈ S, 1 := by
      refine Finset.sum_le_sum fun i _ => ?_
      cases tag i <;> simp [isAxTag, isAddTag, isMulTag]
    simpa using hle
  have hSt : S.card ≤ t := by
    calc S.card ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_le_card (Finset.subset_univ S)
      _ = t := Finset.card_fin t
  exact ⟨by omega, hd_bound⟩

private lemma legal_backward {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (g : ℕ)
    (hneg : ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m), v 0 = v g ∧
      Odd (((Finset.range g).filter (fun j => sign (edge j) = true)).card) ∧
      ∀ j < g, (v j = left (edge j) ∧ v (j + 1) = right (edge j)) ∨
        (v j = right (edge j) ∧ v (j + 1) = left (edge j)))
    (L d : ℕ) (hL : 4 * g ≤ L + 1) (hd : (if g = 1 then 1 else 2) ≤ d) :
    ∃ (t : ℕ) (p : Fin t → MvPolynomial (Fin n) (ZMod 2)),
      t ≤ L ∧
      ((∃ root, p root = 1) ∧ ∀ i, p i = 0 ∨ (∃ e a, p i = ax left right sign e a) ∨
        (∃ v : Fin n, p i = MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v) ∨
        (∃ j < i, ∃ k < i, p i = p j + p k) ∨
        (∃ j < i, ∃ v : Fin n, p i = MvPolynomial.X v * p j)) ∧
      ∀ i, (p i).totalDegree ≤ d := by
  obtain ⟨v, edge, hclosed, hodd, hedge⟩ := hneg
  have hgpos : 1 ≤ g := by
    by_contra h0
    have hg0 : g = 0 := by omega
    subst hg0
    simp at hodd
  let t : ℕ := 4 * g - 1
  have htL : t ≤ L := by omega
  let prefSign : ℕ → MvPolynomial (Fin n) (ZMod 2) :=
    fun r => ∑ j ∈ Finset.range r, b2zPoly (sign (edge j))
  let p : Fin t → MvPolynomial (Fin n) (ZMod 2) := fun i =>
    if i.val < 2 * g then
      if i.val % 2 = 0 then ax left right sign (edge (i.val / 2)) false
      else ax left right sign (edge (i.val / 2)) true
    else if i.val < 3 * g then
      let j := i.val - 2 * g
      MvPolynomial.X (v j) + MvPolynomial.X (v (j + 1)) + b2zPoly (sign (edge j))
    else
      let k := i.val - 3 * g
      MvPolynomial.X (v 0) + MvPolynomial.X (v (k + 2)) + prefSign (k + 2)
  have hsum_sign : prefSign g = 1 := by
    have hcast : ∀ r, prefSign r =
        MvPolynomial.C (((Finset.range r).filter (fun j => sign (edge j) = true)).card : ZMod 2) := by
      intro r
      induction r with
      | zero => simp [prefSign]
      | succ r ihr =>
        simp only [prefSign, Finset.sum_range_succ, Finset.range_add_one, Finset.filter_insert] at ihr ⊢
        rw [ihr]
        cases hs : sign (edge r)
        · simp [b2zPoly]
        · have hnot : r ∉ (Finset.range r).filter (fun j => sign (edge j) = true) := by
            simp
          simp [b2zPoly, Finset.card_insert_of_notMem hnot]
    rw [hcast g, (zmod2_cast_eq_one_iff_odd _).2 hodd, map_one]
  have hedge_sum : ∀ j < g,
      ax left right sign (edge j) false + ax left right sign (edge j) true =
        MvPolynomial.X (v j) + MvPolynomial.X (v (j + 1)) + b2zPoly (sign (edge j)) := by
    intro j hj
    rw [ax_sum_pair]
    rcases hedge j hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, add_comm (MvPolynomial.X (right (edge j))) _]
  have hdeg_lin : ∀ (u w : Fin n) (c : MvPolynomial (Fin n) (ZMod 2)),
      c.totalDegree ≤ 0 → (MvPolynomial.X u + MvPolynomial.X w + c).totalDegree ≤ 1 := by
    intro u w c hc
    have h1 := MvPolynomial.totalDegree_add (MvPolynomial.X u + MvPolynomial.X w) c
    have h2 := MvPolynomial.totalDegree_add (MvPolynomial.X u : MvPolynomial (Fin n) (ZMod 2)) (MvPolynomial.X w)
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X] at h2
    omega
  have hdeg_b2z : ∀ b : Bool, (b2zPoly (n := n) b).totalDegree ≤ 0 := by
    intro b
    cases b <;> simp [b2zPoly]
  have hdeg_pref : ∀ r : ℕ, (prefSign r).totalDegree ≤ 0 := by
    intro r
    induction r with
    | zero => simp [prefSign]
    | succ r ihr =>
      have hsucc : prefSign (r + 1) = prefSign r + b2zPoly (n := n) (sign (edge r)) :=
        Finset.sum_range_succ _ r
      rw [hsucc]
      have h1 := MvPolynomial.totalDegree_add (prefSign r) (b2zPoly (n := n) (sign (edge r)))
      have h2 := hdeg_b2z (sign (edge r))
      omega
  refine ⟨t, p, htL, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨⟨t - 1, by omega⟩, ?_⟩
    by_cases hg1 : g = 1
    · subst hg1
      have ht1 : t - 1 = 2 := by omega
      have h1 : ¬ (2 < 2 * 1) := by omega
      have h2 : 2 < 3 * 1 := by omega
      have hs0 : sign (edge 0) = true := by
        cases h : sign (edge 0)
        · simp [Finset.range_one, Finset.filter_singleton, h] at hodd
        · rfl
      simp only [p, ht1, h1, h2, ↓reduceIte, Nat.sub_self, zero_add, ← hclosed,
        zmod2_poly_add_self, zero_add, hs0, b2zPoly]
    · have h1 : ¬ (t - 1 < 2 * g) := by omega
      have h2 : ¬ (t - 1 < 3 * g) := by omega
      have hk : t - 1 - 3 * g + 2 = g := by omega
      simp only [p, h1, h2, ↓reduceIte, hk, ← hclosed, zmod2_poly_add_self, zero_add, hsum_sign]
  · intro i
    by_cases h1 : i.val < 2 * g
    · right; left
      by_cases hpar : i.val % 2 = 0
      · exact ⟨edge (i.val / 2), false, by simp [p, h1, hpar]⟩
      · exact ⟨edge (i.val / 2), true, by simp [p, h1, hpar]⟩
    · by_cases h2 : i.val < 3 * g
      · right; right; right; left
        let j := i.val - 2 * g
        have hjlt : j < g := by omega
        refine ⟨⟨2 * j, by omega⟩, by simp [Fin.lt_def]; omega,
          ⟨2 * j + 1, by omega⟩, by simp [Fin.lt_def]; omega, ?_⟩
        have hlt0 : 2 * j < 2 * g := by omega
        have hlt1 : 2 * j + 1 < 2 * g := by omega
        have hm0 : (2 * j) % 2 = 0 := by omega
        have hm1 : ¬ ((2 * j + 1) % 2 = 0) := by omega
        have hd0 : (2 * j) / 2 = j := by omega
        have hd1 : (2 * j + 1) / 2 = j := by omega
        simp only [p, h1, h2, hlt0, hlt1, hm0, hm1, hd0, hd1, ↓reduceIte]
        exact (hedge_sum j hjlt).symm
      · right; right; right; left
        let k := i.val - 3 * g
        by_cases hk0 : k = 0
        · refine ⟨⟨2 * g, by omega⟩, by simp [Fin.lt_def]; omega,
            ⟨2 * g + 1, by omega⟩, by simp [Fin.lt_def]; omega, ?_⟩
          have ha1 : ¬ (2 * g < 2 * g) := by omega
          have ha2 : 2 * g < 3 * g := by omega
          have hb1 : ¬ (2 * g + 1 < 2 * g) := by omega
          have hb2 : 2 * g + 1 < 3 * g := by omega
          simp only [p, h1, h2, ha1, ha2, hb1, hb2, ↓reduceIte]
          have hsub0 : 2 * g - 2 * g = 0 := by omega
          have hsub1 : 2 * g + 1 - 2 * g = 1 := by omega
          have hk0' : i.val - 3 * g = 0 := hk0
          rw [hsub0, hsub1, hk0']
          simp only [prefSign, zero_add, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
          calc MvPolynomial.X (v 0) + MvPolynomial.X (v 2) +
                (b2zPoly (sign (edge 0)) + b2zPoly (sign (edge 1)))
              = MvPolynomial.X (v 0) + MvPolynomial.X (v 2) +
                (b2zPoly (sign (edge 0)) + b2zPoly (sign (edge 1))) +
                (MvPolynomial.X (v 1) + MvPolynomial.X (v 1)) := by
                  rw [zmod2_poly_add_self, add_zero]
            _ = (MvPolynomial.X (v 0) + MvPolynomial.X (v 1) + b2zPoly (sign (edge 0))) +
                (MvPolynomial.X (v 1) + MvPolynomial.X (v 2) + b2zPoly (sign (edge 1))) := by ring
        · refine ⟨⟨i.val - 1, by omega⟩, by simp [Fin.lt_def]; omega,
            ⟨2 * g + k + 1, by omega⟩, by simp [Fin.lt_def]; omega, ?_⟩
          have ha1 : ¬ (i.val - 1 < 2 * g) := by omega
          have ha2 : ¬ (i.val - 1 < 3 * g) := by omega
          have hb1 : ¬ (2 * g + k + 1 < 2 * g) := by omega
          have hb2 : 2 * g + k + 1 < 3 * g := by omega
          simp only [p, h1, h2, ha1, ha2, hb1, hb2, ↓reduceIte]
          have hka : i.val - 1 - 3 * g + 2 = k + 1 := by omega
          have hkb : 2 * g + k + 1 - 2 * g = k + 1 := by omega
          have hkc : i.val - 3 * g = k := rfl
          rw [hka, hkb, hkc]
          have hps : prefSign (k + 2) = prefSign (k + 1) + b2zPoly (sign (edge (k + 1))) :=
            Finset.sum_range_succ _ (k + 1)
          rw [hps]
          calc MvPolynomial.X (v 0) + MvPolynomial.X (v (k + 2)) +
                (prefSign (k + 1) + b2zPoly (sign (edge (k + 1))))
              = MvPolynomial.X (v 0) + MvPolynomial.X (v (k + 2)) +
                (prefSign (k + 1) + b2zPoly (sign (edge (k + 1)))) +
                (MvPolynomial.X (v (k + 1)) + MvPolynomial.X (v (k + 1))) := by
                  rw [zmod2_poly_add_self, add_zero]
            _ = (MvPolynomial.X (v 0) + MvPolynomial.X (v (k + 1)) + prefSign (k + 1)) +
                (MvPolynomial.X (v (k + 1)) + MvPolynomial.X (v (k + 1 + 1)) +
                  b2zPoly (sign (edge (k + 1)))) := by ring
  · intro i
    by_cases h1 : i.val < 2 * g
    · by_cases hg1 : g = 1
      · subst hg1
        simp only [↓reduceIte] at hd
        have hi0 : i.val / 2 = 0 := by omega
        have hloop : left (edge 0) = right (edge 0) ∧ sign (edge 0) = true := by
          have hs0 : sign (edge 0) = true := by
            cases h : sign (edge 0)
            · simp [Finset.range_one, Finset.filter_singleton, h] at hodd
            · rfl
          rcases hedge 0 (by omega) with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact ⟨by rw [← ha, ← hb, hclosed], hs0⟩
          · exact ⟨by rw [← ha, ← hb, hclosed], hs0⟩
        by_cases hpar : i.val % 2 = 0
        · simp only [p, h1, hpar, hi0, ↓reduceIte]
          have hle := totalDegree_ax_le left right sign (edge 0) false
          simp only [hloop, and_self, ↓reduceIte] at hle
          omega
        · simp only [p, h1, hpar, hi0, ↓reduceIte]
          have hle := totalDegree_ax_le left right sign (edge 0) true
          simp only [hloop, and_self, ↓reduceIte] at hle
          omega
      · simp only [hg1, ↓reduceIte] at hd
        by_cases hpar : i.val % 2 = 0
        · simp only [p, h1, hpar, ↓reduceIte]
          have hle := totalDegree_ax_le left right sign (edge (i.val / 2)) false
          split_ifs at hle <;> omega
        · simp only [p, h1, hpar, ↓reduceIte]
          have hle := totalDegree_ax_le left right sign (edge (i.val / 2)) true
          split_ifs at hle <;> omega
    · by_cases h2 : i.val < 3 * g
      · simp only [p, h1, h2, ↓reduceIte]
        have hle := hdeg_lin (v (i.val - 2 * g)) (v (i.val - 2 * g + 1))
          (b2zPoly (sign (edge (i.val - 2 * g)))) (hdeg_b2z _)
        split_ifs at hd <;> omega
      · simp only [p, h1, h2, ↓reduceIte]
        have hle := hdeg_lin (v 0) (v (i.val - 3 * g + 2))
          (prefSign (i.val - 3 * g + 2)) (hdeg_pref _)
        split_ifs at hd <;> omega

end PEqualNP.Outside.L_pcx_265_aux

theorem PEqualNP.Outside.L_pcx_265 :
  ∀ (n m : ℕ) (left right : Fin m → Fin n) (sign : Fin m → Bool),
    let cl := fun (e : Fin m) (a : Bool) =>
      ({(left e, !a), (right e, a ^^ sign e)} : PEqualNP.ProofComplexity.Clause (Fin n))
    let negative := fun k : ℕ =>
      ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m), v 0 = v k ∧
        Odd (((Finset.range k).filter (fun j => sign (edge j) = true)).card) ∧
        ∀ j < k, (v j = left (edge j) ∧ v (j+1) = right (edge j)) ∨
          (v j = right (edge j) ∧ v (j+1) = left (edge j))
    let P := MvPolynomial (Fin n) (ZMod 2)
    let ax := fun (e : Fin m) (a : Bool) => PEqualNP.ProofComplexity.clausePoly (cl e a)
    let legal := fun (t : ℕ) (p : Fin t → P) =>
      (∃ root, p root = 1) ∧ ∀ i, p i = 0 ∨ (∃ e a, p i = ax e a) ∨
        (∃ v : Fin n, p i = MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v) ∨
        (∃ j < i, ∃ k < i, p i = p j + p k) ∨
        (∃ j < i, ∃ v : Fin n, p i = MvPolynomial.X v * p j)
    ∀ g : ℕ, negative g → (∀ k < g, ¬ negative k) →
      ∀ L d : ℕ,
        (∃ (t : ℕ) (p : Fin t → P), t ≤ L ∧ legal t p ∧ ∀ i, (p i).totalDegree ≤ d) ↔
        4*g ≤ L+1 ∧ (if g = 1 then 1 else 2) ≤ d := by
  intro n m left right sign cl negative P ax legal g hneg hmin L d
  constructor
  · rintro ⟨t, p, htL, ⟨hroot, hstep⟩, hdeg⟩
    have hgpos : 1 ≤ g := by
      by_contra h0
      have hg0 : g = 0 := by omega
      subst hg0
      obtain ⟨_, _, _, hodd, _⟩ := hneg
      simp at hodd
    exact PEqualNP.Outside.L_pcx_265_aux.legal_forward left right sign g hgpos hmin L d t p htL hroot hstep hdeg
  · rintro ⟨hL, hd⟩
    exact PEqualNP.Outside.L_pcx_265_aux.legal_backward left right sign g hneg L d hL hd
