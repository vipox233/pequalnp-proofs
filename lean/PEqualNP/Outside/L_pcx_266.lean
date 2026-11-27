import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_266_aux

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


private lemma pairwiseDisjoint_of_card_biUnion_eq_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → Finset β)
    (hsum : (S.biUnion f).card = ∑ w ∈ S, (f w).card) :
    (S : Set α).PairwiseDisjoint f := by
  intro w1 hw1 w2 hw2 hne
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx1 hx2
  have hw1_mem : w1 ∈ S := hw1
  have hw2_mem : w2 ∈ S := hw2
  have hw2_er : w2 ∈ S.erase w1 := Finset.mem_erase.2 ⟨hne.symm, hw2_mem⟩
  let R : Finset α := (S.erase w1).erase w2
  have hS_eq : S = insert w1 (insert w2 R) := by
    dsimp only [R]
    rw [Finset.insert_erase hw2_er, Finset.insert_erase hw1_mem]
  have hw1_not : w1 ∉ insert w2 R := by
    simp [R, hne]
  have hw2_not : w2 ∉ R := by
    simp [R]
  have hcard_sum : ∑ w ∈ S, (f w).card = (f w1).card + (f w2).card + ∑ w ∈ R, (f w).card := by
    conv_lhs => rw [hS_eq]
    rw [Finset.sum_insert hw1_not, Finset.sum_insert hw2_not, add_assoc]
  have hbiU_eq : S.biUnion f = (f w1 ∪ f w2) ∪ R.biUnion f := by
    conv_lhs => rw [hS_eq]
    rw [Finset.biUnion_insert, Finset.biUnion_insert, Finset.union_assoc]
  have hinter_pos : 1 ≤ (f w1 ∩ f w2).card :=
    Finset.card_pos.2 ⟨x, Finset.mem_inter.2 ⟨hx1, hx2⟩⟩
  have hpair := Finset.card_union_add_card_inter (f w1) (f w2)
  have h1 : (S.biUnion f).card ≤ (f w1 ∪ f w2).card + (R.biUnion f).card := by
    rw [hbiU_eq]
    exact Finset.card_union_le (f w1 ∪ f w2) (R.biUnion f)
  have h2 : (R.biUnion f).card ≤ ∑ w ∈ R, (f w).card := Finset.card_biUnion_le
  omega

private lemma poly_coeff_sum {n : ℕ} {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → MvPolynomial (Fin n) (ZMod 2)) (s : Fin n →₀ ℕ) :
    (∑ i ∈ S, f i).coeff s = ∑ i ∈ S, (f i).coeff s := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, poly_coeff_add, ih]

private lemma coeff_ax_quad {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (hsimple_lt : ∀ index, left index < right index)
    (hsimple_inj : Function.Injective (fun index => (left index, right index)))
    (e e' : Fin m) (a' : Bool) :
    (ax left right sign e' a').coeff
      (Finsupp.single (left e) 1 + Finsupp.single (right e) 1) =
      if e' = e then 1 else 0 := by
  let s : Fin n →₀ ℕ := Finsupp.single (left e) 1 + Finsupp.single (right e) 1
  have hs_sum : s.sum (fun _ k => k) = 2 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
  have hne0 : (0 : Fin n →₀ ℕ) ≠ s := by
    intro h
    have := congrArg (fun t : Fin n →₀ ℕ => t.sum fun _ k => k) h
    simp [hs_sum] at this
  have hne1 : ∀ v : Fin n, Finsupp.single v 1 ≠ s := by
    intro v h
    have := congrArg (fun t : Fin n →₀ ℕ => t.sum fun _ k => k) h
    simp [hs_sum] at this
  have hc1 : (1 : MvPolynomial (Fin n) (ZMod 2)).coeff s = 0 := by
    rw [MvPolynomial.coeff_one]
    simp only [hne0, ↓reduceIte]
  have hcx : ∀ v : Fin n, (MvPolynomial.X v : MvPolynomial (Fin n) (ZMod 2)).coeff s = 0 := by
    intro v
    rw [MvPolynomial.coeff_X]
    simp only [hne1 v, ↓reduceIte]
  have hs_eq : Finsupp.single (left e') 1 + Finsupp.single (right e') 1 = s ↔ e' = e := by
    constructor
    · intro h
      have huv : left e < right e := hsimple_lt e
      have huv' : left e' < right e' := hsimple_lt e'
      have hu' : left e' = left e ∨ left e' = right e := by
        by_contra hno
        push Not at hno
        have hval := congrFun (congrArg DFunLike.coe h) (left e')
        simp [s, Finsupp.single_apply, Ne.symm hno.1, Ne.symm hno.2] at hval
      have hv' : right e' = left e ∨ right e' = right e := by
        by_contra hno
        push Not at hno
        have hval := congrFun (congrArg DFunLike.coe h) (right e')
        simp [s, Finsupp.single_apply, Ne.symm hno.1, Ne.symm hno.2] at hval
      have hpair : (left e', right e') = (left e, right e) := by
        rcases hu' with h1 | h1 <;> rcases hv' with h2 | h2
        · exfalso; rw [h1, h2] at huv'; exact lt_irrefl _ huv'
        · exact Prod.ext h1 h2
        · exfalso; rw [h1, h2] at huv'; exact lt_asymm huv huv'
        · exfalso; rw [h1, h2] at huv'; exact lt_irrefl _ huv'
      exact hsimple_inj hpair
    · rintro rfl
      rfl
  have hcuv : (MvPolynomial.X (left e') * MvPolynomial.X (right e') : MvPolynomial (Fin n) (ZMod 2)).coeff s =
      if e' = e then 1 else 0 := by
    have hmul : (MvPolynomial.X (left e') * MvPolynomial.X (right e') : MvPolynomial (Fin n) (ZMod 2)) =
        MvPolynomial.monomial (Finsupp.single (left e') 1 + Finsupp.single (right e') 1) 1 := by
      simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, mul_one]
    rw [hmul, MvPolynomial.coeff_monomial]
    simp only [hs_eq]
  have hne_pair : (left e', !a') ≠ (right e', a' ^^ sign e') :=
    fun h => ne_of_lt (hsimple_lt e') (congrArg Prod.fst h)
  rw [ax_eq_distinct _ _ _ e' a' hne_pair]
  change (litPoly (left e', !a') * litPoly (right e', a' ^^ sign e')).coeff s = _
  cases !a' <;> cases (a' ^^ sign e')
  · simp only [litPoly, Bool.false_eq_true, ↓reduceIte]
    exact hcuv
  · simp only [litPoly, Bool.false_eq_true, ↓reduceIte, mul_add, mul_one]
    rw [poly_coeff_add, hcx (left e'), hcuv, zero_add]
  · simp only [litPoly, Bool.false_eq_true, ↓reduceIte, add_mul, one_mul]
    rw [poly_coeff_add, hcx (right e'), hcuv, zero_add]
  · have hexp : ((1 : MvPolynomial (Fin n) (ZMod 2)) + MvPolynomial.X (left e')) *
        (1 + MvPolynomial.X (right e')) =
        1 + MvPolynomial.X (left e') + MvPolynomial.X (right e') +
        MvPolynomial.X (left e') * MvPolynomial.X (right e') := by ring
    simp only [litPoly, ↓reduceIte, hexp]
    rw [poly_coeff_add, poly_coeff_add, poly_coeff_add, hc1, hcx (left e'), hcx (right e'), hcuv,
      zero_add, zero_add, zero_add]

private lemma coeff_edge_lin {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (e : Fin m) (v : Fin n) :
    (MvPolynomial.X (left e) + MvPolynomial.X (right e) + b2zPoly (sign e) :
      MvPolynomial (Fin n) (ZMod 2)).coeff (Finsupp.single v 1) = inc left right e v := by
  have hne : (0 : Fin n →₀ ℕ) ≠ Finsupp.single v 1 := by
    intro h
    have := congrFun (congrArg DFunLike.coe h) v
    simp at this
  have hcb : (b2zPoly (n := n) (sign e)).coeff (Finsupp.single v 1) = 0 := by
    cases sign e
    · simp [b2zPoly]
    · simp only [b2zPoly, ↓reduceIte, MvPolynomial.coeff_one, hne, ↓reduceIte]
  have hsingle : ∀ u : Fin n, Finsupp.single u 1 = Finsupp.single v 1 ↔ u = v := by
    intro u
    constructor
    · intro h
      by_contra huv
      have := congrFun (congrArg DFunLike.coe h) u
      simp [huv] at this
    · rintro rfl; rfl
  rw [poly_coeff_add, poly_coeff_add, MvPolynomial.coeff_X, MvPolynomial.coeff_X, hcb, add_zero]
  simp only [hsingle, inc]

private lemma coeff_edge_const {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (e : Fin m) :
    (MvPolynomial.X (left e) + MvPolynomial.X (right e) + b2zPoly (sign e) :
      MvPolynomial (Fin n) (ZMod 2)).coeff 0 = b2z (sign e) := by
  have hne : ∀ u : Fin n, Finsupp.single u 1 ≠ (0 : Fin n →₀ ℕ) := by
    intro u h
    have := congrFun (congrArg DFunLike.coe h) u
    simp at this
  rw [poly_coeff_add, poly_coeff_add, MvPolynomial.coeff_X, MvPolynomial.coeff_X]
  simp only [hne, ↓reduceIte, zero_add]
  cases sign e <;> simp [b2zPoly, b2z]

private lemma shortest_pc_profile {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (hsimple_lt : ∀ index, left index < right index)
    (hsimple_inj : Function.Injective (fun index => (left index, right index)))
    (g : ℕ)
    (hneg : ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m), v 0 = v g ∧
      Odd (((Finset.range g).filter (fun j => sign (edge j) = true)).card) ∧
      ∀ j < g, (v j = left (edge j) ∧ v (j + 1) = right (edge j)) ∨
        (v j = right (edge j) ∧ v (j + 1) = left (edge j)))
    (hmin : ∀ k < g, ¬ ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m), v 0 = v k ∧
      Odd (((Finset.range k).filter (fun j => sign (edge j) = true)).card) ∧
      ∀ j < k, (v j = left (edge j) ∧ v (j + 1) = right (edge j)) ∨
        (v j = right (edge j) ∧ v (j + 1) = left (edge j)))
    (t : ℕ) (p : Fin t → MvPolynomial (Fin n) (ZMod 2))
    (ht4g : t + 1 = 4 * g)
    (hroot : ∃ root, p root = 1)
    (hstep : ∀ i : Fin t, p i = 0 ∨ (∃ e a, p i = ax left right sign e a) ∨
      (∃ v : Fin n, p i = MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v) ∨
      (∃ j < i, ∃ k < i, p i = p j + p k) ∨
      (∃ j < i, ∃ v : Fin n, p i = MvPolynomial.X v * p j)) :
    ∃ D : Finset (Fin m), D.card = g ∧
      (Odd ((D.filter (fun signed => sign signed = true)).card) ∧
        ∀ v : Fin n, Even ((D.filter (fun tailEdge => left tailEdge = v)).card +
          (D.filter (fun headEdge => right headEdge = v)).card)) ∧
      (∀ e a, (∃ i, p i = ax left right sign e a) ↔ e ∈ D) ∧
      ∀ i, (∃ e ∈ D, ∃ a, p i = ax left right sign e a) ∨
        ∃ j < i, ∃ k < i, p i = p j + p k := by
  classical
  have hgpos : 1 ≤ g := by
    by_contra h0
    have hg0 : g = 0 := by omega
    subst hg0
    obtain ⟨_, _, _, hodd, _⟩ := hneg
    simp at hodd
  obtain ⟨root, hroot_eq⟩ := hroot
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
  have hanc_trans : ∀ r : ℕ, ∀ (hr : r < t), ∀ a ∈ anc ⟨r, hr⟩, anc a ⊆ anc ⟨r, hr⟩ := by
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
  let axSing : Fin t → Finset (Fin m × Bool) := fun i =>
    match tag i with
    | .ax e a => {(e, a)}
    | _ => ∅
  let H : Finset (Fin m × Bool) := S.biUnion axSing
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
          simp [axSing, htag]
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
        have hjS : j ∈ S := hanc_trans root.val root.isLt ⟨idx, hi⟩ hmem (hanc_sub ⟨idx, hi⟩ j hjpar (hanc_self j))
        have hkS : k ∈ S := hanc_trans root.val root.isLt ⟨idx, hi⟩ hmem (hanc_sub ⟨idx, hi⟩ k hkpar (hanc_self k))
        rw [hspec, map_add, ih j.val hjlt j.isLt hjS x hx, ih k.val hklt k.isLt hkS x hx, add_zero]
      | mul j v =>
        rw [htag] at hspec
        have hjpar : j ∈ parents (tag ⟨idx, hi⟩) := by simp [htag, parents]
        have hjlt : j.val < idx := htag_lt ⟨idx, hi⟩ j hjpar
        have hjS : j ∈ S := hanc_trans root.val root.isLt ⟨idx, hi⟩ hmem (hanc_sub ⟨idx, hi⟩ j hjpar (hanc_self j))
        rw [hspec, map_mul, ih j.val hjlt j.isLt hjS x hx, mul_zero]
  have hincomp : ¬ ∃ x : Fin n → Bool, ∀ q ∈ H,
      x (left q.1) = q.2 → x (right q.1) = (q.2 ^^ sign q.1) := by
    rintro ⟨x, hx⟩
    have h0 := hsound root.val root.isLt (hanc_self root) x hx
    rw [hroot_eq, map_one] at h0
    exact absurd h0 (by decide)
  obtain ⟨D0, ⟨hD0odd, hD0even⟩, hD0card⟩ := unsat_core_unit left right sign H hincomp
  obtain ⟨k0, hk0D, hnegk0⟩ := oddSet_implies_negative left right sign D0.card D0 le_rfl hD0odd hD0even
  have hgk0 : g ≤ k0 := by
    by_contra hlt
    exact hmin k0 (by omega) hnegk0
  have hH_sum_le : H.card ≤ ∑ i ∈ S, (axSing i).card := Finset.card_biUnion_le
  have haxSing_sum : ∑ i ∈ S, (axSing i).card = (S.filter (fun i => isAxTag (tag i))).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases htag : tag i <;> simp [axSing, isAxTag, htag]
  have hS_er1 : S.card - 1 = (S.erase root).card := by
    rw [Finset.card_erase_of_mem (hanc_self root)]
  have hS_er2 : (S.erase root).card ≤ (S.biUnion (fun w => parents (tag w))).card :=
    Finset.card_le_card (hanc_cover root.val root.isLt)
  have hS_er3 : (S.biUnion (fun w => parents (tag w))).card ≤ ∑ w ∈ S, (parents (tag w)).card :=
    Finset.card_biUnion_le
  have hS_er4 : ∑ w ∈ S, (parents (tag w)).card ≤
      ∑ w ∈ S, (if isAddTag (tag w) then 2 else if isMulTag (tag w) then 1 else 0) :=
    Finset.sum_le_sum fun w _ => parents_card_le (tag w)
  have hS_er5 : ∑ w ∈ S, (if isAddTag (tag w) then 2 else if isMulTag (tag w) then 1 else 0) =
      2 * (S.filter (fun i => isAddTag (tag i))).card +
      (S.filter (fun i => isMulTag (tag i))).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    cases tag w <;> simp [isAddTag, isMulTag]
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
  have hScard : S.card = t := by omega
  have hSuniv : S = Finset.univ := Finset.eq_univ_of_card S (by rw [Fintype.card_fin]; exact hScard)
  have hHcard_eq : H.card = 2 * g := by omega
  have hAx_card : (S.filter (fun i => isAxTag (tag i))).card = 2 * g := by omega
  have hAdd_card : (S.filter (fun i => isAddTag (tag i))).card = 2 * g - 1 := by omega
  have hMul_card : (S.filter (fun i => isMulTag (tag i))).card = 0 := by omega
  have hH_biU_eq : H.card = ∑ i ∈ S, (axSing i).card := by omega
  have hpar_biU_eq : (S.biUnion (fun w => parents (tag w))).card = ∑ w ∈ S, (parents (tag w)).card := by omega
  have hpar_sum_eq : ∑ w ∈ S, (parents (tag w)).card =
      ∑ w ∈ S, (if isAddTag (tag w) then 2 else if isMulTag (tag w) then 1 else 0) := by omega
  have hpar_er_eq : (S.erase root).card = (S.biUnion (fun w => parents (tag w))).card := by omega
  have hpar_disj : (S : Set (Fin t)).PairwiseDisjoint (fun w => parents (tag w)) :=
    pairwiseDisjoint_of_card_biUnion_eq_sum S (fun w => parents (tag w)) hpar_biU_eq
  have hax_disj : (S : Set (Fin t)).PairwiseDisjoint axSing :=
    pairwiseDisjoint_of_card_biUnion_eq_sum S axSing hH_biU_eq
  have hpar_eq_erase : S.biUnion (fun w => parents (tag w)) = S.erase root :=
    (Finset.eq_of_subset_of_card_le (hanc_cover root.val root.isLt) (le_of_eq hpar_er_eq.symm)).symm
  have hpar_pt : ∀ w ∈ S, (parents (tag w)).card =
      if isAddTag (tag w) then 2 else if isMulTag (tag w) then 1 else 0 :=
    (Finset.sum_eq_sum_iff_of_le (fun w _ => parents_card_le (tag w))).1 hpar_sum_eq
  have hax_or_add : ∀ i : Fin t, isAxTag (tag i) = true ∨ isAddTag (tag i) = true := by
    have hdisj : Disjoint (S.filter (fun i => isAxTag (tag i))) (S.filter (fun i => isAddTag (tag i))) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      have ha1 := (Finset.mem_filter.1 h1).2
      have ha2 := (Finset.mem_filter.1 h2).2
      cases htag : tag i <;> simp [isAxTag, isAddTag, htag] at ha1 ha2
    have hunion : S.filter (fun i => isAxTag (tag i)) ∪ S.filter (fun i => isAddTag (tag i)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_union_of_disjoint hdisj, hAx_card, hAdd_card, Fintype.card_fin]
      omega
    intro i
    have hi : i ∈ S.filter (fun i => isAxTag (tag i)) ∪ S.filter (fun i => isAddTag (tag i)) := by
      rw [hunion]; exact Finset.mem_univ i
    rcases Finset.mem_union.1 hi with h1 | h2
    · left; exact (Finset.mem_filter.1 h1).2
    · right; exact (Finset.mem_filter.1 h2).2
  have hsum_parents : ∑ w ∈ S, ∑ u ∈ parents (tag w), p u =
      ∑ w ∈ S.filter (fun i => isAddTag (tag i)), p w := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hspec := htag_eq w
    have hpt := hpar_pt w hw
    cases htag : tag w with
    | zero => simp [parents, isAddTag]
    | ax e a => simp [parents, isAddTag]
    | bool v => simp [parents, isAddTag]
    | mul j v =>
      exfalso
      have hmul0 : w ∉ S.filter (fun i => isMulTag (tag i)) := by
        rw [Finset.card_eq_zero.1 hMul_card]
        simp
      exact hmul0 (Finset.mem_filter.2 ⟨hw, by simp [htag, isMulTag]⟩)
    | add j k =>
      rw [htag] at hspec hpt
      simp only [parents, isAddTag, ↓reduceIte] at hpt ⊢
      have hjk : j ≠ k := by
        intro heq
        subst heq
        simp at hpt
      rw [Finset.sum_pair hjk, hspec]
  have hsum_er_eq : ∑ u ∈ S.erase root, p u = ∑ w ∈ S.filter (fun i => isAddTag (tag i)), p w := by
    rw [← hpar_eq_erase, Finset.sum_biUnion hpar_disj, hsum_parents]
  have hsum_all_1 : ∑ u ∈ S, p u = p root + ∑ w ∈ S.filter (fun i => isAddTag (tag i)), p w := by
    rw [← Finset.add_sum_erase S p (hanc_self root), hsum_er_eq]
  have hsum_all_2 : ∑ u ∈ S, p u =
      ∑ i ∈ S.filter (fun i => isAxTag (tag i)), p i +
      ∑ w ∈ S.filter (fun i => isAddTag (tag i)), p w := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hax_or_add i with h1 | h2
    · cases htag : tag i <;> simp [isAxTag, isAddTag, htag] at h1 ⊢
    · cases htag : tag i <;> simp [isAxTag, isAddTag, htag] at h2 ⊢
  have hroot_eq_ax : p root = ∑ i ∈ S.filter (fun i => isAxTag (tag i)), p i := by
    have h1 := hsum_all_1.symm.trans hsum_all_2
    exact add_right_cancel h1
  have hsumH_eq_ax : ∑ q ∈ H, ax left right sign q.1 q.2 =
      ∑ i ∈ S.filter (fun i => isAxTag (tag i)), p i := by
    change ∑ q ∈ S.biUnion axSing, ax left right sign q.1 q.2 = _
    rw [Finset.sum_biUnion hax_disj, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hspec := htag_eq i
    cases htag : tag i with
    | zero => simp [axSing, isAxTag, htag]
    | bool v => simp [axSing, isAxTag, htag]
    | add j k => simp [axSing, isAxTag, htag]
    | mul j v => simp [axSing, isAxTag, htag]
    | ax e a =>
      rw [htag] at hspec
      simp [axSing, isAxTag, htag, hspec]
  have h1_eq_sumH : (1 : MvPolynomial (Fin n) (ZMod 2)) = ∑ q ∈ H, ax left right sign q.1 q.2 := by
    rw [← hroot_eq, hroot_eq_ax, hsumH_eq_ax]
  have hpair_iff : ∀ e : Fin m, (e, false) ∈ H ↔ (e, true) ∈ H := by
    intro e
    let s : Fin n →₀ ℕ := Finsupp.single (left e) 1 + Finsupp.single (right e) 1
    have hs_sum : s.sum (fun _ k => k) = 2 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      simp
    have hne0 : (0 : Fin n →₀ ℕ) ≠ s := by
      intro h
      have := congrArg (fun t : Fin n →₀ ℕ => t.sum fun _ k => k) h
      simp [hs_sum] at this
    have hc_lhs : (1 : MvPolynomial (Fin n) (ZMod 2)).coeff s = 0 := by
      rw [MvPolynomial.coeff_one]
      simp only [hne0, ↓reduceIte]
    have hc_rhs : (∑ q ∈ H, ax left right sign q.1 q.2).coeff s =
        ((H.filter (fun q => q.1 = e)).card : ZMod 2) := by
      rw [poly_coeff_sum]
      calc ∑ q ∈ H, (ax left right sign q.1 q.2).coeff s
          = ∑ q ∈ H, if q.1 = e then (1 : ZMod 2) else 0 :=
              Finset.sum_congr rfl fun q _ => coeff_ax_quad left right sign hsimple_lt hsimple_inj e q.1 q.2
        _ = ((H.filter (fun q => q.1 = e)).card : ZMod 2) := by
              simp [Finset.sum_boole]
    have hev_card : Even (H.filter (fun q => q.1 = e)).card := by
      rw [← zmod2_cast_eq_zero_iff_even, ← hc_rhs, ← h1_eq_sumH, hc_lhs]
    have hsub_pair : H.filter (fun q => q.1 = e) ⊆ {(e, false), (e, true)} := by
      intro q hq
      have hqe : q.1 = e := (Finset.mem_filter.1 hq).2
      cases hb : q.2
      · simp [Finset.mem_insert, Prod.ext_iff, hqe, hb]
      · simp [Finset.mem_insert, Prod.ext_iff, hqe, hb]
    have hle2 : (H.filter (fun q => q.1 = e)).card ≤ 2 :=
      le_trans (Finset.card_le_card hsub_pair) Finset.card_le_two
    have h0or2 : (H.filter (fun q => q.1 = e)).card = 0 ∨ (H.filter (fun q => q.1 = e)).card = 2 := by
      obtain ⟨r, hr⟩ := hev_card
      omega
    rcases h0or2 with h0 | h2
    · have hempty : H.filter (fun q => q.1 = e) = ∅ := Finset.card_eq_zero.1 h0
      have hf : (e, false) ∉ H := fun hm => by
        have : (e, false) ∈ H.filter (fun q => q.1 = e) := Finset.mem_filter.2 ⟨hm, rfl⟩
        rw [hempty] at this
        exact Finset.notMem_empty _ this
      have ht : (e, true) ∉ H := fun hm => by
        have : (e, true) ∈ H.filter (fun q => q.1 = e) := Finset.mem_filter.2 ⟨hm, rfl⟩
        rw [hempty] at this
        exact Finset.notMem_empty _ this
      exact ⟨fun h => absurd h hf, fun h => absurd h ht⟩
    · have hpair_card : ({(e, false), (e, true)} : Finset (Fin m × Bool)).card = 2 := by
        rw [Finset.card_pair]
        simp
      have heq_set : H.filter (fun q => q.1 = e) = {(e, false), (e, true)} :=
        Finset.eq_of_subset_of_card_le hsub_pair (by omega)
      have hf : (e, false) ∈ H := (Finset.mem_filter.1 (heq_set.symm ▸ Finset.mem_insert_self _ _)).1
      have ht : (e, true) ∈ H := (Finset.mem_filter.1 (heq_set.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).1
      exact ⟨fun _ => ht, fun _ => hf⟩
  let D : Finset (Fin m) := Finset.univ.filter (fun e => (e, false) ∈ H)
  have hH_prod : H = D ×ˢ (Finset.univ : Finset Bool) := by
    ext ⟨e, b⟩
    simp only [D, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    cases b
    · rfl
    · exact (hpair_iff e).symm
  have hD_card : D.card = g := by
    have hprod_card : H.card = D.card * 2 := by
      rw [hH_prod, Finset.card_product, Finset.card_univ, Fintype.card_bool]
    omega
  have h1_eq_sumD : (1 : MvPolynomial (Fin n) (ZMod 2)) =
      ∑ e ∈ D, (MvPolynomial.X (left e) + MvPolynomial.X (right e) + b2zPoly (sign e)) := by
    rw [h1_eq_sumH, hH_prod, Finset.sum_product]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Fintype.sum_bool]
    rw [add_comm, ax_sum_pair]
  have hD_odd : Odd ((D.filter (fun signed => sign signed = true)).card) := by
    rw [← zmod2_cast_eq_one_iff_odd, ← sum_b2z_over_finset]
    have h0 := congrArg (fun q : MvPolynomial (Fin n) (ZMod 2) => q.coeff 0) h1_eq_sumD
    rw [MvPolynomial.coeff_one, poly_coeff_sum] at h0
    simp only [↓reduceIte] at h0
    have hrhs : ∑ e ∈ D, (MvPolynomial.X (left e) + MvPolynomial.X (right e) + b2zPoly (sign e) :
        MvPolynomial (Fin n) (ZMod 2)).coeff 0 = ∑ e ∈ D, b2z (sign e) :=
      Finset.sum_congr rfl fun e _ => coeff_edge_const left right sign e
    rw [hrhs] at h0
    exact h0.symm
  have hD_even : ∀ v : Fin n, Even ((D.filter (fun tailEdge => left tailEdge = v)).card +
      (D.filter (fun headEdge => right headEdge = v)).card) := by
    intro v
    rw [← zmod2_cast_eq_zero_iff_even, ← sum_inc_over_finset]
    have hv := congrArg (fun q : MvPolynomial (Fin n) (ZMod 2) => q.coeff (Finsupp.single v 1)) h1_eq_sumD
    have hne : (0 : Fin n →₀ ℕ) ≠ Finsupp.single v 1 := by
      intro h
      have := congrFun (congrArg DFunLike.coe h) v
      simp at this
    rw [MvPolynomial.coeff_one, poly_coeff_sum] at hv
    simp only [hne, ↓reduceIte] at hv
    have hrhs : ∑ e ∈ D, (MvPolynomial.X (left e) + MvPolynomial.X (right e) + b2zPoly (sign e) :
        MvPolynomial (Fin n) (ZMod 2)).coeff (Finsupp.single v 1) = ∑ e ∈ D, inc left right e v :=
      Finset.sum_congr rfl fun e _ => coeff_edge_lin left right sign e v
    rw [hrhs] at hv
    exact hv.symm
  refine ⟨D, hD_card, ⟨hD_odd, hD_even⟩, ?_, ?_⟩
  · intro e a
    constructor
    · rintro ⟨i, hi⟩
      have hne0 : p i ≠ 0 := by
        intro h0
        have hc := congrArg (fun q : MvPolynomial (Fin n) (ZMod 2) =>
          q.coeff (Finsupp.single (left e) 1 + Finsupp.single (right e) 1)) (h0.symm.trans hi)
        rw [coeff_ax_quad left right sign hsimple_lt hsimple_inj e e a] at hc
        simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, ↓reduceIte] at hc
        exact absurd hc (by decide)
      have hex : ∃ e' a', p i = ax left right sign e' a' := ⟨e, a, hi⟩
      have htag_ax : tag i = .ax (Classical.choose hex) (Classical.choose (Classical.choose_spec hex)) := by
        simp only [tag, hne0, ↓reduceDIte, hex]
      let e' := Classical.choose hex
      let a' := Classical.choose (Classical.choose_spec hex)
      have hpe' : p i = ax left right sign e' a' := Classical.choose_spec (Classical.choose_spec hex)
      have heeq : e' = e := by
        have hc := congrArg (fun q : MvPolynomial (Fin n) (ZMod 2) =>
          q.coeff (Finsupp.single (left e) 1 + Finsupp.single (right e) 1)) (hpe'.symm.trans hi)
        rw [coeff_ax_quad left right sign hsimple_lt hsimple_inj e e' a',
          coeff_ax_quad left right sign hsimple_lt hsimple_inj e e a] at hc
        simp only [↓reduceIte] at hc
        by_contra hne
        simp only [hne, ↓reduceIte] at hc
        exact absurd hc (by decide)
      have hmemH : (e', a') ∈ H := by
        refine Finset.mem_biUnion.2 ⟨i, hSuniv.symm ▸ Finset.mem_univ i, ?_⟩
        simp [axSing, htag_ax, e', a']
      rw [heeq, hH_prod, Finset.mem_product] at hmemH
      exact hmemH.1
    · intro heD
      have hmemH : (e, a) ∈ H := by
        rw [hH_prod]
        exact Finset.mem_product.2 ⟨heD, Finset.mem_univ a⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 hmemH
      have hspec := htag_eq i
      cases htag : tag i with
      | zero => simp [axSing, htag] at hi
      | bool v => simp [axSing, htag] at hi
      | add j k => simp [axSing, htag] at hi
      | mul j v => simp [axSing, htag] at hi
      | ax e' a' =>
        simp only [axSing, htag, Finset.mem_singleton, Prod.mk.injEq] at hi
        rw [htag] at hspec
        exact ⟨i, by rw [hspec, hi.1, hi.2]⟩
  · intro i
    have hspec := htag_eq i
    rcases hax_or_add i with hax | hadd
    · cases htag : tag i with
      | zero => simp [isAxTag, htag] at hax
      | bool v => simp [isAxTag, htag] at hax
      | add j k => simp [isAxTag, htag] at hax
      | mul j v => simp [isAxTag, htag] at hax
      | ax e a =>
        rw [htag] at hspec
        have hmemH : (e, a) ∈ H := by
          refine Finset.mem_biUnion.2 ⟨i, hSuniv.symm ▸ Finset.mem_univ i, ?_⟩
          simp [axSing, htag]
        rw [hH_prod, Finset.mem_product] at hmemH
        left
        exact ⟨e, hmemH.1, a, hspec⟩
    · cases htag : tag i with
      | zero => simp [isAddTag, htag] at hadd
      | bool v => simp [isAddTag, htag] at hadd
      | ax e a => simp [isAddTag, htag] at hadd
      | mul j v => simp [isAddTag, htag] at hadd
      | add j k =>
        rw [htag] at hspec
        have hjlt : j < i := htag_lt i j (by simp [htag, parents])
        have hklt : k < i := htag_lt i k (by simp [htag, parents])
        right
        exact ⟨j, hjlt, k, hklt, hspec⟩

end PEqualNP.Outside.L_pcx_266_aux

theorem PEqualNP.Outside.L_pcx_266 :
  ∀ (n m : ℕ) (left right : Fin m → Fin n) (sign : Fin m → Bool),
    (∀ index, left index < right index) → Function.Injective (fun index => (left index, right index)) →
    let cl := fun (e : Fin m) (a : Bool) =>
      ({(left e, !a), (right e, a ^^ sign e)} : PEqualNP.ProofComplexity.Clause (Fin n))
    let oddSet := fun D : Finset (Fin m) =>
      Odd ((D.filter (fun signed => sign signed = true)).card) ∧
      ∀ v : Fin n, Even ((D.filter (fun tailEdge => left tailEdge = v)).card +
        (D.filter (fun headEdge => right headEdge = v)).card)
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
      ∀ (t : ℕ) (p : Fin t → P), t+1 = 4*g → legal t p →
        ∃ D : Finset (Fin m), D.card = g ∧ oddSet D ∧
          (∀ e a, (∃ i, p i = ax e a) ↔ e ∈ D) ∧
          ∀ i, (∃ e ∈ D, ∃ a, p i = ax e a) ∨ ∃ j < i, ∃ k < i, p i = p j + p k := by
  intro n m left right sign hlt hinj cl oddSet negative P ax legal g hneg hmin t p ht4g ⟨hroot, hstep⟩
  exact PEqualNP.Outside.L_pcx_266_aux.shortest_pc_profile left right sign hlt hinj g hneg hmin t p ht4g hroot hstep
