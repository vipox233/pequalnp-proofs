import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1049_aux

private lemma bool_xor_cancel (a b : Bool) : xor (xor a b) b = a := by
  cases a <;> cases b <;> rfl

private lemma bool_xor_cancel_left (a b : Bool) : xor a (xor b a) = b := by
  cases a <;> cases b <;> rfl

private lemma bool_xor_same_of_ne (a b c d s : Bool)
    (h1 : xor a b ≠ s) (h2 : xor c d ≠ s) : xor a c = xor b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases s <;> simp_all

private lemma bool_xor_pair_shift (a b t : Bool) :
    xor (xor a t) (xor b t) = xor a b := by
  cases a <;> cases b <;> cases t <;> rfl

private lemma bool_xor_inj (a b c : Bool) (h : xor a b = xor a c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

private lemma mem_comp_iff {n m : ℕ} (l r : Fin m → Fin n)
    (S : Finset (Fin m)) (v y : Fin n) :
    y ∈ Finset.univ.filter (fun y : Fin n =>
      @decide (Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) v y)
        (Classical.propDecidable _) = true) ↔
    Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) v y := by
  simp

private lemma comp_eq_of_eqv {n m : ℕ} (l r : Fin m → Fin n)
    (S : Finset (Fin m)) {v w : Fin n}
    (h : Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) v w) :
    Finset.univ.filter (fun y : Fin n =>
      @decide (Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) v y)
        (Classical.propDecidable _) = true) =
    Finset.univ.filter (fun y : Fin n =>
      @decide (Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) w y)
        (Classical.propDecidable _) = true) := by
  ext y
  simp only [mem_comp_iff]
  exact ⟨fun hvy => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) hvy,
    fun hwy => Relation.EqvGen.trans _ _ _ h hwy⟩

private lemma comp_self {n m : ℕ} (l r : Fin m → Fin n)
    (S : Finset (Fin m)) (v : Fin n) :
    v ∈ Finset.univ.filter (fun y : Fin n =>
      @decide (Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) v y)
        (Classical.propDecidable _) = true) := by
  rw [mem_comp_iff]
  exact Relation.EqvGen.refl v

private lemma comp_eq_of_mem {n m : ℕ} (l r : Fin m → Fin n)
    (S : Finset (Fin m)) {U : Finset (Fin n)} {v : Fin n}
    (hU : U ∈ Finset.univ.image (fun w : Fin n => Finset.univ.filter (fun y : Fin n =>
      @decide (Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) w y)
        (Classical.propDecidable _) = true)))
    (hv : v ∈ U) :
    Finset.univ.filter (fun y : Fin n =>
      @decide (Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) v y)
        (Classical.propDecidable _) = true) = U := by
  rcases Finset.mem_image.mp hU with ⟨w, -, rfl⟩
  rw [mem_comp_iff] at hv
  exact comp_eq_of_eqv l r S (Relation.EqvGen.symm _ _ hv)

private lemma comp_pairwiseDisjoint {n m : ℕ} (l r : Fin m → Fin n)
    (S : Finset (Fin m)) :
    ((Finset.univ.image (fun w : Fin n => Finset.univ.filter (fun y : Fin n =>
      @decide (Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) w y)
        (Classical.propDecidable _) = true))) : Set (Finset (Fin n))).PairwiseDisjoint id := by
  intro U₁ hU₁ U₂ hU₂ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro v hv₁ hv₂
  exact hne ((comp_eq_of_mem l r S hU₁ hv₁).symm.trans (comp_eq_of_mem l r S hU₂ hv₂))

private lemma comp_biUnion_eq_univ {n m : ℕ} (l r : Fin m → Fin n)
    (S : Finset (Fin m)) :
    (Finset.univ.image (fun w : Fin n => Finset.univ.filter (fun y : Fin n =>
      @decide (Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) w y)
        (Classical.propDecidable _) = true))).biUnion id = Finset.univ := by
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true, id_eq]
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ v), comp_self l r S v⟩

private lemma eqv_const {n m q : ℕ} (l r : Fin m → Fin n)
    (S : Finset (Fin m)) (c : Fin n → Fin q)
    (hc : ∀ e ∈ S, c (l e) = c (r e)) {x y : Fin n}
    (h : Relation.EqvGen (fun a b : Fin n => ∃ e ∈ S, l e = a ∧ r e = b) x y) :
    c x = c y := by
  induction h with
  | rel a b hab =>
    rcases hab with ⟨e, he, rfl, rfl⟩
    exact hc e he
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b d _ _ ih1 ih2 => exact ih1.trans ih2

private lemma eqv_phase_diff {n m : ℕ} (l r : Fin m → Fin n) (sign : Fin m → Bool)
    (S : Finset (Fin m)) (s s₀ : Fin n → Bool)
    (hs : ∀ e ∈ S, xor (s (l e)) (s (r e)) ≠ sign e)
    (hs₀ : ∀ e ∈ S, xor (s₀ (l e)) (s₀ (r e)) ≠ sign e)
    {x y : Fin n}
    (h : Relation.EqvGen (fun a b : Fin n => ∃ e ∈ S, l e = a ∧ r e = b) x y) :
    xor (s x) (s₀ x) = xor (s y) (s₀ y) := by
  induction h with
  | rel a b hab =>
    rcases hab with ⟨e, he, rfl, rfl⟩
    exact bool_xor_same_of_ne _ _ _ _ (sign e) (hs e he) (hs₀ e he)
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b d _ _ ih1 ih2 => exact ih1.trans ih2

private lemma card_const_colorings {n m q : ℕ} (l r : Fin m → Fin n)
    (S : Finset (Fin m)) :
    let comp := fun v : Fin n => Finset.univ.filter (fun y : Fin n =>
      @decide (Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) v y)
        (Classical.propDecidable _) = true)
    let C := Finset.univ.image comp
    (Finset.univ.filter (fun c : Fin n → Fin q => ∀ e ∈ S, c (l e) = c (r e))).card = q ^ C.card := by
  intro comp C
  have hcard : (Finset.univ : Finset (C → Fin q)).card = q ^ C.card := by
    simp [Fintype.card_pi]
  rw [← hcard]
  symm
  refine Finset.card_bij
    (fun (g : C → Fin q) _ => fun v : Fin n => g ⟨comp v, Finset.mem_image_of_mem comp (Finset.mem_univ v)⟩)
    ?_ ?_ ?_
  · intro g _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun e he => ?_⟩
    have hcomp : comp (l e) = comp (r e) :=
      comp_eq_of_eqv l r S (Relation.EqvGen.rel _ _ ⟨e, he, rfl, rfl⟩)
    exact congrArg g (Subtype.ext hcomp)
  · intro g₁ _ g₂ _ h
    funext ⟨U, hU⟩
    rcases Finset.mem_image.mp hU with ⟨v, -, rfl⟩
    exact congrFun h v
  · intro c hc
    rw [Finset.mem_filter] at hc
    refine ⟨fun u => c (Classical.choose (Finset.mem_image.mp u.2)), Finset.mem_univ _, ?_⟩
    funext v
    have hv : comp (Classical.choose (Finset.mem_image.mp (Finset.mem_image_of_mem comp (Finset.mem_univ v)))) = comp v :=
      (Classical.choose_spec (Finset.mem_image.mp (Finset.mem_image_of_mem comp (Finset.mem_univ v)))).2
    have hmem : v ∈ comp (Classical.choose (Finset.mem_image.mp (Finset.mem_image_of_mem comp (Finset.mem_univ v)))) := by
      rw [hv]
      exact comp_self l r S v
    rw [mem_comp_iff] at hmem
    exact eqv_const l r S c hc.2 hmem

private lemma vertexCost_eq_sum_comp {n m : ℕ} (l r : Fin m → Fin n)
    (target : Fin n → Bool) (pin : Fin n → ℕ)
    (S : Finset (Fin m)) (s : Fin n → Bool) :
    let comp := fun v : Fin n => Finset.univ.filter (fun y : Fin n =>
      @decide (Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) v y)
        (Classical.propDecidable _) = true)
    let C := Finset.univ.image comp
    ((Finset.univ : Finset (Fin n)).filter (fun v => s v ≠ target v)).sum pin =
    ∑ U ∈ C, (U.filter (fun v => s v ≠ target v)).sum pin := by
  intro comp C
  have h1 : ∀ U : Finset (Fin n),
      (U.filter (fun v => s v ≠ target v)).sum pin =
      ∑ v ∈ U, if s v ≠ target v then pin v else 0 := fun U => by
    rw [Finset.sum_filter]
  simp_rw [h1]
  have hbi := comp_biUnion_eq_univ l r S
  have hpd := comp_pairwiseDisjoint l r S
  calc
    (∑ v : Fin n, if s v ≠ target v then pin v else 0)
      = ∑ v ∈ C.biUnion id, if s v ≠ target v then pin v else 0 := by rw [hbi]
    _ = ∑ U ∈ C, ∑ v ∈ id U, if s v ≠ target v then pin v else 0 := Finset.sum_biUnion hpd
    _ = ∑ U ∈ C, ∑ v ∈ U, if s v ≠ target v then pin v else 0 := rfl

private lemma sum_phase_eq_prod {n m : ℕ} (l r : Fin m → Fin n) (sign : Fin m → Bool)
    (target : Fin n → Bool) (pin : Fin n → ℕ)
    (S : Finset (Fin m)) (s₀ : Fin n → Bool)
    (hs₀ : ∀ e ∈ S, xor (s₀ (l e)) (s₀ (r e)) ≠ sign e) :
    let comp := fun v : Fin n => Finset.univ.filter (fun y : Fin n =>
      @decide (Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) v y)
        (Classical.propDecidable _) = true)
    let C := Finset.univ.image comp
    let X : Polynomial ℤ := Polynomial.X
    let vertexCost := fun (U : Finset (Fin n)) (s : Fin n → Bool) =>
      (U.filter (fun v => s v ≠ target v)).sum pin
    (∑ s : Fin n → Bool,
      if ∀ e ∈ S, xor (s (l e)) (s (r e)) ≠ sign e then X ^ vertexCost Finset.univ s else 0) =
    ∏ U ∈ C, (X ^ vertexCost U s₀ + X ^ vertexCost U (fun v => !(s₀ v))) := by
  intro comp C X vertexCost
  have hbool : ∀ U ∈ C,
      X ^ vertexCost U s₀ + X ^ vertexCost U (fun v => !(s₀ v)) =
      ∑ b : Bool, X ^ vertexCost U (fun v => xor (s₀ v) b) := by
    intro U _
    rw [Fintype.sum_bool, add_comm]
    simp [vertexCost]
  rw [Finset.prod_congr rfl hbool]
  rw [← Finset.prod_coe_sort C (fun U => ∑ b : Bool, X ^ vertexCost U (fun v => xor (s₀ v) b))]
  rw [Fintype.prod_sum]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij
    (fun (g : C → Bool) _ => fun v : Fin n =>
      xor (s₀ v) (g ⟨comp v, Finset.mem_image_of_mem comp (Finset.mem_univ v)⟩))
    ?_ ?_ ?_ ?_
  · intro g _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun e he => ?_⟩
    have hcomp : comp (l e) = comp (r e) :=
      comp_eq_of_eqv l r S (Relation.EqvGen.rel _ _ ⟨e, he, rfl, rfl⟩)
    have hge : g ⟨comp (l e), Finset.mem_image_of_mem comp (Finset.mem_univ (l e))⟩ =
        g ⟨comp (r e), Finset.mem_image_of_mem comp (Finset.mem_univ (r e))⟩ :=
      congrArg g (Subtype.ext hcomp)
    dsimp only
    rw [hge, bool_xor_pair_shift]
    exact hs₀ e he
  · intro g₁ _ g₂ _ h
    funext ⟨U, hU⟩
    rcases Finset.mem_image.mp hU with ⟨v, -, rfl⟩
    exact bool_xor_inj (s₀ v) _ _ (congrFun h v)
  · intro s hs
    rw [Finset.mem_filter] at hs
    refine ⟨fun u => xor (s (Classical.choose (Finset.mem_image.mp u.2)))
        (s₀ (Classical.choose (Finset.mem_image.mp u.2))), Finset.mem_univ _, ?_⟩
    funext v
    have hv : comp (Classical.choose (Finset.mem_image.mp (Finset.mem_image_of_mem comp (Finset.mem_univ v)))) = comp v :=
      (Classical.choose_spec (Finset.mem_image.mp (Finset.mem_image_of_mem comp (Finset.mem_univ v)))).2
    have hmem : v ∈ comp (Classical.choose (Finset.mem_image.mp (Finset.mem_image_of_mem comp (Finset.mem_univ v)))) := by
      rw [hv]
      exact comp_self l r S v
    rw [mem_comp_iff] at hmem
    have hdiff := eqv_phase_diff l r sign S s s₀ hs.2 hs₀ hmem
    dsimp only
    rw [hdiff, bool_xor_cancel_left]
  · intro g _
    dsimp only [vertexCost]
    rw [vertexCost_eq_sum_comp l r target pin S]
    rw [← Finset.prod_pow_eq_pow_sum]
    rw [← Finset.prod_coe_sort C (fun U => X ^ (U.filter (fun v => xor (s₀ v) (g ⟨comp v, Finset.mem_image_of_mem comp (Finset.mem_univ v)⟩) ≠ target v)).sum pin)]
    refine Finset.prod_congr rfl fun u _ => ?_
    congr 1
    congr 1
    refine Finset.filter_congr fun v hv => ?_
    have hcv : comp v = u.1 := comp_eq_of_mem l r S u.2 hv
    have hgu : g ⟨comp v, Finset.mem_image_of_mem comp (Finset.mem_univ v)⟩ = g u :=
      congrArg g (Subtype.ext hcv)
    rw [hgu]

private lemma prod_one_add_sub {m : ℕ} (X : Polynomial ℤ) (wt : Fin m → ℕ)
    (B : Finset (Fin m)) :
    X ^ (B.sum wt) = ∑ S : Finset (Fin m), if S ⊆ B then ∏ e ∈ S, (X ^ wt e - 1) else 0 := by
  rw [← Finset.prod_pow_eq_pow_sum]
  have hstep : ∏ e ∈ B, X ^ wt e = ∏ e ∈ B, ((X ^ wt e - 1) + 1) := by
    refine Finset.prod_congr rfl fun e _ => ?_
    ring
  rw [hstep, Finset.prod_add]
  simp only [Finset.prod_const_one, mul_one]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext S
  simp [Finset.mem_powerset]

end PEqualNP.Outside.L_lib_1049_aux

theorem PEqualNP.Outside.L_lib_1049 :
∀ (n m q : ℕ) (l r : Fin m → Fin n) (sign : Fin m → Bool)
  (wt : Fin m → ℕ) (target : Fin n → Bool) (pin : Fin n → ℕ),
  let comp := fun (S : Finset (Fin m)) (v : Fin n) => Finset.univ.filter (fun y : Fin n =>
    @decide (Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) v y)
      (Classical.propDecidable _) = true)
  let phase := fun (S : Finset (Fin m)) (s : Fin n → Bool) =>
    ∀ e ∈ S, xor (s (l e)) (s (r e)) ≠ sign e
  let X : Polynomial ℤ := Polynomial.X
  let vertexCost := fun (U : Finset (Fin n)) (s : Fin n → Bool) =>
    (U.filter (fun v => s v ≠ target v)).sum pin
  let fieldFactor := fun (S : Finset (Fin m)) =>
    if h : ∃ s : Fin n → Bool, phase S s then
      let s := Classical.choose h
      ∏ U ∈ Finset.univ.image (comp S),
        (Polynomial.C (q : ℤ)) * (X ^ vertexCost U s + X ^ vertexCost U (fun v => !(s v)))
    else 0
  let Z := ∑ S : Finset (Fin m), fieldFactor S * ∏ e ∈ S, (X ^ wt e - 1)
  let loss := fun (c : Fin n → Fin q) (s : Fin n → Bool) =>
    vertexCost Finset.univ s + (Finset.univ.filter (fun e : Fin m =>
      c (l e) = c (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e)).sum wt
  Z = ∑ c : Fin n → Fin q, ∑ s : Fin n → Bool, X ^ loss c s := by
  intro n m q l r sign wt target pin
  dsimp only
  let comp := fun (S : Finset (Fin m)) (v : Fin n) => Finset.univ.filter (fun y : Fin n =>
    @decide (Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) v y)
      (Classical.propDecidable _) = true)
  let phase := fun (S : Finset (Fin m)) (s : Fin n → Bool) =>
    ∀ e ∈ S, xor (s (l e)) (s (r e)) ≠ sign e
  let X : Polynomial ℤ := Polynomial.X
  let vertexCost := fun (U : Finset (Fin n)) (s : Fin n → Bool) =>
    (U.filter (fun v => s v ≠ target v)).sum pin
  let fieldFactor := fun (S : Finset (Fin m)) =>
    if h : ∃ s : Fin n → Bool, phase S s then
      let s := Classical.choose h
      ∏ U ∈ Finset.univ.image (comp S),
        (Polynomial.C (q : ℤ)) * (X ^ vertexCost U s + X ^ vertexCost U (fun v => !(s v)))
    else 0
  change (∑ S : Finset (Fin m), fieldFactor S * ∏ e ∈ S, (X ^ wt e - 1)) =
    ∑ c : Fin n → Fin q, ∑ s : Fin n → Bool,
      X ^ (vertexCost Finset.univ s + (Finset.univ.filter (fun e : Fin m =>
        c (l e) = c (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e)).sum wt)
  have hrhs : ∀ (c : Fin n → Fin q) (s : Fin n → Bool),
      X ^ (vertexCost Finset.univ s + (Finset.univ.filter (fun e : Fin m =>
        c (l e) = c (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e)).sum wt) =
      ∑ S : Finset (Fin m),
        ((if ∀ e ∈ S, c (l e) = c (r e) then (1 : Polynomial ℤ) else 0) *
         (if phase S s then X ^ vertexCost Finset.univ s else 0)) *
        ∏ e ∈ S, (X ^ wt e - 1) := by
    intro c s
    rw [pow_add, PEqualNP.Outside.L_lib_1049_aux.prod_one_add_sub X wt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    have hsub : (S ⊆ Finset.univ.filter (fun e : Fin m =>
        c (l e) = c (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e)) ↔
        (∀ e ∈ S, c (l e) = c (r e)) ∧ phase S s := by
      simp [Finset.subset_iff, phase]
      constructor
      · intro h
        exact ⟨fun e he => (h he).1, fun e he => (h he).2⟩
      · intro ⟨h1, h2⟩ e he
        exact ⟨h1 e he, h2 e he⟩
    by_cases hc : ∀ e ∈ S, c (l e) = c (r e)
    · by_cases hs : phase S s
      · have hS : S ⊆ Finset.univ.filter (fun e : Fin m =>
            c (l e) = c (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e) := hsub.mpr ⟨hc, hs⟩
        rw [ite_eq_left_iff.mpr (fun h => (h hS).elim),
          ite_eq_left_iff.mpr (fun h => (h hc).elim),
          ite_eq_left_iff.mpr (fun h => (h hs).elim), one_mul]
      · have hS : ¬ S ⊆ Finset.univ.filter (fun e : Fin m =>
            c (l e) = c (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e) := fun h => hs (hsub.mp h).2
        rw [ite_eq_right_iff.mpr (fun h => (hS h).elim),
          ite_eq_right_iff.mpr (fun h => (hs h).elim)]
        ring
    · have hS : ¬ S ⊆ Finset.univ.filter (fun e : Fin m =>
          c (l e) = c (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e) := fun h => hc (hsub.mp h).1
      rw [ite_eq_right_iff.mpr (fun h => (hS h).elim),
        ite_eq_right_iff.mpr (fun h => (hc h).elim)]
      ring
  simp_rw [hrhs]
  rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    ext s
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp_rw [← Finset.sum_mul]
  congr 1
  rw [← Finset.mul_sum]
  dsimp only [fieldFactor]
  split_ifs with h
  · rw [Finset.prod_mul_distrib]
    congr 1
    · rw [Finset.prod_const]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [PEqualNP.Outside.L_lib_1049_aux.card_const_colorings l r S]
      push_cast
      rfl
    · exact (PEqualNP.Outside.L_lib_1049_aux.sum_phase_eq_prod l r sign target pin S
        (Classical.choose h) (Classical.choose_spec h)).symm
  · have hzero : (∑ s : Fin n → Bool, if phase S s then X ^ vertexCost Finset.univ s else 0) = 0 := by
      refine Finset.sum_eq_zero fun s _ => ?_
      have hns : ¬ phase S s := fun hs => h ⟨s, hs⟩
      simp [hns]
    rw [hzero, mul_zero]
