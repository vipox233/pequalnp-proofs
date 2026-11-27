import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_637

abbrev D (n : ℕ) := (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2

theorem z1 : ∀ a1 b1 a2 b2 a3 b3 : ZMod 2, a1*b2 + a2*b1 = 0 → a1*b3 + a3*b1 = 0 →
    a2*b3 + a3*b2 = 0 → a1 = 0 ∨ b2 = 0 ∨ a3 + b3 = 0 := by decide

theorem z2 : ∀ p q s t cy cz ry rz u v e β : ZMod 2,
    (p+u)*(s+v) + cy + e = ry + β → (q+u)*(t+v) + cz + e = rz + β →
    (p+q+u)*(s+t+v) + (cy+cz) + e = (ry+rz) + β → u*v + e = β → p*t + q*s = 0 := by
  decide +kernel

theorem z3 : ∀ s t : ZMod 2, (s = 0 ↔ t = 0) → s = t := by decide

theorem z4 : ∀ s t u v : ZMod 2, (s+u)*(t+v) = (1+(s+t)+u+v)*s + u*((s+t)+v) := by decide

theorem pathL {n d : ℕ} (ask : Fin d → ℕ → D n) (x : Fin n → ZMod 2) :
    ∀ (l : List (Fin d)) (h0 : ℕ),
      (∀ l1 j l2, l = l1 ++ j :: l2 →
        ask j (l1.foldl (fun h j => 2 * h + (if ask j h (0 : Fin n → ZMod 2) = 0 then 0 else 1)) h0) x = 0) →
      l.foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) h0 =
      l.foldl (fun h j => 2 * h + (if ask j h (0 : Fin n → ZMod 2) = 0 then 0 else 1)) h0 := by
  intro l
  induction l with
  | nil => intro h0 _; rfl
  | cons j l ih =>
    intro h0 hyp
    have h1 : ask j h0 x = 0 := hyp [] j l rfl
    have h2 : ask j h0 (0 : Fin n → ZMod 2) = 0 := map_zero _
    simp only [List.foldl_cons, h1, h2, ↓reduceIte, Nat.add_zero]
    apply ih
    intro l1 j' l2 hl
    have h3 := hyp (j :: l1) j' l2 (by rw [hl]; rfl)
    simpa only [List.foldl_cons, h2, ↓reduceIte, Nat.add_zero] using h3

theorem encInj {d : ℕ} (bx bz : Fin d → ℕ) (hx : ∀ j, bx j ≤ 1) (hz : ∀ j, bz j ≤ 1) :
    ∀ (l : List (Fin d)) (h0 h1 : ℕ),
      l.foldl (fun h j => 2 * h + bx j) h0 = l.foldl (fun h j => 2 * h + bz j) h1 →
      h0 = h1 ∧ ∀ j ∈ l, bx j = bz j := by
  intro l
  induction l with
  | nil => intro h0 h1 e; exact ⟨e, fun j hj => by simp at hj⟩
  | cons j l ih =>
    intro h0 h1 e
    rw [List.foldl_cons, List.foldl_cons] at e
    obtain ⟨e1, e2⟩ := ih _ _ e
    have hxj := hx j
    have hzj := hz j
    refine ⟨by omega, fun j' hj' => ?_⟩
    rcases List.mem_cons.mp hj' with rfl | h
    · omega
    · exact e2 j' h

theorem fwd (n t d : ℕ) (a b c : Fin t → D n) (u v e : Fin t → ZMod 2)
    (ask : Fin d → ℕ → D n) (readout : ℕ → Fin t → D n) (bias : ℕ → Fin t → ZMod 2)
    (H : ∀ x i, (a i x + u i) * (b i x + v i) + c i x + e i =
      readout ((List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)) i x
        + bias ((List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)) i) :
    ∃ pick : Fin t → D n, (∀ i, pick i = a i ∨ pick i = b i ∨ pick i = a i + b i) ∧
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range pick)) ≤ d := by
  classical
  obtain ⟨q, hq⟩ : ∃ q : Fin d → D n, ∀ k : Fin d, q k = ask k
      (((List.finRange d).take k.val).foldl
        (fun h j => 2 * h + (if ask j h (0 : Fin n → ZMod 2) = 0 then 0 else 1)) (0 : ℕ)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨h0, hK⟩ : ∃ h0 : ℕ, ∀ x : Fin n → ZMod 2, (∀ k, q k x = 0) →
      (List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ) = h0 := by
    refine ⟨(List.finRange d).foldl
      (fun h j => 2 * h + (if ask j h (0 : Fin n → ZMod 2) = 0 then 0 else 1)) (0 : ℕ), ?_⟩
    intro x hx
    apply pathL ask x (List.finRange d) 0
    intro l1 j l2 hl
    have hlen : l1.length < d := by
      have h5 := congrArg List.length hl
      rw [List.length_finRange, List.length_append, List.length_cons] at h5
      omega
    have e1 : (List.finRange d).take l1.length = l1 := by rw [hl]; exact List.take_left
    have e2 : (⟨l1.length, hlen⟩ : Fin d) = j := by
      have h3 : (List.finRange d)[l1.length]? = some j := by
        rw [hl, List.getElem?_append_right (le_refl _)]; simp
      obtain ⟨h4, h5⟩ := List.getElem?_eq_some_iff.mp h3
      rw [List.getElem_finRange] at h5
      rw [← h5]; rfl
    have h6 : ask ⟨l1.length, hlen⟩ (((List.finRange d).take l1.length).foldl
        (fun h j => 2 * h + (if ask j h (0 : Fin n → ZMod 2) = 0 then 0 else 1)) (0 : ℕ)) x = 0 := by
      have h7 := hx ⟨l1.length, hlen⟩
      rw [hq] at h7
      exact h7
    rw [e1, e2] at h6
    exact h6
  have hzz : ∀ i y z, (∀ k, q k y = 0) → (∀ k, q k z = 0) → a i y * b i z + a i z * b i y = 0 := by
    intro i y z hy hz
    have hyz : ∀ k, q k (y + z) = 0 := fun k => by rw [map_add, hy k, hz k, add_zero]
    have Hy := H y i
    have Hz := H z i
    have Hyz := H (y + z) i
    have H0 := H 0 i
    rw [hK y hy] at Hy
    rw [hK z hz] at Hz
    rw [hK _ hyz] at Hyz
    rw [hK 0 (fun k => map_zero _)] at H0
    simp only [map_add] at Hyz
    simp only [map_zero, zero_add, add_zero] at H0
    exact z2 _ _ _ _ _ _ _ _ _ _ _ _ Hy Hz Hyz H0
  have hcase : ∀ i, ∃ p : D n, (p = a i ∨ p = b i ∨ p = a i + b i) ∧
      ∀ x, (∀ k, q k x = 0) → p x = 0 := by
    intro i
    by_cases h1 : ∀ x, (∀ k, q k x = 0) → a i x = 0
    · exact ⟨a i, Or.inl rfl, h1⟩
    by_cases h2 : ∀ x, (∀ k, q k x = 0) → b i x = 0
    · exact ⟨b i, Or.inr (Or.inl rfl), h2⟩
    refine ⟨a i + b i, Or.inr (Or.inr rfl), ?_⟩
    by_contra h3
    obtain ⟨x1, hx1, n1⟩ : ∃ x, (∀ k, q k x = 0) ∧ a i x ≠ 0 := by
      by_contra hc
      exact h1 (fun x hx => by
        by_contra hn
        exact hc ⟨x, hx, hn⟩)
    obtain ⟨x2, hx2, n2⟩ : ∃ x, (∀ k, q k x = 0) ∧ b i x ≠ 0 := by
      by_contra hc
      exact h2 (fun x hx => by
        by_contra hn
        exact hc ⟨x, hx, hn⟩)
    obtain ⟨x3, hx3, n3⟩ : ∃ x, (∀ k, q k x = 0) ∧ a i x + b i x ≠ 0 := by
      by_contra hc
      exact h3 (fun x hx => by
        by_contra hn
        exact hc ⟨x, hx, hn⟩)
    rcases z1 (a i x1) (b i x1) (a i x2) (b i x2) (a i x3) (b i x3)
      (hzz i x1 x2 hx1 hx2) (hzz i x1 x3 hx1 hx3) (hzz i x2 x3 hx2 hx3) with h | h | h
    · exact n1 h
    · exact n2 h
    · exact n3 h
  choose pick hp1 hp2 using hcase
  refine ⟨pick, hp1, ?_⟩
  have hspan : Submodule.span (ZMod 2) (Set.range pick) ≤ Submodule.span (ZMod 2) (Set.range q) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    show pick i ∈ Submodule.span (ZMod 2) (Set.range q)
    apply mem_span_of_iInf_ker_le_ker
    intro x hx
    rw [LinearMap.mem_ker]
    apply hp2 i x
    intro k
    exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hx k)
  calc Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range pick))
      ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range q)) := Submodule.finrank_mono hspan
    _ ≤ Fintype.card (Fin d) := finrank_range_le_card q
    _ = d := Fintype.card_fin d

theorem bwd (n t d : ℕ) (a b c : Fin t → D n) (u v e : Fin t → ZMod 2)
    (pick : Fin t → D n) (hp : ∀ i, pick i = a i ∨ pick i = b i ∨ pick i = a i + b i)
    (hfin : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range pick)) ≤ d) :
    ∃ (ask : Fin d → ℕ → D n) (readout : ℕ → Fin t → D n) (bias : ℕ → Fin t → ZMod 2),
      ∀ x i, (a i x + u i) * (b i x + v i) + c i x + e i =
        readout ((List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)) i x
        + bias ((List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)) i := by
  classical
  have hfree : Module.Free (ZMod 2) ↥(Submodule.span (ZMod 2) (Set.range pick)) :=
    @Module.Free.of_divisionRing (ZMod 2) _ _ (Submodule.addCommGroup _) _
  obtain ⟨bs⟩ : Nonempty (Module.Basis (Fin (Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range pick)))) (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range pick))) := ⟨Module.finBasis _ _⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Fin d → D n, ∀ k : Fin (Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range pick))), ∃ j, Q j = (bs k : D n) := by
    refine ⟨fun j => if hj : j.val < Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range pick)) then (bs ⟨j.val, hj⟩ : D n) else 0,
      fun k => ⟨⟨k.val, lt_of_lt_of_le k.isLt hfin⟩, ?_⟩⟩
    simp
  obtain ⟨run, hrun⟩ : ∃ run : (Fin n → ZMod 2) → ℕ, ∀ x, run x =
      (List.finRange d).foldl (fun h j => 2 * h + (if Q j x = 0 then 0 else 1)) (0 : ℕ) :=
    ⟨_, fun _ => rfl⟩
  have key1 : ∀ x y, run x = run y → ∀ j, Q j x = Q j y := by
    intro x y hxy j
    rw [hrun, hrun] at hxy
    have h1 := (encInj (fun j => if Q j x = 0 then 0 else 1) (fun j => if Q j y = 0 then 0 else 1)
      (fun j => by split_ifs <;> omega) (fun j => by split_ifs <;> omega)
      (List.finRange d) 0 0 hxy).2 j (List.mem_finRange j)
    apply z3
    constructor
    · intro h0
      by_contra h2
      simp [h0, h2] at h1
    · intro h0
      by_contra h2
      simp [h0, h2] at h1
  have key2 : ∀ x y, (∀ j, Q j x = Q j y) →
      ∀ w ∈ Submodule.span (ZMod 2) (Set.range pick), w x = w y := by
    intro x y hxy w hw
    have hs := bs.sum_repr ⟨w, hw⟩
    have hs2 : (∑ k, (bs.repr ⟨w, hw⟩ k) • (bs k : D n)) = w := by
      have h1 := congrArg Subtype.val hs
      rw [Submodule.coe_sum] at h1
      exact h1
    rw [← hs2]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro k _
    obtain ⟨j, hj⟩ := hQ k
    rw [← hj, hxy j]
  have hrep : ∀ h : ℕ, ∃ x0 : Fin n → ZMod 2, ∀ x, run x = h → ∀ i, pick i x = pick i x0 := by
    intro h
    by_cases hx : ∃ x0, run x0 = h
    · obtain ⟨x0, hx0⟩ := hx
      exact ⟨x0, fun x hxh i => key2 x x0 (key1 x x0 (hxh.trans hx0.symm)) (pick i)
        (Submodule.subset_span ⟨i, rfl⟩)⟩
    · exact ⟨0, fun x hxh => absurd ⟨x, hxh⟩ hx⟩
  choose rep hrepP using hrep
  refine ⟨fun j _ => Q j,
    fun h i => if pick i = a i then (pick i (rep h) + u i) • b i + c i
      else if pick i = b i then (pick i (rep h) + v i) • a i + c i
      else (1 + pick i (rep h) + u i + v i) • a i + c i,
    fun h i => if pick i = a i then (pick i (rep h) + u i) * v i + e i
      else if pick i = b i then (pick i (rep h) + v i) * u i + e i
      else u i * (pick i (rep h) + v i) + e i, ?_⟩
  intro x i
  have hr := hrepP (run x) x rfl i
  dsimp only
  rw [← hrun x, ← hr]
  split_ifs with c1 c2
  · rw [c1]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  · rw [c2]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  · have c3 : pick i = a i + b i := by
      rcases hp i with h | h | h
      · exact absurd h c1
      · exact absurd h c2
      · exact h
    rw [c3]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination z4 (a i x) (b i x) (u i) (v i)

end PEqualNP.Outside.L_lib_637

theorem PEqualNP.Outside.L_lib_637 : ∀ (n t d : ℕ),
  let F := ZMod 2
  let V := Fin n → F
  let D := V →ₗ[F] F
  ∀ (a b c : Fin t → D) (u v e : Fin t → F),
    let target := fun (i : Fin t) (x : V) =>
      (a i x + u i) * (b i x + v i) + c i x + e i
    let run := fun (ask : Fin d → ℕ → D) (x : V) =>
      (List.finRange d).foldl (fun h j =>
        2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
    (∃ (ask : Fin d → ℕ → D) (readout : ℕ → Fin t → D)
        (bias : ℕ → Fin t → F),
      ∀ x i, target i x = readout (run ask x) i x + bias (run ask x) i) ↔
    (∃ pick : Fin t → D,
      (∀ i, pick i = a i ∨ pick i = b i ∨ pick i = a i + b i) ∧
      Module.finrank F (Submodule.span F (Set.range pick)) ≤ d) := by
  intro n t d
  dsimp only
  intro a b c u v e
  constructor
  · rintro ⟨ask, readout, bias, H⟩
    exact PEqualNP.Outside.L_lib_637.fwd n t d a b c u v e ask readout bias H
  · rintro ⟨pick, hp, hfin⟩
    exact PEqualNP.Outside.L_lib_637.bwd n t d a b c u v e pick hp hfin
