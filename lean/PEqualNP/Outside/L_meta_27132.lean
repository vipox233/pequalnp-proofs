import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27132.Crit


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



theorem crit : ∀ (n t d : ℕ),
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
    exact fwd n t d a b c u v e ask readout bias H
  · rintro ⟨pick, hp, hfin⟩
    exact bwd n t d a b c u v e pick hp hfin

end PEqualNP.Outside.L_meta_27132.Crit

namespace PEqualNP.Outside.L_meta_27132

def adj (s : Finset ℕ) (v : ℕ) : Finset ℕ := s ∪ s.image (fun u => u ^^^ v)

def Sub (s : Finset ℕ) : Prop := 0 ∈ s ∧ ∀ a ∈ s, ∀ b ∈ s, a ^^^ b ∈ s

theorem mem_adj {s : Finset ℕ} {v a : ℕ} : a ∈ adj s v ↔ a ∈ s ∨ ∃ u ∈ s, u ^^^ v = a := by
  simp [adj]

theorem x1 (a b : ℕ) : (a ^^^ b) ^^^ b = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem xswap (u b v : ℕ) : (u ^^^ b) ^^^ v = (u ^^^ v) ^^^ b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor]
  cases Nat.testBit u i <;> cases Nat.testBit b i <;> cases Nat.testBit v i <;> rfl

theorem xcanc (u v w : ℕ) : (u ^^^ v) ^^^ (w ^^^ v) = u ^^^ w := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor]
  cases Nat.testBit u i <;> cases Nat.testBit w i <;> cases Nat.testBit v i <;> rfl

theorem xc2 (u v : ℕ) : (u ^^^ v) ^^^ u = v := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor]
  cases Nat.testBit u i <;> cases Nat.testBit v i <;> rfl

theorem xor_eq_zero' {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  have := x1 a b
  rw [h, Nat.zero_xor] at this
  exact this.symm

theorem Sub.adj {s : Finset ℕ} (h : Sub s) (v : ℕ) : Sub (adj s v) := by
  refine ⟨mem_adj.2 (Or.inl h.1), ?_⟩
  intro a ha b hb
  rcases mem_adj.1 ha with ha | ⟨u, hu, rfl⟩ <;> rcases mem_adj.1 hb with hb | ⟨w, hw, rfl⟩
  · exact mem_adj.2 (Or.inl (h.2 a ha b hb))
  · exact mem_adj.2 (Or.inr ⟨a ^^^ w, h.2 a ha w hw, by rw [Nat.xor_assoc]⟩)
  · exact mem_adj.2 (Or.inr ⟨u ^^^ b, h.2 u hu b hb, xswap u b v⟩)
  · exact mem_adj.2 (Or.inl (by rw [xcanc]; exact h.2 u hu w hw))

theorem sub_adj (s : Finset ℕ) (v : ℕ) : s ⊆ adj s v := fun _ ha => mem_adj.2 (Or.inl ha)

theorem self_mem_adj {s : Finset ℕ} (h : 0 ∈ s) (v : ℕ) : v ∈ adj s v :=
  mem_adj.2 (Or.inr ⟨0, h, Nat.zero_xor v⟩)

theorem adj_of_mem {s : Finset ℕ} (h : Sub s) {v : ℕ} (hv : v ∈ s) : adj s v = s := by
  ext a; rw [mem_adj]; constructor
  · rintro (ha | ⟨u, hu, rfl⟩)
    · exact ha
    · exact h.2 u hu v hv
  · exact Or.inl

theorem adj_card {s : Finset ℕ} (h : Sub s) {v : ℕ} (hv : v ∉ s) : (adj s v).card = 2 * s.card := by
  unfold adj
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective]
  · omega
  · intro a b hab
    have h2 : (a ^^^ v) ^^^ v = (b ^^^ v) ^^^ v := congrArg (fun t => t ^^^ v) hab
    rwa [x1, x1] at h2
  · rw [Finset.disjoint_left]; intro a ha ha2
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ha2
    apply hv
    have := h.2 _ ha u hu
    rwa [xc2] at this

theorem U_xor {i a b : ℕ} (ha : a % 2 ^ i = 0) (hb : b % 2 ^ i = 0) : (a ^^^ b) % 2 ^ i = 0 := by
  rw [Nat.xor_mod_two_pow, ha, hb]; rfl

theorem U_xor_iff {i v : ℕ} (hv : v % 2 ^ i = 0) (a : ℕ) : (a ^^^ v) % 2 ^ i = 0 ↔ a % 2 ^ i = 0 := by
  rw [Nat.xor_mod_two_pow, hv, Nat.xor_zero]

theorem U_succ (i g : ℕ) : g % 2 ^ (i + 1) = 0 ↔ g % 2 ^ i = 0 ∧ g.testBit i = false := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  have hp : 0 < 2 ^ i := Nat.two_pow_pos i
  have h2 : g / 2 ^ i % 2 = 0 ∨ g / 2 ^ i % 2 = 1 := by omega
  rcases h2 with h | h
  · simp [h]
  · simp [h]

theorem Sub.filterU {s : Finset ℕ} (h : Sub s) (i : ℕ) : Sub (s.filter (fun g => g % 2 ^ i = 0)) := by
  refine ⟨Finset.mem_filter.2 ⟨h.1, Nat.zero_mod _⟩, ?_⟩
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb ⊢
  exact ⟨h.2 a ha.1 b hb.1, U_xor ha.2 hb.2⟩

theorem adj_filter (s : Finset ℕ) {i v : ℕ} (hv : v % 2 ^ i = 0) :
    (adj s v).filter (fun g => g % 2 ^ i = 0) = adj (s.filter (fun g => g % 2 ^ i = 0)) v := by
  ext a
  rw [Finset.mem_filter, mem_adj, mem_adj]
  constructor
  · rintro ⟨ha | ⟨u, hu, rfl⟩, hp⟩
    · exact Or.inl (Finset.mem_filter.2 ⟨ha, hp⟩)
    · exact Or.inr ⟨u, Finset.mem_filter.2 ⟨hu, (U_xor_iff hv u).1 hp⟩, rfl⟩
  · rintro (ha | ⟨u, hu, rfl⟩)
    · exact ⟨Or.inl (Finset.mem_filter.1 ha).1, (Finset.mem_filter.1 ha).2⟩
    · exact ⟨Or.inr ⟨u, (Finset.mem_filter.1 hu).1, rfl⟩, (U_xor_iff hv u).2 (Finset.mem_filter.1 hu).2⟩

theorem adj_ratio {s : Finset ℕ} (h : Sub s) {i v c : ℕ} (hv : v % 2 ^ i = 0)
    (hc : s.card = 2 ^ c * (s.filter (fun g => g % 2 ^ i = 0)).card) :
    (adj s v).card = 2 ^ c * ((adj s v).filter (fun g => g % 2 ^ i = 0)).card := by
  rw [adj_filter s hv]
  by_cases hm : v ∈ s
  · rw [adj_of_mem h hm, adj_of_mem (h.filterU i) (Finset.mem_filter.2 ⟨hm, hv⟩)]
    exact hc
  · rw [adj_card h hm, adj_card (h.filterU i) (fun hh => hm (Finset.mem_filter.1 hh).1), hc]
    ring

theorem gen_inv (i c : ℕ) : ∀ (rows : List ℕ) (G : Finset ℕ), Sub G → (∀ r ∈ rows, r % 2 ^ i = 0) →
    G.card = 2 ^ c * (G.filter (fun g => g % 2 ^ i = 0)).card →
    Sub (rows.foldl adj G) ∧
    (rows.foldl adj G).filter (fun g => g % 2 ^ i = 0) = rows.foldl adj (G.filter (fun g => g % 2 ^ i = 0)) ∧
    (rows.foldl adj G).card = 2 ^ c * ((rows.foldl adj G).filter (fun g => g % 2 ^ i = 0)).card := by
  intro rows
  induction rows with
  | nil => intro G hG _ hc; exact ⟨hG, rfl, hc⟩
  | cons r rs ih =>
    intro G hG hr hc
    have hr0 := hr r (by simp)
    have := ih (adj G r) (hG.adj r) (fun x hx => hr x (by simp [hx])) (adj_ratio hG hr0 hc)
    simp only [List.foldl_cons]
    rw [← adj_filter G hr0]
    exact this

theorem gen_ind (Q : ℕ → Prop) (hQ : ∀ a b, Q a → Q b → Q (a ^^^ b)) : ∀ (rows : List ℕ) (T : Finset ℕ),
    (∀ g ∈ T, Q g) → (∀ r ∈ rows, Q r) → ∀ g ∈ rows.foldl adj T, Q g := by
  intro rows
  induction rows with
  | nil => intro T hT _ g hg; exact hT g hg
  | cons r rs ih =>
    intro T hT hr
    simp only [List.foldl_cons]
    apply ih
    · intro g hg
      rcases mem_adj.1 hg with hg | ⟨u, hu, rfl⟩
      · exact hT g hg
      · exact hQ _ _ (hT u hu) (hr r (by simp))
    · intro x hx; exact hr x (by simp [hx])

theorem gen_mono : ∀ (rows : List ℕ) (T T' : Finset ℕ), T ⊆ T' → rows.foldl adj T ⊆ rows.foldl adj T' := by
  intro rows
  induction rows with
  | nil => intro T T' h; exact h
  | cons r rs ih =>
    intro T T' h
    simp only [List.foldl_cons]
    apply ih
    intro a ha
    rcases mem_adj.1 ha with ha | ⟨u, hu, rfl⟩
    · exact mem_adj.2 (Or.inl (h ha))
    · exact mem_adj.2 (Or.inr ⟨u, h hu, rfl⟩)

theorem gen_sup : ∀ (rows : List ℕ) (T : Finset ℕ), T ⊆ rows.foldl adj T := by
  intro rows
  induction rows with
  | nil => intro T; exact Finset.Subset.refl _
  | cons r rs ih =>
    intro T
    simp only [List.foldl_cons]
    exact (sub_adj T r).trans (ih _)

theorem image_adj (f : ℕ → ℕ) (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b) (s : Finset ℕ) (v : ℕ) :
    (adj s v).image f = adj (s.image f) (f v) := by
  ext a
  simp only [Finset.mem_image, mem_adj]
  constructor
  · rintro ⟨x, hx | ⟨u, hu, rfl⟩, rfl⟩
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨f u, ⟨u, hu, rfl⟩, (hf u v).symm⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨_, ⟨u, hu, rfl⟩, rfl⟩)
    · exact ⟨x, Or.inl hx, rfl⟩
    · exact ⟨u ^^^ v, Or.inr ⟨u, hu, rfl⟩, hf u v⟩

theorem image_gen (f : ℕ → ℕ) (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b) : ∀ (rows : List ℕ) (T : Finset ℕ),
    (rows.foldl adj T).image f = (rows.map f).foldl adj (T.image f) := by
  intro rows
  induction rows with
  | nil => intro T; rfl
  | cons r rs ih =>
    intro T
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, image_adj f hf]

theorem half {B : Finset ℕ} (h : Sub B) (i : ℕ) :
    B.filter (fun g => g.testBit i = false) = B ∨
    B.card = 2 * (B.filter (fun g => g.testBit i = false)).card := by
  by_cases hall : ∀ g ∈ B, g.testBit i = false
  · left; exact Finset.filter_true_of_mem hall
  · right
    obtain ⟨g0, hg0, hb⟩ : ∃ g0 ∈ B, ¬ g0.testBit i = false := by
      by_contra hc
      exact hall (fun g hg => by
        by_contra hh
        exact hc ⟨g, hg, hh⟩)
    have hb' : g0.testBit i = true := by simpa using hb
    have himg : B.filter (fun g => ¬ g.testBit i = false) =
        (B.filter (fun g => g.testBit i = false)).image (fun u => u ^^^ g0) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨ha, hbit⟩
        have hbit' : a.testBit i = true := by simpa using hbit
        exact ⟨a ^^^ g0, ⟨h.2 a ha g0 hg0, by rw [Nat.testBit_xor, hbit', hb']; rfl⟩, x1 a g0⟩
      · rintro ⟨u, ⟨hu, hbit⟩, rfl⟩
        exact ⟨h.2 u hu g0 hg0, by rw [Nat.testBit_xor, hbit, hb']; simp⟩
    have hsum := Finset.card_filter_add_card_filter_not (s := B) (fun g => g.testBit i = false)
    rw [himg, Finset.card_image_of_injective] at hsum
    · omega
    · intro a b hab
      have h2 : (a ^^^ g0) ^^^ g0 = (b ^^^ g0) ^^^ g0 := congrArg (fun t => t ^^^ g0) hab
      rwa [x1, x1] at h2

theorem Sub.image {s : Finset ℕ} (h : Sub s) (f : ℕ → ℕ) (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b) :
    Sub (s.image f) := by
  have h0 : f 0 = 0 := by
    have := hf 0 0
    rw [Nat.xor_self] at this
    rw [this, Nat.xor_self]
  refine ⟨Finset.mem_image.2 ⟨0, h.1, h0⟩, ?_⟩
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
  exact Finset.mem_image.2 ⟨x ^^^ y, h.2 x hx y hy, hf x y⟩

def seed : Finset ℕ := (Finset.range 64).image (fun v => v + 64*v)

def emb (N i v : ℕ) : ℕ := ((v % 64) <<< i) ^^^ ((v / 64) <<< N)

def emb7 (N i y : ℕ) : ℕ := ((y % 128) <<< i) ^^^ ((y / 128) <<< N)

def stepSt (m1 m2 : ℕ) (st : ℕ × Finset ℕ) : ℕ × Finset ℕ :=
  let shifted := st.2.image (fun v => v % 64 + 128*(v / 64))
  let both := adj (adj shifted m1) m2
  let even := both.filter (fun v => v % 2 = 0)
  (st.1 + (if even = both then 0 else 1), even.image (fun v => v / 2))

theorem x4 (a b c d : ℕ) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor]
  cases Nat.testBit a i <;> cases Nat.testBit b i <;> cases Nat.testBit c i <;> cases Nat.testBit d i <;> rfl

theorem emb7_xor (N i a b : ℕ) : emb7 N i (a ^^^ b) = emb7 N i a ^^^ emb7 N i b := by
  unfold emb7
  have h1 : (a ^^^ b) % 128 = a % 128 ^^^ b % 128 := Nat.xor_mod_two_pow (n := 7)
  have h2 : (a ^^^ b) / 128 = a / 128 ^^^ b / 128 := Nat.xor_div_two_pow (n := 7)
  rw [h1, h2, Nat.shiftLeft_xor_distrib, Nat.shiftLeft_xor_distrib, x4]

theorem emb_xor (N i a b : ℕ) : emb N i (a ^^^ b) = emb N i a ^^^ emb N i b := by
  unfold emb
  have h1 : (a ^^^ b) % 64 = a % 64 ^^^ b % 64 := Nat.xor_mod_two_pow (n := 6)
  have h2 : (a ^^^ b) / 64 = a / 64 ^^^ b / 64 := Nat.xor_div_two_pow (n := 6)
  rw [h1, h2, Nat.shiftLeft_xor_distrib, Nat.shiftLeft_xor_distrib, x4]

theorem emb7_small (N i m : ℕ) (hm : m < 128) : emb7 N i m = m <<< i := by
  unfold emb7
  rw [Nat.mod_eq_of_lt hm, Nat.div_eq_of_lt hm, Nat.zero_shiftLeft, Nat.xor_zero]

theorem emb7_sh (N i v : ℕ) : emb7 N i (v % 64 + 128 * (v / 64)) = emb N i v := by
  unfold emb7 emb
  have h1 : (v % 64 + 128 * (v / 64)) % 128 = v % 64 := by omega
  have h2 : (v % 64 + 128 * (v / 64)) / 128 = v / 64 := by omega
  rw [h1, h2]

theorem emb_half (N i y : ℕ) (hy : y % 2 = 0) : emb N (i+1) (y / 2) = emb7 N i y := by
  unfold emb emb7
  rw [Nat.shiftLeft_succ_inside]
  have h1 : 2 * (y / 2 % 64) = y % 128 := by omega
  have h2 : y / 2 / 64 = y / 128 := by omega
  rw [h1, h2]

theorem emb7_bit (N i y : ℕ) (hi : i < N) : (emb7 N i y).testBit i = decide (y % 2 = 1) := by
  unfold emb7
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.sub_self, Nat.testBit_zero]
  have h1 : y % 128 % 2 = y % 2 := by omega
  rw [h1]
  simp [Nat.not_le.2 hi]

def Inv (N i : ℕ) (st : ℕ × Finset ℕ) (G : Finset ℕ) : Prop :=
  Sub G ∧ st.2.image (emb N i) = G.filter (fun g => g % 2 ^ i = 0) ∧
    G.card = 2 ^ st.1 * (G.filter (fun g => g % 2 ^ i = 0)).card

theorem step_inv (N i m1 m2 : ℕ) (hi : i < N) (h1 : m1 < 128) (h2 : m2 < 128)
    (st : ℕ × Finset ℕ) (G : Finset ℕ) (h : Inv N i st G) :
    Inv N (i+1) (stepSt m1 m2 st) ([m1 <<< i, m2 <<< i].foldl adj G) := by
  obtain ⟨hS, hH, hc⟩ := h
  have hr : ∀ r ∈ [m1 <<< i, m2 <<< i], r % 2 ^ i = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [Nat.shiftLeft_eq] <;> exact Nat.mul_mod_left _ _
  obtain ⟨hS', hF', hc'⟩ := gen_inv i st.1 _ G hS hr hc
  generalize hG' : [m1 <<< i, m2 <<< i].foldl adj G = G' at hS' hF' hc' ⊢
  have hB : (adj (adj (st.2.image (fun v => v % 64 + 128*(v / 64))) m1) m2).image (emb7 N i) =
      G'.filter (fun g => g % 2 ^ i = 0) := by
    rw [hF', ← hH, image_adj _ (emb7_xor N i), image_adj _ (emb7_xor N i), Finset.image_image,
      emb7_small N i m1 h1, emb7_small N i m2 h2]
    have : (emb7 N i ∘ fun v => v % 64 + 128*(v / 64)) = emb N i := by
      funext v; exact emb7_sh N i v
    rw [this]; rfl
  generalize hboth : adj (adj (st.2.image (fun v => v % 64 + 128*(v / 64))) m1) m2 = both at hB
  have hst : stepSt m1 m2 st = (st.1 + (if both.filter (fun v => v % 2 = 0) = both then 0 else 1),
      (both.filter (fun v => v % 2 = 0)).image (fun v => v / 2)) := by
    rw [← hboth]; rfl
  rw [hst]
  refine ⟨hS', ?_, ?_⟩
  · ext g
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨_, ⟨y, ⟨hy, hev⟩, rfl⟩, rfl⟩
      rw [emb_half N i y hev]
      have hm : emb7 N i y ∈ G'.filter (fun g => g % 2 ^ i = 0) := by
        rw [← hB]; exact Finset.mem_image_of_mem _ hy
      rw [Finset.mem_filter] at hm
      refine ⟨hm.1, (U_succ i _).2 ⟨hm.2, ?_⟩⟩
      rw [emb7_bit N i y hi]
      simp [hev]
    · rintro ⟨hg, hu⟩
      obtain ⟨hu1, hbit⟩ := (U_succ i g).1 hu
      have hm : g ∈ G'.filter (fun g => g % 2 ^ i = 0) := Finset.mem_filter.2 ⟨hg, hu1⟩
      rw [← hB] at hm
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hm
      rw [emb7_bit N i y hi] at hbit
      have hev : y % 2 = 0 := by
        have := of_decide_eq_false hbit
        omega
      exact ⟨y / 2, ⟨y, ⟨hy, hev⟩, rfl⟩, emb_half N i y hev⟩
  · have hBsub : Sub (G'.filter (fun g => g % 2 ^ i = 0)) := hS'.filterU i
    have hfilt : (G'.filter (fun g => g % 2 ^ i = 0)).filter (fun g => g.testBit i = false) =
        G'.filter (fun g => g % 2 ^ (i+1) = 0) := by
      ext g
      simp only [Finset.mem_filter, U_succ, and_assoc]
    have hiff : (both.filter (fun v => v % 2 = 0) = both) ↔
        ((G'.filter (fun g => g % 2 ^ i = 0)).filter (fun g => g.testBit i = false) =
          G'.filter (fun g => g % 2 ^ i = 0)) := by
      rw [Finset.filter_eq_self, Finset.filter_eq_self, ← hB]
      constructor
      · intro h g hg
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hg
        rw [emb7_bit N i y hi]
        simp [h y hy]
      · intro h y hy
        have := h _ (Finset.mem_image_of_mem _ hy)
        rw [emb7_bit N i y hi] at this
        have := of_decide_eq_false this
        omega
    show G'.card = 2 ^ (st.1 + if both.filter (fun v => v % 2 = 0) = both then 0 else 1) * _
    by_cases he : both.filter (fun v => v % 2 = 0) = both
    · rw [if_pos he, ← hfilt, hiff.1 he]
      simpa using hc'
    · rw [if_neg he, ← hfilt]
      rcases half hBsub i with hh | hh
      · exact absurd (hiff.2 hh) he
      · rw [hc', hh]; ring

theorem seed_xor : ∀ a < 64, ∀ b < 64, (a + 64*a) ^^^ (b + 64*b) = (a ^^^ b) + 64 * (a ^^^ b) := by
  decide +kernel

theorem seed_sub : Sub seed := by
  refine ⟨Finset.mem_image.2 ⟨0, by simp, rfl⟩, ?_⟩
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
  rw [Finset.mem_range] at hx hy
  exact Finset.mem_image.2 ⟨x ^^^ y, Finset.mem_range.2 (Nat.xor_lt_two_pow (n := 6) hx hy),
    (seed_xor x hx y hy).symm⟩

def strm (M : ℕ → Bool → ℕ) (j : ℕ) : ℕ × Finset ℕ :=
  (List.range j).foldl (fun st i => stepSt (M i false) (M i true) st) (0, seed)

def Gs (N : ℕ) (M : ℕ → Bool → ℕ) : ℕ → Finset ℕ
  | 0 => seed.image (emb N 0)
  | j+1 => [M j false <<< j, M j true <<< j].foldl adj (Gs N M j)

theorem strm_succ (M : ℕ → Bool → ℕ) (j : ℕ) :
    strm M (j+1) = stepSt (M j false) (M j true) (strm M j) := by
  simp [strm, List.range_succ]

theorem inv_all (N : ℕ) (M : ℕ → Bool → ℕ) (hM : ∀ j b, M j b < 128) :
    ∀ j, j ≤ N → Inv N j (strm M j) (Gs N M j) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨seed_sub.image _ (emb_xor N 0), ?_, ?_⟩
    · show seed.image (emb N 0) = (seed.image (emb N 0)).filter _
      rw [Finset.filter_true_of_mem]
      intro g _; simp [Nat.mod_one]
    · show (seed.image (emb N 0)).card = 2 ^ 0 * ((seed.image (emb N 0)).filter _).card
      rw [Finset.filter_true_of_mem]
      · simp
      · intro g _; simp [Nat.mod_one]
  | succ j ih =>
    intro hj
    rw [strm_succ]
    exact step_inv N j _ _ (by omega) (hM j false) (hM j true) _ _ (ih (by omega))

def rows6 : List ℕ := [65, 130, 260, 520, 1040, 2080]

theorem seed_gen : seed = rows6.foldl adj {0} := by
  decide +kernel

theorem biU_gen (S : Finset ℕ) : ∀ (rows : List ℕ) (T : Finset ℕ),
    S.biUnion (fun v => (rows.foldl adj T).image (fun u => v ^^^ u)) =
      rows.foldl adj (S.biUnion (fun v => T.image (fun u => v ^^^ u))) := by
  intro rows
  induction rows with
  | nil => intro T; rfl
  | cons r rs ih =>
    intro T
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_image, mem_adj]
    constructor
    · rintro ⟨v, hv, u, hu | ⟨w, hw, rfl⟩, rfl⟩
      · exact Or.inl ⟨v, hv, u, hu, rfl⟩
      · exact Or.inr ⟨v ^^^ w, ⟨v, hv, w, hw, rfl⟩, Nat.xor_assoc _ _ _⟩
    · rintro (⟨v, hv, u, hu, rfl⟩ | ⟨_, ⟨v, hv, w, hw, rfl⟩, rfl⟩)
      · exact ⟨v, hv, u, Or.inl hu, rfl⟩
      · exact ⟨v, hv, w ^^^ r, Or.inr ⟨w, hw, rfl⟩, (Nat.xor_assoc _ _ _).symm⟩

theorem closed_gen (S : Finset ℕ) :
    S.biUnion (fun v => seed.image (fun u => v ^^^ u)) = rows6.foldl adj S := by
  rw [seed_gen, biU_gen]
  congr 1
  ext a
  simp

theorem split64 (v : ℕ) : v % 64 ^^^ (v / 64) <<< 6 = v := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 : (v % 64).testBit i = (decide (i < 6) && v.testBit i) := Nat.testBit_mod_two_pow v 6 i
  have h2 : (v / 64).testBit (i - 6) = v.testBit (i - 6 + 6) := Nat.testBit_div_two_pow (n := 6) v (i - 6)
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft, h1, h2]
  by_cases h : i < 6
  · simp [h, Nat.not_le.2 h]
  · have h' : 6 ≤ i := by omega
    simp [h, h', Nat.sub_add_cancel h']

theorem emb_last (k v : ℕ) : emb (k+6) k v = v <<< k := by
  unfold emb
  rw [Nat.add_comm k 6, Nat.shiftLeft_add, ← Nat.shiftLeft_xor_distrib, split64]

theorem shl_inj (k : ℕ) : Function.Injective (fun v : ℕ => v <<< k) := by
  intro a b h
  have h2 : (a <<< k) >>> k = (b <<< k) >>> k := congrArg (fun t => t >>> k) h
  rwa [Nat.shiftLeft_shiftRight, Nat.shiftLeft_shiftRight] at h2

def Gt (k : ℕ) (M : ℕ → Bool → ℕ) : Finset ℕ :=
  (rows6.map (fun r => r <<< k)).foldl adj (Gs (k+6) M k)

theorem phase1 (k : ℕ) (M : ℕ → Bool → ℕ) (hM : ∀ j b, M j b < 128) :
    Sub (Gt k M) ∧ (Gt k M).card = 2 ^ (strm M k).1 *
      ((strm M k).2.biUnion (fun v => seed.image (fun u => v ^^^ u))).card := by
  obtain ⟨hS, hH, hc⟩ := inv_all (k+6) M hM k (by omega)
  have hr : ∀ r ∈ rows6.map (fun r => r <<< k), r % 2 ^ k = 0 := by
    intro r hr
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 hr
    show x <<< k % 2 ^ k = 0
    rw [Nat.shiftLeft_eq]; exact Nat.mul_mod_left _ _
  obtain ⟨hS', hF', hc'⟩ := gen_inv k (strm M k).1 _ _ hS hr hc
  refine ⟨hS', ?_⟩
  unfold Gt
  rw [hc', hF', ← hH, closed_gen]
  have he : emb (k+6) k = fun v => v <<< k := by funext v; exact emb_last k v
  rw [he, ← image_gen _ (fun a b => Nat.shiftLeft_xor_distrib), Finset.card_image_of_injective _ (shl_inj k)]

abbrev D (k : ℕ) := (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2

def ix (k : ℕ) (hk : 0 < k) (j : ℕ) : Fin k := ⟨j % k, Nat.mod_lt _ hk⟩

noncomputable def pj (k : ℕ) (i : Fin k) : D k := LinearMap.proj i

theorem pj_apply (k : ℕ) (i : Fin k) (x : Fin k → ZMod 2) : pj k i x = x i := rfl

noncomputable def bitp (k : ℕ) (hk : 0 < k) (g j p : ℕ) : D k :=
  if g.testBit j then LinearMap.proj (ix k hk p) else 0

noncomputable def phi (k : ℕ) (hk : 0 < k) (g : ℕ) : D k :=
  (∑ j ∈ Finset.range (k+6), bitp k hk g j j) + ∑ j ∈ Finset.range 6, bitp k hk g (k+6+j) j

theorem dd {k : ℕ} (p : D k) : p + p = 0 := by
  apply LinearMap.ext; intro x
  show p x + p x = 0
  exact CharTwo.add_self_eq_zero _

theorem bitp_xor (k : ℕ) (hk : 0 < k) (a b j p : ℕ) :
    bitp k hk (a ^^^ b) j p = bitp k hk a j p + bitp k hk b j p := by
  unfold bitp
  rw [Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> simp [dd]

theorem phi_xor (k : ℕ) (hk : 0 < k) (a b : ℕ) : phi k hk (a ^^^ b) = phi k hk a + phi k hk b := by
  unfold phi
  simp only [bitp_xor, Finset.sum_add_distrib]
  abel

theorem bitp_false (k : ℕ) (hk : 0 < k) (g j p : ℕ) (h : g.testBit j = false) : bitp k hk g j p = 0 := by
  unfold bitp; rw [h]; rfl

theorem lt64 {u n : ℕ} (hu : u < 64) (hn : 6 ≤ n) : u < 2 ^ n :=
  lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 6 ≤ 2 ^ n)

theorem phi_low (k : ℕ) (hk : 0 < k) (u : ℕ) (hu : u < 64) :
    phi k hk u = ∑ j ∈ Finset.range 6, bitp k hk u j j := by
  unfold phi
  rw [Nat.add_comm k 6, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range k, bitp k hk u (6 + x) (6 + x) = 0 :=
    Finset.sum_eq_zero (fun x _ => bitp_false k hk u _ _ (Nat.testBit_lt_two_pow (lt64 hu (by omega))))
  have h2 : ∑ j ∈ Finset.range 6, bitp k hk u (6 + k + j) j = 0 :=
    Finset.sum_eq_zero (fun x _ => bitp_false k hk u _ _ (Nat.testBit_lt_two_pow (lt64 hu (by omega))))
  rw [h1, h2, add_zero, add_zero]

theorem phi_high (k : ℕ) (hk : 0 < k) (u : ℕ) :
    phi k hk (u <<< (k+6)) = ∑ j ∈ Finset.range 6, bitp k hk u j j := by
  unfold phi
  have h1 : ∑ j ∈ Finset.range (k+6), bitp k hk (u <<< (k+6)) j j = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_range] at hx
    apply bitp_false
    rw [Nat.testBit_shiftLeft]
    simp [Nat.not_le.2 hx]
  rw [h1, zero_add]
  apply Finset.sum_congr rfl
  intro x _
  unfold bitp
  rw [Nat.testBit_shiftLeft]
  simp

theorem ix_add_left (k : ℕ) (hk : 0 < k) (x : ℕ) : ix k hk (k + x) = ix k hk x := by
  apply Fin.ext
  show (k + x) % k = x % k
  exact Nat.add_mod_left k x

theorem phi_mid (k : ℕ) (hk : 0 < k) (u : ℕ) (hu : u < 64) :
    phi k hk (u <<< k) = ∑ j ∈ Finset.range 6, bitp k hk u j j := by
  unfold phi
  rw [Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range k, bitp k hk (u <<< k) x x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_range] at hx
    apply bitp_false
    rw [Nat.testBit_shiftLeft]
    simp [Nat.not_le.2 hx]
  have h2 : ∑ j ∈ Finset.range 6, bitp k hk (u <<< k) (k + 6 + j) j = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    apply bitp_false
    rw [Nat.testBit_shiftLeft]
    have : u.testBit (k + 6 + x - k) = false := Nat.testBit_lt_two_pow (lt64 hu (by omega))
    simp [this]
  rw [h1, h2, zero_add, add_zero]
  apply Finset.sum_congr rfl
  intro x _
  unfold bitp
  rw [Nat.testBit_shiftLeft, ix_add_left]
  simp

theorem phi_init (k : ℕ) (hk : 0 < k) (a : ℕ) (ha : a < 64) : phi k hk (a ^^^ a <<< (k+6)) = 0 := by
  rw [phi_xor, phi_low k hk a ha, phi_high, dd]

theorem phi_fin (k : ℕ) (hk : 0 < k) (b : ℕ) (hb : b < 64) : phi k hk ((b ^^^ b <<< 6) <<< k) = 0 := by
  rw [Nat.shiftLeft_xor_distrib, ← Nat.shiftLeft_add, Nat.add_comm 6 k, phi_xor, phi_mid k hk b hb,
    phi_high, dd]

theorem phi_pow (k : ℕ) (hk : 0 < k) (j : ℕ) (hj : j < k + 6) :
    phi k hk (2 ^ j) = pj k (ix k hk j) := by
  unfold phi pj
  have h2 : ∑ x ∈ Finset.range 6, bitp k hk (2 ^ j) (k + 6 + x) x = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    apply bitp_false
    rw [Nat.testBit_two_pow]
    simp; omega
  rw [h2, add_zero, Finset.sum_eq_single j]
  · unfold bitp
    rw [Nat.testBit_two_pow]; simp
  · intro b _ hb
    apply bitp_false
    rw [Nat.testBit_two_pow]
    simp; omega
  · intro h
    exact absurd (Finset.mem_range.2 hj) h

theorem phi_single (k : ℕ) (hk : 0 < k) (h : ℕ) (hh : h < 2 ^ k) (j : ℕ) (hj : j < k) :
    phi k hk h (Pi.single (ix k hk j) 1) = if h.testBit j then 1 else 0 := by
  unfold phi
  have h2 : ∑ x ∈ Finset.range 6, bitp k hk h (k + 6 + x) x = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    apply bitp_false
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hh (Nat.pow_le_pow_right (by norm_num) (by omega)))
  rw [h2, add_zero, LinearMap.sum_apply, Finset.sum_eq_single j]
  · unfold bitp
    split_ifs <;> simp
  · intro b hb hbj
    by_cases hbk : b < k
    · unfold bitp
      have hne : ix k hk b ≠ ix k hk j := by
        intro he
        have := congrArg Fin.val he
        simp only [ix, Nat.mod_eq_of_lt hbk, Nat.mod_eq_of_lt hj] at this
        exact hbj this
      split_ifs <;> simp [hne]
    · rw [bitp_false]
      · rfl
      · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hh (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

theorem solveA (k : ℕ) (hk : 0 < k) : ∀ c < 64, ∃ a < 64, a ^^^ a >>> k = c := by
  by_cases h6 : 6 ≤ k
  · intro c hc
    refine ⟨c, hc, ?_⟩
    have : c >>> k = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (lt64 hc h6)
    rw [this, Nat.xor_zero]
  · have hk5 : k ≤ 5 := by omega
    interval_cases k <;> decide +kernel

theorem tail_surj (k : ℕ) (hk : 0 < k) (t : ℕ) (ht : t < 4096) :
    ∃ a < 64, ∃ b < 64, ((a ^^^ a <<< (k+6)) ^^^ ((b ^^^ b <<< 6) <<< k)) >>> k = t := by
  have h0 : t % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have h1 : t / 64 < 64 := by omega
  obtain ⟨a, ha, hax⟩ := solveA k hk (t % 64 ^^^ t / 64) (Nat.xor_lt_two_pow (n := 6) h0 h1)
  refine ⟨a, ha, a ^^^ t / 64, Nat.xor_lt_two_pow (n := 6) ha h1, ?_⟩
  rw [Nat.shiftRight_xor_distrib, Nat.shiftRight_xor_distrib, Nat.shiftLeft_shiftRight,
    Nat.add_comm k 6, Nat.shiftLeft_add, Nat.shiftLeft_shiftRight, Nat.shiftLeft_xor_distrib]
  conv_rhs => rw [← split64 t]
  apply Nat.eq_of_testBit_eq; intro i
  have hb := congrArg (fun z => z.testBit i) hax
  simp only [Nat.testBit_xor] at hb ⊢
  generalize a.testBit i = A at *
  generalize (a >>> k).testBit i = K at *
  generalize (a <<< 6).testBit i = S at *
  generalize (t / 64).testBit i = T1 at *
  generalize ((t / 64) <<< 6).testBit i = T1s at *
  generalize (t % 64).testBit i = T0 at *
  revert hb
  cases A <;> cases K <;> cases S <;> cases T1 <;> cases T1s <;> cases T0 <;> simp

theorem xk (a t : ℕ) : a ^^^ (t ^^^ a) = t := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor]
  cases Nat.testBit a i <;> cases Nat.testBit t i <;> rfl

theorem phase2 (k : ℕ) (hk : 0 < k) (G : Finset ℕ) (hS : Sub G) (hb : ∀ g ∈ G, g < 2 ^ (k+12))
    (hR : ∀ a < 64, ∀ b < 64, (a ^^^ a <<< (k+6)) ^^^ ((b ^^^ b <<< 6) <<< k) ∈ G)
    (Sp : Submodule (ZMod 2) (D k)) (hImg : ∀ δ : D k, δ ∈ Sp ↔ ∃ g ∈ G, phi k hk g = δ) :
    G.card = 4096 * Nat.card Sp := by
  classical
  have hset : (Sp : Set (D k)) = ↑(G.image (phi k hk)) := by
    ext δ
    simp only [SetLike.mem_coe, Finset.coe_image, Set.mem_image]
    exact hImg δ
  have hcard : Nat.card Sp = (G.image (phi k hk)).card := by
    have h1 : Nat.card Sp = (Sp : Set (D k)).ncard := Nat.card_coe_set_eq _
    rw [h1, hset, Set.ncard_coe_finset]
  rw [hcard]
  have hinj : Set.InjOn (fun g => (phi k hk g, g >>> k)) (G : Set ℕ) := by
    intro g1 _ g2 _ heq
    obtain ⟨e1, e2⟩ := Prod.mk.inj heq
    apply xor_eq_zero'
    have hφ : phi k hk (g1 ^^^ g2) = 0 := by rw [phi_xor, e1, dd]
    have hsh : (g1 ^^^ g2) >>> k = 0 := by rw [Nat.shiftRight_xor_distrib, e2, Nat.xor_self]
    have hlt : g1 ^^^ g2 < 2 ^ k := by
      by_contra hc
      have := Nat.div_pos (Nat.not_lt.1 hc) (Nat.two_pow_pos k)
      rw [Nat.shiftRight_eq_div_pow] at hsh
      omega
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.zero_testBit]
    by_cases hj : j < k
    · have h1 := phi_single k hk _ hlt j hj
      rw [hφ] at h1
      by_contra hc
      have hc' : (g1 ^^^ g2).testBit j = true := by simpa using hc
      rw [hc'] at h1
      simp at h1
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have himg : G.image (fun g => (phi k hk g, g >>> k)) = (G.image (phi k hk)) ×ˢ Finset.range 4096 := by
    ext ⟨δ, t⟩
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨g, hg, heq⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      refine ⟨⟨g, hg, rfl⟩, ?_⟩
      rw [Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_of_lt_mul
      have := hb g hg
      rw [pow_add] at this
      exact this
    · rintro ⟨⟨g, hg, rfl⟩, ht⟩
      have hgk : g >>> k < 4096 := by
        rw [Nat.shiftRight_eq_div_pow]
        apply Nat.div_lt_of_lt_mul
        have := hb g hg
        rw [pow_add] at this
        exact this
      obtain ⟨a, ha, b, hb', hab⟩ := tail_surj k hk (t ^^^ g >>> k) (Nat.xor_lt_two_pow (n := 12) ht hgk)
      refine ⟨g ^^^ ((a ^^^ a <<< (k+6)) ^^^ ((b ^^^ b <<< 6) <<< k)), hS.2 g hg _ (hR a ha b hb'), ?_⟩
      rw [phi_xor, phi_xor, phi_init k hk a ha, phi_fin k hk b hb', Nat.shiftRight_xor_distrib, hab, xk]
      simp
  rw [← Finset.card_image_of_injOn hinj, himg, Finset.card_product, Finset.card_range]
  ring

theorem Gs_mono (N : ℕ) (M : ℕ → Bool → ℕ) (i j : ℕ) (h : i ≤ j) : Gs N M i ⊆ Gs N M j := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (gen_sup _ _)

theorem Gs_le_Gt (k : ℕ) (M : ℕ → Bool → ℕ) : Gs (k+6) M k ⊆ Gt k M := gen_sup _ _

theorem seed_shape : ∀ b < 64, b ^^^ b <<< 6 = b + 64 * b := by decide +kernel

theorem rows6_shape : ∀ r ∈ rows6, ∃ b < 64, r = b ^^^ b <<< 6 := by decide +kernel

theorem emb0_seed (N a : ℕ) (ha : a < 64) : emb N 0 (a + 64*a) = a ^^^ a <<< N := by
  unfold emb
  have h1 : (a + 64*a) % 64 = a := by omega
  have h2 : (a + 64*a) / 64 = a := by omega
  rw [h1, h2, Nat.shiftLeft_zero]

theorem shl_lt (a n m : ℕ) (ha : a < 2 ^ n) : a <<< m < 2 ^ (n + m) := by
  rw [Nat.shiftLeft_eq, pow_add]
  exact Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos m)

theorem phi_zero (k : ℕ) (hk : 0 < k) : phi k hk 0 = 0 := by
  have h := phi_xor k hk 0 0
  rw [dd] at h
  simpa using h

theorem core (k : ℕ) (hk : 0 < k) (M : ℕ → Bool → ℕ) (hM : ∀ j b, M j b < 128) :
    2 ^ (strm M k).1 * ((strm M k).2.biUnion (fun v => seed.image (fun u => v ^^^ u))).card =
      4096 * 2 ^ Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        (Set.range (fun p : Fin k × Bool => phi k hk (M p.1.val p.2 <<< p.1.val)))) := by
  generalize hSp : Submodule.span (ZMod 2)
    (Set.range (fun p : Fin k × Bool => phi k hk (M p.1.val p.2 <<< p.1.val))) = Sp
  have hgen : ∀ (i : Fin k) (b : Bool), phi k hk (M i.val b <<< i.val) ∈ Sp := by
    intro i b
    rw [← hSp]
    exact Submodule.subset_span ⟨(i, b), rfl⟩
  have hQx : ∀ a b, (a < 2 ^ (k+12) ∧ phi k hk a ∈ Sp) → (b < 2 ^ (k+12) ∧ phi k hk b ∈ Sp) →
      (a ^^^ b < 2 ^ (k+12) ∧ phi k hk (a ^^^ b) ∈ Sp) := fun a b ha hb =>
    ⟨Nat.xor_lt_two_pow ha.1 hb.1, by rw [phi_xor]; exact Sp.add_mem ha.2 hb.2⟩
  have hQs : ∀ j, j ≤ k → ∀ g ∈ Gs (k+6) M j, g < 2 ^ (k+12) ∧ phi k hk g ∈ Sp := by
    intro j
    induction j with
    | zero =>
      intro _ g hg
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hg
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hv
      rw [Finset.mem_range] at ha
      rw [emb0_seed _ a ha]
      refine ⟨Nat.xor_lt_two_pow (lt64 ha (by omega)) ?_, by rw [phi_init k hk a ha]; exact Sp.zero_mem⟩
      have := shl_lt a 6 (k+6) ha
      rwa [show 6 + (k + 6) = k + 12 by omega] at this
    | succ j ih =>
      intro hj
      apply gen_ind _ hQx _ _ (ih (by omega))
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨lt_of_lt_of_le (shl_lt (M j false) 7 j (hM j false))
          (Nat.pow_le_pow_right (by norm_num) (by omega)), hgen ⟨j, by omega⟩ false⟩
      · exact ⟨lt_of_lt_of_le (shl_lt (M j true) 7 j (hM j true))
          (Nat.pow_le_pow_right (by norm_num) (by omega)), hgen ⟨j, by omega⟩ true⟩
  have hQt : ∀ g ∈ Gt k M, g < 2 ^ (k+12) ∧ phi k hk g ∈ Sp := by
    apply gen_ind _ hQx _ _ (hQs k le_rfl)
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
    obtain ⟨b, hb, rfl⟩ := rows6_shape x hx
    refine ⟨?_, by rw [phi_fin k hk b hb]; exact Sp.zero_mem⟩
    have h12 : b ^^^ b <<< 6 < 2 ^ 12 := Nat.xor_lt_two_pow (lt64 hb (by omega)) (shl_lt b 6 6 hb)
    have := shl_lt _ 12 k h12
    rwa [Nat.add_comm 12 k] at this
  obtain ⟨hSt, hcard⟩ := phase1 k M hM
  have h0 : ∀ j, j ≤ k+6 → (0:ℕ) ∈ Gs (k+6) M j := fun j hj => (inv_all (k+6) M hM j hj).1.1
  have hR : ∀ a < 64, ∀ b < 64, (a ^^^ a <<< (k+6)) ^^^ ((b ^^^ b <<< 6) <<< k) ∈ Gt k M := by
    intro a ha b hb
    apply hSt.2
    · apply Gs_le_Gt
      apply Gs_mono (k+6) M 0 k (Nat.zero_le _)
      rw [← emb0_seed (k+6) a ha]
      exact Finset.mem_image_of_mem _ (Finset.mem_image.2 ⟨a, Finset.mem_range.2 ha, rfl⟩)
    · have hsub : seed.image (fun r => r <<< k) ⊆ Gt k M := by
        rw [seed_gen, image_gen _ (fun a b => Nat.shiftLeft_xor_distrib)]
        apply gen_mono
        intro x hx
        rw [Finset.image_singleton, Finset.mem_singleton] at hx
        rw [hx, Nat.zero_shiftLeft]
        exact h0 k (by omega)
      apply hsub
      rw [seed_shape b hb]
      exact Finset.mem_image_of_mem _ (Finset.mem_image.2 ⟨b, Finset.mem_range.2 hb, rfl⟩)
  have hmask : ∀ (i : Fin k) (b : Bool), M i.val b <<< i.val ∈ Gt k M := by
    intro i b
    apply Gs_le_Gt
    apply Gs_mono (k+6) M (i.val+1) k i.isLt
    show M i.val b <<< i.val ∈ adj (adj (Gs (k+6) M i.val) (M i.val false <<< i.val)) (M i.val true <<< i.val)
    have hz := h0 i.val (by omega)
    cases b
    · exact sub_adj _ _ (self_mem_adj hz _)
    · exact self_mem_adj (sub_adj _ _ hz) _
  have hImg : ∀ δ : D k, δ ∈ Sp ↔ ∃ g ∈ Gt k M, phi k hk g = δ := by
    intro δ
    constructor
    · intro hδ
      have hadd : ∀ {x y : D k}, x ∈ {δ : D k | ∃ g ∈ Gt k M, phi k hk g = δ} →
          y ∈ {δ : D k | ∃ g ∈ Gt k M, phi k hk g = δ} → x + y ∈ {δ : D k | ∃ g ∈ Gt k M, phi k hk g = δ} := by
        rintro _ _ ⟨g1, h1, rfl⟩ ⟨g2, h2, rfl⟩
        exact ⟨g1 ^^^ g2, hSt.2 g1 h1 g2 h2, phi_xor k hk g1 g2⟩
      have hsmul : ∀ (c : ZMod 2) {x : D k}, x ∈ {δ : D k | ∃ g ∈ Gt k M, phi k hk g = δ} →
          c • x ∈ {δ : D k | ∃ g ∈ Gt k M, phi k hk g = δ} := by
        rintro c _ ⟨g, hg, rfl⟩
        have hc : c = 0 ∨ c = 1 := by
          fin_cases c
          · left; rfl
          · right; rfl
        rcases hc with rfl | rfl
        · exact ⟨0, hSt.1, by rw [phi_zero, zero_smul]⟩
        · exact ⟨g, hg, by rw [one_smul]⟩
      let Sp' : Submodule (ZMod 2) (D k) :=
        { carrier := {δ | ∃ g ∈ Gt k M, phi k hk g = δ}, add_mem' := hadd,
          zero_mem' := ⟨0, hSt.1, phi_zero k hk⟩, smul_mem' := hsmul }
      have hle : Sp ≤ Sp' := by
        rw [← hSp]
        apply Submodule.span_le.2
        rintro _ ⟨⟨i, b⟩, rfl⟩
        exact ⟨_, hmask i b, rfl⟩
      exact hle hδ
    · rintro ⟨g, hg, rfl⟩
      exact (hQt g hg).2
  have h2 := phase2 k hk (Gt k M) hSt (fun g hg => (hQt g hg).1) hR Sp hImg
  rw [← hcard, h2, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

def rot (k : ℕ) (hk : 0 < k) (s : ℕ) (x : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  x (ix k hk (i.val+k-s % k))

def mix (k : ℕ) (hk : 0 < k) (g : ℕ) (x : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  x i + x (ix k hk (i.val+g)) + x (ix k hk (i.val+k-g % k))

def stp (k : ℕ) (hk : 0 < k) (x : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  x i + (1+x (ix k hk (i.val+1))) * x (ix k hk (i.val+2))

def tgt (k : ℕ) (hk : 0 < k) (mark : Bool → Fin k → Bool) (row col c₁ c₂ : Fin k → ZMod 2)
    (x : Fin k → ZMod 2) (b : Bool) (i : Fin k) : ZMod 2 :=
  if mark b i then
    if b then stp k hk (mix k hk 2 (rot k hk 3 x + col)) i + rot k hk 4 x i + c₂ i
    else stp k hk (mix k hk 1 (rot k hk 1 x + row)) i + x i + c₁ i
  else 0

def runD (k d : ℕ) (ask : Fin d → ℕ → D k) (x : Fin k → ZMod 2) : ℕ :=
  (List.finRange d).foldl (fun tr j => 2*tr + (if ask j tr x = 0 then 0 else 1)) (0 : ℕ)

def chz (k : ℕ) (hk : 0 < k) (mark : Bool → Fin k → Bool) (i : Fin k) (b : Bool) (j : Fin 3) : ℕ :=
  let u : ℕ := if b then 21 else 56
  let v : ℕ := if b then 42 else 112
  if mark b (ix k hk (i.val+4)) then
    (if j.val = 0 then u else if j.val = 1 then v else u ^^^ v)
  else 0

def rr (k : ℕ) (hk : 0 < k) (s : ℕ) (j : Fin k) : Fin k := ix k hk (j.val + k - s % k)

noncomputable def Yl (k : ℕ) (hk : 0 < k) (g s : ℕ) (j : Fin k) : D k :=
  pj k (rr k hk s j) + pj k (rr k hk s (ix k hk (j.val+g))) +
    pj k (rr k hk s (ix k hk (j.val+k-g % k)))

def cyv (k : ℕ) (hk : 0 < k) (g : ℕ) (cv : Fin k → ZMod 2) (j : Fin k) : ZMod 2 :=
  cv j + cv (ix k hk (j.val+g)) + cv (ix k hk (j.val+k-g % k))

theorem mix_eq (k : ℕ) (hk : 0 < k) (g s : ℕ) (cv x : Fin k → ZMod 2) (j : Fin k) :
    mix k hk g (rot k hk s x + cv) j = Yl k hk g s j x + cyv k hk g cv j := by
  simp only [mix, rot, Yl, cyv, rr, Pi.add_apply, LinearMap.add_apply, pj_apply]
  ring

theorem rlem (k : ℕ) (hk : 0 < k) (s : ℕ) (a : ℕ) : rr k hk s (ix k hk (a + s)) = ix k hk a := by
  apply Fin.ext
  show ((a + s) % k + k - s % k) % k = a % k
  have hq : s % k < k := Nat.mod_lt _ hk
  have h1 : ((a + s) % k + k - s % k) + s % k = (a + s) % k + k := by
    generalize (a + s) % k = p at *
    generalize s % k = q at *
    omega
  have e1 : ((a + s) % k + k - s % k) + s % k ≡ a + s % k [MOD k] := by
    rw [h1]
    show ((a + s) % k + k) % k = (a + s % k) % k
    rw [Nat.add_mod_right, Nat.mod_mod, Nat.add_mod a s, Nat.add_mod a (s % k), Nat.mod_mod]
  exact Nat.ModEq.add_right_cancel' _ e1

theorem ixadd (k : ℕ) (hk : 0 < k) (a b : ℕ) : ix k hk ((ix k hk a).val + b) = ix k hk (a + b) := by
  apply Fin.ext
  show (a % k + b) % k = (a + b) % k
  exact Nat.mod_add_mod a k b

theorem shl_pow (a i : ℕ) : 2 ^ a <<< i = 2 ^ (i + a) := by
  rw [Nat.shiftLeft_eq, ← pow_add, Nat.add_comm]

theorem phi_three (k : ℕ) (hk : 0 < k) (i a b c : ℕ) (hi : i < k) (ha : a ≤ 6) (hb : b ≤ 6) (hc : c ≤ 6) :
    phi k hk ((2 ^ a ^^^ 2 ^ b ^^^ 2 ^ c) <<< i) =
      pj k (ix k hk (i + a)) + pj k (ix k hk (i + b)) + pj k (ix k hk (i + c)) := by
  rw [Nat.shiftLeft_xor_distrib, Nat.shiftLeft_xor_distrib, shl_pow, shl_pow, shl_pow, phi_xor, phi_xor,
    phi_pow k hk _ (by omega), phi_pow k hk _ (by omega), phi_pow k hk _ (by omega)]

theorem mA_f (k : ℕ) (hk : 0 < k) (i : Fin k) :
    phi k hk (56 <<< i.val) = Yl k hk 1 1 (ix k hk ((ix k hk (i.val+4)).val+1)) := by
  have hJ : ix k hk ((ix k hk (i.val+4)).val+1) = ix k hk (i.val+4+1) := ixadd k hk _ _
  have h1 : rr k hk 1 (ix k hk (i.val+4+1)) = ix k hk (i.val+4) := rlem k hk 1 _
  have h2 : ix k hk ((ix k hk (i.val+4+1)).val+1) = ix k hk (i.val+5+1) := ixadd k hk _ _
  have h3 : rr k hk 1 (ix k hk (i.val+5+1)) = ix k hk (i.val+5) := rlem k hk 1 _
  have h4 : ix k hk ((ix k hk (i.val+4+1)).val+k-1 % k) = ix k hk (i.val+3+1) := h1
  have h5 : rr k hk 1 (ix k hk (i.val+3+1)) = ix k hk (i.val+3) := rlem k hk 1 _
  have hp := phi_three k hk i.val 3 4 5 i.isLt (by omega) (by omega) (by omega)
  have hp' : phi k hk (56 <<< i.val) = _ := hp
  rw [hp', Yl, hJ, h1, h2, h3, h4, h5]
  abel

theorem mB_f (k : ℕ) (hk : 0 < k) (i : Fin k) :
    phi k hk (112 <<< i.val) = Yl k hk 1 1 (ix k hk ((ix k hk (i.val+4)).val+2)) := by
  have hJ : ix k hk ((ix k hk (i.val+4)).val+2) = ix k hk (i.val+5+1) := ixadd k hk _ _
  have h1 : rr k hk 1 (ix k hk (i.val+5+1)) = ix k hk (i.val+5) := rlem k hk 1 _
  have h2 : ix k hk ((ix k hk (i.val+5+1)).val+1) = ix k hk (i.val+6+1) := ixadd k hk _ _
  have h3 : rr k hk 1 (ix k hk (i.val+6+1)) = ix k hk (i.val+6) := rlem k hk 1 _
  have h4 : ix k hk ((ix k hk (i.val+5+1)).val+k-1 % k) = ix k hk (i.val+4+1) := h1
  have h5 : rr k hk 1 (ix k hk (i.val+4+1)) = ix k hk (i.val+4) := rlem k hk 1 _
  have hp := phi_three k hk i.val 4 5 6 i.isLt (by omega) (by omega) (by omega)
  have hp' : phi k hk (112 <<< i.val) = _ := hp
  rw [hp', Yl, hJ, h1, h2, h3, h4, h5]
  abel

theorem mA_t (k : ℕ) (hk : 0 < k) (i : Fin k) :
    phi k hk (21 <<< i.val) = Yl k hk 2 3 (ix k hk ((ix k hk (i.val+4)).val+1)) := by
  have hJ : ix k hk ((ix k hk (i.val+4)).val+1) = ix k hk (i.val+2+3) := ixadd k hk _ _
  have h1 : rr k hk 3 (ix k hk (i.val+2+3)) = ix k hk (i.val+2) := rlem k hk 3 _
  have h2 : ix k hk ((ix k hk (i.val+2+3)).val+2) = ix k hk (i.val+4+3) := ixadd k hk _ _
  have h3 : rr k hk 3 (ix k hk (i.val+4+3)) = ix k hk (i.val+4) := rlem k hk 3 _
  have h4 : ix k hk ((ix k hk (i.val+3+2)).val+k-2 % k) = ix k hk (i.val+3) := rlem k hk 2 _
  have h4' : ix k hk ((ix k hk (i.val+2+3)).val+k-2 % k) = ix k hk (i.val+0+3) := h4
  have h5 : rr k hk 3 (ix k hk (i.val+0+3)) = ix k hk (i.val+0) := rlem k hk 3 _
  have hp := phi_three k hk i.val 0 2 4 i.isLt (by omega) (by omega) (by omega)
  have hp' : phi k hk (21 <<< i.val) = _ := hp
  rw [hp', Yl, hJ, h1, h2, h3, h4', h5]
  abel

theorem mB_t (k : ℕ) (hk : 0 < k) (i : Fin k) :
    phi k hk (42 <<< i.val) = Yl k hk 2 3 (ix k hk ((ix k hk (i.val+4)).val+2)) := by
  have hJ : ix k hk ((ix k hk (i.val+4)).val+2) = ix k hk (i.val+3+3) := ixadd k hk _ _
  have h1 : rr k hk 3 (ix k hk (i.val+3+3)) = ix k hk (i.val+3) := rlem k hk 3 _
  have h2 : ix k hk ((ix k hk (i.val+3+3)).val+2) = ix k hk (i.val+5+3) := ixadd k hk _ _
  have h3 : rr k hk 3 (ix k hk (i.val+5+3)) = ix k hk (i.val+5) := rlem k hk 3 _
  have h4 : ix k hk ((ix k hk (i.val+4+2)).val+k-2 % k) = ix k hk (i.val+4) := rlem k hk 2 _
  have h4' : ix k hk ((ix k hk (i.val+3+3)).val+k-2 % k) = ix k hk (i.val+1+3) := h4
  have h5 : rr k hk 3 (ix k hk (i.val+1+3)) = ix k hk (i.val+1) := rlem k hk 3 _
  have hp := phi_three k hk i.val 1 3 5 i.isLt (by omega) (by omega) (by omega)
  have hp' : phi k hk (42 <<< i.val) = _ := hp
  rw [hp', Yl, hJ, h1, h2, h3, h4', h5]
  abel

noncomputable def gA (k : ℕ) (hk : 0 < k) (mark : Bool → Fin k → Bool) (b : Bool) (s : Fin k) : D k :=
  if mark b s then Yl k hk (if b then 2 else 1) (if b then 3 else 1) (ix k hk (s.val+1)) else 0

noncomputable def gB (k : ℕ) (hk : 0 < k) (mark : Bool → Fin k → Bool) (b : Bool) (s : Fin k) : D k :=
  if mark b s then Yl k hk (if b then 2 else 1) (if b then 3 else 1) (ix k hk (s.val+2)) else 0

noncomputable def gC (k : ℕ) (hk : 0 < k) (mark : Bool → Fin k → Bool) (b : Bool) (s : Fin k) : D k :=
  if mark b s then Yl k hk (if b then 2 else 1) (if b then 3 else 1) s +
    (if b then pj k (rr k hk 4 s) else pj k s) else 0

def gU (k : ℕ) (hk : 0 < k) (mark : Bool → Fin k → Bool) (row col : Fin k → ZMod 2) (b : Bool) (s : Fin k) : ZMod 2 :=
  if mark b s then 1 + cyv k hk (if b then 2 else 1) (if b then col else row) (ix k hk (s.val+1)) else 0

def gV (k : ℕ) (hk : 0 < k) (mark : Bool → Fin k → Bool) (row col : Fin k → ZMod 2) (b : Bool) (s : Fin k) : ZMod 2 :=
  if mark b s then cyv k hk (if b then 2 else 1) (if b then col else row) (ix k hk (s.val+2)) else 0

def gE (k : ℕ) (hk : 0 < k) (mark : Bool → Fin k → Bool) (row col c₁ c₂ : Fin k → ZMod 2) (b : Bool) (s : Fin k) : ZMod 2 :=
  if mark b s then cyv k hk (if b then 2 else 1) (if b then col else row) s + (if b then c₂ s else c₁ s) else 0

theorem tgt_eq (k : ℕ) (hk : 0 < k) (mark : Bool → Fin k → Bool) (row col c₁ c₂ : Fin k → ZMod 2)
    (x : Fin k → ZMod 2) (b : Bool) (s : Fin k) :
    tgt k hk mark row col c₁ c₂ x b s =
      (gA k hk mark b s x + gU k hk mark row col b s) * (gB k hk mark b s x + gV k hk mark row col b s) +
        gC k hk mark b s x + gE k hk mark row col c₁ c₂ b s := by
  unfold tgt gA gB gC gU gV gE
  by_cases hm : mark b s = true
  · cases b
    · simp only [hm, ↓reduceIte, Bool.false_eq_true, stp, mix_eq]
      simp only [LinearMap.add_apply, pj_apply]
      ring
    · simp only [hm, ↓reduceIte, stp, mix_eq]
      simp only [rot, rr, LinearMap.add_apply, pj_apply]
      ring
  · simp [hm]

theorem KA (k : ℕ) (hk : 0 < k) (mark : Bool → Fin k → Bool) (i : Fin k) (b : Bool) (j : Fin 3) :
    phi k hk (chz k hk mark i b j <<< i.val) =
      if j.val = 0 then gA k hk mark b (ix k hk (i.val+4))
      else if j.val = 1 then gB k hk mark b (ix k hk (i.val+4))
      else gA k hk mark b (ix k hk (i.val+4)) + gB k hk mark b (ix k hk (i.val+4)) := by
  unfold chz gA gB
  by_cases hm : mark b (ix k hk (i.val+4)) = true
  · cases b
    · simp only [hm, ↓reduceIte, Bool.false_eq_true]
      rw [← mA_f, ← mB_f]
      split_ifs
      · rfl
      · rfl
      · rw [Nat.shiftLeft_xor_distrib, phi_xor]
    · simp only [hm, ↓reduceIte]
      rw [← mA_t, ← mB_t]
      split_ifs
      · rfl
      · rfl
      · rw [Nat.shiftLeft_xor_distrib, phi_xor]
  · simp [hm, phi_zero]

theorem sig_tau (k : ℕ) (hk : 0 < k) (s : Fin k) : ix k hk ((rr k hk 4 s).val + 4) = s := by
  apply Fin.ext
  show ((s.val + k - 4 % k) % k + 4) % k = s.val
  rw [Nat.mod_add_mod]
  have hq := Nat.mod_lt 4 hk
  have hdiv := Nat.mod_add_div 4 k
  have h : s.val + k - 4 % k + 4 = s.val + k * (4 / k + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    generalize 4 % k = q at *
    generalize k * (4 / k) = m at *
    omega
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt s.isLt]

def Mof (k : ℕ) (hk : 0 < k) (mark : Bool → Fin k → Bool) (pk : Fin k → Bool → Fin 3) (j : ℕ) (b : Bool) : ℕ :=
  if h : j < k then chz k hk mark ⟨j, h⟩ b (pk ⟨j, h⟩ b) else 0

theorem chz_lt (k : ℕ) (hk : 0 < k) (mark : Bool → Fin k → Bool) (i : Fin k) (b : Bool) (j : Fin 3) :
    chz k hk mark i b j < 128 := by
  unfold chz
  cases b <;> dsimp only <;> split_ifs <;> decide

theorem Mof_lt (k : ℕ) (hk : 0 < k) (mark : Bool → Fin k → Bool) (pk : Fin k → Bool → Fin 3) (j : ℕ) (b : Bool) :
    Mof k hk mark pk j b < 128 := by
  unfold Mof
  split_ifs
  · exact chz_lt k hk mark _ b _
  · decide

theorem Mof_val (k : ℕ) (hk : 0 < k) (mark : Bool → Fin k → Bool) (pk : Fin k → Bool → Fin 3) (i : Fin k) (b : Bool) :
    Mof k hk mark pk i.val b = chz k hk mark i b (pk i b) := by
  unfold Mof
  rw [dif_pos i.isLt]

theorem fold_eq (k : ℕ) (hk : 0 < k) (mark : Bool → Fin k → Bool) (pk : Fin k → Bool → Fin 3) :
    (List.finRange k).foldl (fun (st : ℕ × Finset ℕ) i =>
      stepSt (chz k hk mark i false (pk i false)) (chz k hk mark i true (pk i true)) st)
      ((0, seed) : ℕ × Finset ℕ) = strm (Mof k hk mark pk) k := by
  unfold strm
  rw [← List.map_coe_finRange_eq_range, List.foldl_map]
  congr 1
  funext st i
  rw [Mof_val, Mof_val]

theorem final (k : ℕ) (hk : 0 < k) (mark : Bool → Fin k → Bool) (d : ℕ) (pk : Fin k → Bool → Fin 3) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (fun p : Fin k × Bool =>
      phi k hk (chz k hk mark p.1 p.2 (pk p.1 p.2) <<< p.1.val)))) ≤ d ↔
    ((List.finRange k).foldl (fun (st : ℕ × Finset ℕ) i =>
      stepSt (chz k hk mark i false (pk i false)) (chz k hk mark i true (pk i true)) st)
      ((0, seed) : ℕ × Finset ℕ)).1 +
      Nat.log2 (((List.finRange k).foldl (fun (st : ℕ × Finset ℕ) i =>
        stepSt (chz k hk mark i false (pk i false)) (chz k hk mark i true (pk i true)) st)
        ((0, seed) : ℕ × Finset ℕ)).2.biUnion (fun v => seed.image (fun u => v ^^^ u))).card ≤ d + 12 := by
  rw [fold_eq]
  have hc := core k hk (Mof k hk mark pk) (Mof_lt k hk mark pk)
  have hrange : (fun p : Fin k × Bool => phi k hk (Mof k hk mark pk p.1.val p.2 <<< p.1.val)) =
      (fun p : Fin k × Bool => phi k hk (chz k hk mark p.1 p.2 (pk p.1 p.2) <<< p.1.val)) := by
    funext p
    rw [Mof_val]
  rw [hrange] at hc
  generalize Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (fun p : Fin k × Bool =>
      phi k hk (chz k hk mark p.1 p.2 (pk p.1 p.2) <<< p.1.val)))) = r at hc ⊢
  generalize ((strm (Mof k hk mark pk) k).2.biUnion (fun v => seed.image (fun u => v ^^^ u))).card = n at hc ⊢
  generalize (strm (Mof k hk mark pk) k).1 = c at hc ⊢
  have hdvd : n ∣ 2 ^ (12 + r) := by
    refine ⟨2 ^ c, ?_⟩
    rw [pow_add]
    have : (2:ℕ) ^ 12 = 4096 := by norm_num
    rw [this]
    linarith
  obtain ⟨e, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [Nat.log2_two_pow]
  have h2 : 2 ^ (c + e) = 2 ^ (12 + r) := by
    rw [pow_add, pow_add, hc]
    norm_num
  have h3 : c + e = 12 + r := Nat.pow_right_injective (le_refl 2) h2
  omega

theorem glue (k : ℕ) (hk : 0 < k) (mark : Bool → Fin k → Bool) (row col c₁ c₂ : Fin k → ZMod 2) (d : ℕ) :
    (∃ (ask : Fin d → ℕ → D k) (readout : ℕ → Bool → Fin k → D k) (bias : ℕ → Bool → Fin k → ZMod 2),
      ∀ x b i, tgt k hk mark row col c₁ c₂ x b i =
        readout (runD k d ask x) b i x + bias (runD k d ask x) b i) ↔
    ∃ pick : Fin k → Bool → Fin 3,
      ((List.finRange k).foldl (fun (st : ℕ × Finset ℕ) i =>
        stepSt (chz k hk mark i false (pick i false)) (chz k hk mark i true (pick i true)) st)
        ((0, seed) : ℕ × Finset ℕ)).1 +
        Nat.log2 (((List.finRange k).foldl (fun (st : ℕ × Finset ℕ) i =>
          stepSt (chz k hk mark i false (pick i false)) (chz k hk mark i true (pick i true)) st)
          ((0, seed) : ℕ × Finset ℕ)).2.biUnion (fun v => seed.image (fun u => v ^^^ u))).card ≤ d + 12 := by
  let e : Fin k × Bool ≃ Fin (Fintype.card (Fin k × Bool)) := Fintype.equivFin _
  have L : (∃ (ask : Fin d → ℕ → D k) (readout : ℕ → Fin (Fintype.card (Fin k × Bool)) → D k)
        (bias : ℕ → Fin (Fintype.card (Fin k × Bool)) → ZMod 2),
      ∀ x j, (gA k hk mark (e.symm j).2 (ix k hk ((e.symm j).1.val+4)) x +
            gU k hk mark row col (e.symm j).2 (ix k hk ((e.symm j).1.val+4))) *
          (gB k hk mark (e.symm j).2 (ix k hk ((e.symm j).1.val+4)) x +
            gV k hk mark row col (e.symm j).2 (ix k hk ((e.symm j).1.val+4))) +
          gC k hk mark (e.symm j).2 (ix k hk ((e.symm j).1.val+4)) x +
          gE k hk mark row col c₁ c₂ (e.symm j).2 (ix k hk ((e.symm j).1.val+4)) =
        readout (runD k d ask x) j x + bias (runD k d ask x) j) ↔
      (∃ pick : Fin (Fintype.card (Fin k × Bool)) → D k,
        (∀ j, pick j = gA k hk mark (e.symm j).2 (ix k hk ((e.symm j).1.val+4)) ∨
          pick j = gB k hk mark (e.symm j).2 (ix k hk ((e.symm j).1.val+4)) ∨
          pick j = gA k hk mark (e.symm j).2 (ix k hk ((e.symm j).1.val+4)) +
            gB k hk mark (e.symm j).2 (ix k hk ((e.symm j).1.val+4))) ∧
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range pick)) ≤ d) :=
    PEqualNP.Outside.L_meta_27132.Crit.crit k (Fintype.card (Fin k × Bool)) d
      (fun j => gA k hk mark (e.symm j).2 (ix k hk ((e.symm j).1.val+4)))
      (fun j => gB k hk mark (e.symm j).2 (ix k hk ((e.symm j).1.val+4)))
      (fun j => gC k hk mark (e.symm j).2 (ix k hk ((e.symm j).1.val+4)))
      (fun j => gU k hk mark row col (e.symm j).2 (ix k hk ((e.symm j).1.val+4)))
      (fun j => gV k hk mark row col (e.symm j).2 (ix k hk ((e.symm j).1.val+4)))
      (fun j => gE k hk mark row col c₁ c₂ (e.symm j).2 (ix k hk ((e.symm j).1.val+4)))
  constructor
  · rintro ⟨ask, readout, bias, H⟩
    obtain ⟨pick', hp, hfin⟩ := L.1 ⟨ask,
      fun h j => readout h (e.symm j).2 (ix k hk ((e.symm j).1.val+4)),
      fun h j => bias h (e.symm j).2 (ix k hk ((e.symm j).1.val+4)),
      fun x j => (tgt_eq k hk mark row col c₁ c₂ x _ _).symm.trans (H x _ _)⟩
    have hex : ∀ (i : Fin k) (b : Bool), ∃ j3 : Fin 3,
        pick' (e (i, b)) = phi k hk (chz k hk mark i b j3 <<< i.val) := by
      intro i b
      have h := hp (e (i, b))
      simp only [Equiv.symm_apply_apply] at h
      rcases h with h | h | h
      · exact ⟨0, h.trans ((KA k hk mark i b 0).trans (if_pos rfl)).symm⟩
      · exact ⟨1, h.trans ((KA k hk mark i b 1).trans ((if_neg (by decide)).trans (if_pos rfl))).symm⟩
      · exact ⟨2, h.trans ((KA k hk mark i b 2).trans ((if_neg (by decide)).trans (if_neg (by decide)))).symm⟩
    choose pk hpk using hex
    refine ⟨pk, (final k hk mark d pk).1 ?_⟩
    have hr : Set.range pick' = Set.range (fun p : Fin k × Bool =>
        phi k hk (chz k hk mark p.1 p.2 (pk p.1 p.2) <<< p.1.val)) := by
      ext δ
      constructor
      · rintro ⟨j, rfl⟩
        refine ⟨e.symm j, ?_⟩
        show phi k hk (chz k hk mark (e.symm j).1 (e.symm j).2 (pk (e.symm j).1 (e.symm j).2) <<< (e.symm j).1.val) = pick' j
        rw [← hpk]
        simp
      · rintro ⟨p, rfl⟩
        exact ⟨e p, hpk p.1 p.2⟩
    rw [← hr]
    exact hfin
  · rintro ⟨pk, hbound⟩
    have hfin := (final k hk mark d pk).2 hbound
    have hp : ∀ j : Fin (Fintype.card (Fin k × Bool)),
        phi k hk (chz k hk mark (e.symm j).1 (e.symm j).2 (pk (e.symm j).1 (e.symm j).2) <<< (e.symm j).1.val) =
            gA k hk mark (e.symm j).2 (ix k hk ((e.symm j).1.val+4)) ∨
        phi k hk (chz k hk mark (e.symm j).1 (e.symm j).2 (pk (e.symm j).1 (e.symm j).2) <<< (e.symm j).1.val) =
            gB k hk mark (e.symm j).2 (ix k hk ((e.symm j).1.val+4)) ∨
        phi k hk (chz k hk mark (e.symm j).1 (e.symm j).2 (pk (e.symm j).1 (e.symm j).2) <<< (e.symm j).1.val) =
            gA k hk mark (e.symm j).2 (ix k hk ((e.symm j).1.val+4)) +
              gB k hk mark (e.symm j).2 (ix k hk ((e.symm j).1.val+4)) := by
      intro j
      rw [KA]
      by_cases h0 : (pk (e.symm j).1 (e.symm j).2).val = 0
      · left; rw [if_pos h0]
      · by_cases h1 : (pk (e.symm j).1 (e.symm j).2).val = 1
        · right; left; rw [if_neg h0, if_pos h1]
        · right; right; rw [if_neg h0, if_neg h1]
    have hr : Set.range (fun j : Fin (Fintype.card (Fin k × Bool)) =>
        phi k hk (chz k hk mark (e.symm j).1 (e.symm j).2 (pk (e.symm j).1 (e.symm j).2) <<< (e.symm j).1.val)) =
        Set.range (fun p : Fin k × Bool =>
          phi k hk (chz k hk mark p.1 p.2 (pk p.1 p.2) <<< p.1.val)) := by
      ext δ
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e.symm j, rfl⟩
      · rintro ⟨p, rfl⟩
        exact ⟨e p, by simp⟩
    obtain ⟨ask, readout', bias', H'⟩ := L.2 ⟨_, hp, by rw [hr]; exact hfin⟩
    refine ⟨ask, fun h b s => readout' h (e (rr k hk 4 s, b)), fun h b s => bias' h (e (rr k hk 4 s, b)), ?_⟩
    intro x b s
    have h := H' x (e (rr k hk 4 s, b))
    simp only [Equiv.symm_apply_apply] at h
    rw [sig_tau k hk s] at h
    exact (tgt_eq k hk mark row col c₁ c₂ x b s).trans h

end PEqualNP.Outside.L_meta_27132

theorem PEqualNP.Outside.L_meta_27132 : (∀ (k : ℕ) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun j : ℕ => (⟨j % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val+k-s % k))
  let mix := fun (g : ℕ) (x : W) (i : Fin k) =>
    x i + x (ix (i.val+g)) + x (ix (i.val+k-g % k))
  let step := fun (x : W) (i : Fin k) => x i + (1+x (ix (i.val+1))) * x (ix (i.val+2))
  let D := W →ₗ[F] F
  let seed := (Finset.range 64).image (fun v => v + 64*v)
  let adjoin := fun (s : Finset ℕ) (v : ℕ) => s ∪ s.image (fun u => u ^^^ v)
  ∀ (mark : Bool → Fin k → Bool) (row col c₁ c₂ : W) (d : ℕ),
    let target := fun (x : W) (b : Bool) (i : Fin k) =>
      if mark b i then
        if b then step (mix 2 (rot 3 x + col)) i + rot 4 x i + c₂ i
        else step (mix 1 (rot 1 x + row)) i + x i + c₁ i
      else 0
    let run := fun (ask : Fin d → ℕ → D) (x : W) =>
      (List.finRange d).foldl (fun tr j => 2*tr + (if ask j tr x = 0 then 0 else 1)) (0 : ℕ)
    let choose := fun (i : Fin k) (b : Bool) (j : Fin 3) =>
      let u : ℕ := if b then 21 else 56
      let v : ℕ := if b then 42 else 112
      if mark b (ix (i.val+4)) then
        (if j.val = 0 then u else if j.val = 1 then v else u ^^^ v)
      else 0
    (∃ (ask : Fin d → ℕ → D) (readout : ℕ → Bool → Fin k → D)
        (bias : ℕ → Bool → Fin k → F),
      ∀ x b i, target x b i = readout (run ask x) b i x + bias (run ask x) b i) ↔
    ∃ pick : Fin k → Bool → Fin 3,
      let last := (List.finRange k).foldl (fun (st : ℕ × Finset ℕ) i =>
        let shifted := st.2.image (fun v => v % 64 + 128*(v / 64))
        let both := adjoin (adjoin shifted (choose i false (pick i false)))
          (choose i true (pick i true))
        let even := both.filter (fun v => v % 2 = 0)
        (st.1 + (if even = both then 0 else 1), even.image (fun v => v / 2)))
        ((0, seed) : ℕ × Finset ℕ)
      let closed := last.2.biUnion (fun v => seed.image (fun u => v ^^^ u))
      last.1 + Nat.log2 closed.card ≤ d+12) := by
  intro k hk
  dsimp only
  intro mark row col c₁ c₂ d
  exact PEqualNP.Outside.L_meta_27132.glue k hk mark row col c₁ c₂ d
