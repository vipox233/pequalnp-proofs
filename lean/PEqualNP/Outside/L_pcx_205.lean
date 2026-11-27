import PEqualNP.Defs

/-! Method: read the variables in order, remembering the first `w` and the last `w` read (at most
`2w`), so every cyclic window clause fits at its last variable. A backward dynamic program over
this scan keeps, for each step and each memory state that cannot be extended, one clause
falsified by it; each comes from two children by at most one resolution step (three lines). -/

namespace PEqualNP.Outside.L_pcx_205_aux
open PEqualNP.ProofComplexity

section scan
variable {n : ℕ} (F : Set (Clause (Fin n))) (K : ℕ → Finset (Fin n))

/-- the clause `C` fits at step `i`: its variables are the query `i` and the memory `K i`. -/
def Fits (C : Clause (Fin n)) (i : ℕ) : Prop := ∀ l ∈ C, l.1.val = i ∨ l.1 ∈ K i

/-- every way to extend `a` off the memory `K i` falsifies a clause placed at a step `≥ i`. -/
def Bad (i : ℕ) (a : Fin n → Bool) : Prop :=
  ∀ a' : Fin n → Bool, (∀ v ∈ K i, a' v = a v) →
    ∃ C ∈ F, (∃ j, i ≤ j ∧ j < n ∧ Fits K C j) ∧ ¬ ClauseSat a' C

/-- `C` is supported on `K i` and falsified by `a`. -/
def Neg (i : ℕ) (a : Fin n → Bool) (C : Clause (Fin n)) : Prop :=
  ∀ l ∈ C, l.1 ∈ K i ∧ a l.1 ≠ l.2

/-- every bad memory state at step `i` has its clause in `π`. -/
def Good (π : List (Clause (Fin n))) (i : ℕ) : Prop :=
  ∀ a, Bad F K i a → ∃ C ∈ π, Neg K i a C

theorem card_le (S : Finset (Fin n)) (f : Fin n → Bool) (G : Clause (Fin n))
    (h : ∀ l ∈ G, l.1 ∈ S ∧ f l.1 ≠ l.2) : G.card ≤ S.card := by
  apply Finset.card_le_card_of_injOn (fun l => l.1)
  · intro l hl; exact (h l hl).1
  · intro l hl l' hl' he
    have h1 := (h l hl).2
    have h2 := (h l' hl').2
    simp only at he
    apply Prod.ext he
    rw [he] at h1
    cases hl2 : l.2 <;> cases hl2' : l'.2 <;> cases hf : f l'.1 <;> simp_all

theorem addG (π : List (Clause (Fin n))) (G : Clause (Fin n)) (hd : IsDerivation F π)
    (hG : G ∈ π ∨ G ∈ F) :
    ∃ pre : List (Clause (Fin n)), pre.length ≤ 1 ∧ (∀ C ∈ pre, C = G) ∧
      IsDerivation F (pre ++ π) ∧ G ∈ pre ++ π := by
  rcases hG with hG | hG
  · exact ⟨[], by simp, by simp, hd, by simpa using hG⟩
  · exact ⟨[G], by simp, by simp, IsDerivation.ax hd hG, by simp⟩

variable (hlt : ∀ i ≤ n, ∀ v ∈ K i, v.val < i)
  (hKs : ∀ i < n, ∀ v ∈ K (i + 1), v.val = i ∨ v ∈ K i)

include hKs in
theorem persist (i : ℕ) : ∀ j, i < j → j ≤ n → ∀ v ∈ K j, v.val ≤ i → v ∈ K (i + 1) := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro hij hjn v hv hvi
    rcases Nat.lt_or_ge i j with h | h
    · rcases hKs j (by omega) v hv with h' | h'
      · omega
      · exact ih h (by omega) v h' hvi
    · have : j = i := by omega
      subst this; exact hv

include hlt hKs in
theorem child (π : List (Clause (Fin n))) (i : ℕ) (hi : i < n) (a : Fin n → Bool)
    (hbad : Bad F K i a) (hgood : Good F K π (i + 1)) (bb : Bool) :
    ∃ G, (G ∈ π ∨ G ∈ F) ∧ ∀ l ∈ G, (l.1.val = i ∨ l.1 ∈ K i) ∧
      (fun v : Fin n => if v.val = i then bb else a v) l.1 ≠ l.2 := by
  let ab : Fin n → Bool := fun v => if v.val = i then bb else a v
  by_cases hB : Bad F K (i + 1) ab
  · obtain ⟨C, hC, hN⟩ := hgood ab hB
    exact ⟨C, Or.inl hC, fun l hl => ⟨hKs i hi l.1 (hN l hl).1, (hN l hl).2⟩⟩
  · simp only [Bad, not_forall, not_exists, not_and, not_not] at hB
    obtain ⟨a', ha', hsat⟩ := hB
    let a'' : Fin n → Bool := fun v => if v.val = i ∨ v ∈ K i then ab v else a' v
    have hag : ∀ v ∈ K i, a'' v = a v := by
      intro v hv
      have := hlt i hi.le v hv
      simp only [a'', ab, hv, or_true, if_true, show v.val ≠ i by omega, if_false]
    obtain ⟨C, hC, ⟨j, hij, hjn, hfit⟩, hns⟩ := hbad a'' hag
    rcases Nat.lt_or_ge i j with hj | hj
    · exfalso
      obtain ⟨l, hl, hle⟩ := hsat C hC ⟨j, by omega, hjn, hfit⟩
      apply hns
      refine ⟨l, hl, ?_⟩
      rw [← hle]
      simp only [a'']
      split
      · next hcase =>
        have hm : l.1 ∈ K (i + 1) := by
          have hv : l.1.val ≤ i := by
            rcases hcase with h | h
            · omega
            · have := hlt i hi.le _ h; omega
          rcases hfit l hl with h | h
          · omega
          · exact persist K hKs i j hj hjn.le l.1 h hv
        exact (ha' l.1 hm).symm
      · rfl
    · have : j = i := by omega
      subst this
      refine ⟨C, Or.inr hC, fun l hl => ⟨hfit l hl, ?_⟩⟩
      intro he
      apply hns
      refine ⟨l, hl, ?_⟩
      simp only [a'', hfit l hl, if_true]
      exact he

variable (b : ℕ) (hKc : ∀ i < n, (K i).card ≤ b)

include hlt hKs hKc in
theorem one (π : List (Clause (Fin n))) (i : ℕ) (hi : i < n) (a : Fin n → Bool)
    (hd : IsDerivation F π) (hw : ∀ C ∈ π, C.card ≤ b + 1) (hgood : Good F K π (i + 1)) :
    ∃ ext : List (Clause (Fin n)), ext.length ≤ 3 ∧ IsDerivation F (ext ++ π) ∧
      (∀ C ∈ ext ++ π, C.card ≤ b + 1) ∧ (Bad F K i a → ∃ C ∈ ext ++ π, Neg K i a C) := by
  by_cases hbad : Bad F K i a
  swap
  · exact ⟨[], by simp, hd, hw, fun h => absurd h hbad⟩
  let vi : Fin n := ⟨i, hi⟩
  have hwid : ∀ (G : Clause (Fin n)) (f : Fin n → Bool),
      (∀ l ∈ G, (l.1.val = i ∨ l.1 ∈ K i) ∧ f l.1 ≠ l.2) → G.card ≤ b + 1 := by
    intro G f h
    have := card_le (insert vi (K i)) f G (fun l hl => ⟨by
      rcases (h l hl).1 with h' | h'
      · rw [Finset.mem_insert]; left; exact Fin.ext h'
      · exact Finset.mem_insert_of_mem h', (h l hl).2⟩)
    have := Finset.card_insert_le vi (K i)
    have := hKc i hi
    omega
  obtain ⟨G0, hG0, hN0⟩ := child F K hlt hKs π i hi a hbad hgood false
  obtain ⟨G1, hG1, hN1⟩ := child F K hlt hKs π i hi a hbad hgood true
  obtain ⟨p0, hl0, hc0, hd0, hm0⟩ := addG F π G0 hd hG0
  obtain ⟨p1, hl1, hc1, hd1, hm1⟩ := addG F (p0 ++ π) G1 hd0
    (by rcases hG1 with h | h
        · left; simp [h]
        · right; exact h)
  have hw1 : ∀ C ∈ p1 ++ (p0 ++ π), C.card ≤ b + 1 := by
    intro C hC
    simp only [List.mem_append] at hC
    rcases hC with h | h | h
    · rw [hc1 C h]; exact hwid G1 (fun v : Fin n => if v.val = i then true else a v) hN1
    · rw [hc0 C h]; exact hwid G0 (fun v : Fin n => if v.val = i then false else a v) hN0
    · exact hw C h
  have hG0' : G0 ∈ p1 ++ (p0 ++ π) := List.mem_append_right _ hm0
  -- a child clause that does not mention the queried variable already works
  have hkeep : ∀ (G : Clause (Fin n)) (bb : Bool),
      (∀ l ∈ G, (l.1.val = i ∨ l.1 ∈ K i) ∧
        (fun v : Fin n => if v.val = i then bb else a v) l.1 ≠ l.2) →
      ∀ l ∈ G, l ≠ (vi, !bb) → l.1 ∈ K i ∧ a l.1 ≠ l.2 := by
    intro G bb hN l hl hne
    obtain ⟨h1, h2⟩ := hN l hl
    have hvi : l.1.val ≠ i := by
      intro he
      apply hne
      apply Prod.ext (Fin.ext he)
      simp only [he, if_true] at h2
      cases hb : bb <;> cases hl2 : l.2 <;> simp_all
    rcases h1 with h1 | h1
    · exact absurd h1 hvi
    · exact ⟨h1, by simpa [hvi] using h2⟩
  by_cases hr : (vi, true) ∈ G0 ∧ (vi, false) ∈ G1
  · let R : Clause (Fin n) := G0.erase (vi, true) ∪ G1.erase (vi, false)
    have hNR : Neg K i a R := by
      intro l hl
      simp only [R, Finset.mem_union, Finset.mem_erase] at hl
      rcases hl with ⟨hne, hl⟩ | ⟨hne, hl⟩
      · exact hkeep G0 false hN0 l hl hne
      · exact hkeep G1 true hN1 l hl hne
    refine ⟨R :: (p1 ++ p0), by simp; omega, ?_, ?_, fun _ => ⟨R, by simp, hNR⟩⟩
    · have := IsDerivation.res hd1 hG0' hm1 ⟨vi, hr.1, hr.2, rfl⟩
      simpa using this
    · intro C hC
      simp only [List.cons_append, List.mem_cons, List.append_assoc] at hC
      rcases hC with h | h
      · rw [h]
        have := card_le (K i) a R hNR
        have := hKc i hi
        omega
      · exact hw1 C (by simpa using h)
  · refine ⟨p1 ++ p0, by simp; omega, by simpa using hd1,
      fun C hC => hw1 C (by simpa using hC), fun _ => ?_⟩
    by_cases h0 : (vi, true) ∈ G0
    · have h1 : (vi, false) ∉ G1 := fun h => hr ⟨h0, h⟩
      exact ⟨G1, by simpa using hm1, fun l hl => hkeep G1 true hN1 l hl
        (fun he => h1 (he ▸ hl))⟩
    · exact ⟨G0, by simpa using hG0', fun l hl => hkeep G0 false hN0 l hl
        (fun he => h0 (he ▸ hl))⟩

theorem bad_congr (i : ℕ) (a a2 : Fin n → Bool) (h : ∀ v ∈ K i, a v = a2 v) (hb : Bad F K i a) :
    Bad F K i a2 := by
  intro a' ha'
  exact hb a' (fun v hv => by rw [ha' v hv, h v hv])

include hlt hKs hKc in
theorem many (i : ℕ) (hi : i < n) : ∀ (L : List (Fin n → Bool)) (π : List (Clause (Fin n))),
    IsDerivation F π → (∀ C ∈ π, C.card ≤ b + 1) → Good F K π (i + 1) →
    ∃ π', π'.length ≤ π.length + 3 * L.length ∧ IsDerivation F π' ∧
      (∀ C ∈ π', C.card ≤ b + 1) ∧ (∀ C ∈ π, C ∈ π') ∧
      ∀ a ∈ L, Bad F K i a → ∃ C ∈ π', Neg K i a C := by
  intro L
  induction L with
  | nil => intro π hd hw _; exact ⟨π, by simp, hd, hw, fun C h => h, by simp⟩
  | cons a L ih =>
    intro π hd hw hg
    obtain ⟨ext, hl, hd', hw', hb⟩ := one F K hlt hKs b hKc π i hi a hd hw hg
    have hg' : Good F K (ext ++ π) (i + 1) := fun a' h => by
      obtain ⟨C, hC, hN⟩ := hg a' h; exact ⟨C, List.mem_append_right _ hC, hN⟩
    obtain ⟨π', hl', hd'', hw'', hsub, hall⟩ := ih (ext ++ π) hd' hw' hg'
    refine ⟨π', by simp at hl' ⊢; omega, hd'', hw'',
      fun C h => hsub C (List.mem_append_right _ h), ?_⟩
    intro a' ha' hbad
    rcases List.mem_cons.mp ha' with h | h
    · subst h
      obtain ⟨C, hC, hN⟩ := hb hbad
      exact ⟨C, hsub C hC, hN⟩
    · exact hall a' h hbad

include hlt hKs hKc in
theorem step (i : ℕ) (hi : i < n) (π : List (Clause (Fin n)))
    (hd : IsDerivation F π) (hw : ∀ C ∈ π, C.card ≤ b + 1) (hg : Good F K π (i + 1)) :
    ∃ π', π'.length ≤ π.length + 3 * 2 ^ (K i).card ∧ IsDerivation F π' ∧
      (∀ C ∈ π', C.card ≤ b + 1) ∧ Good F K π' i := by
  let L : List (Fin n → Bool) := (K i).powerset.toList.map (fun T v => decide (v ∈ T))
  obtain ⟨π', hl, hd', hw', _, hall⟩ := many F K hlt hKs b hKc i hi L π hd hw hg
  refine ⟨π', by simpa [L, Finset.card_powerset] using hl, hd', hw', ?_⟩
  intro a hbad
  let T := (K i).filter (fun v => a v = true)
  have hag : ∀ v ∈ K i, a v = decide (v ∈ T) := by
    intro v hv; cases h : a v <;> simp [T, hv, h]
  obtain ⟨C, hC, hN⟩ := hall (fun v => decide (v ∈ T))
    (List.mem_map.mpr ⟨T, by simp [T], rfl⟩) (bad_congr F K i a _ hag hbad)
  refine ⟨C, hC, fun l hl => ⟨(hN l hl).1, ?_⟩⟩
  rw [hag _ (hN l hl).1]; exact (hN l hl).2

include hlt hKs hKc in
theorem down : ∀ d ≤ n, ∃ π : List (Clause (Fin n)), IsDerivation F π ∧
    (∀ C ∈ π, C.card ≤ b + 1) ∧
    π.length ≤ 3 * ∑ j ∈ Finset.Ico (n - d) n, 2 ^ (K j).card ∧ Good F K π (n - d) := by
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨[], IsDerivation.nil, by simp, by simp, ?_⟩
    intro a hbad
    obtain ⟨C, _, ⟨j, hj, hjn, _⟩, _⟩ := hbad a (fun _ _ => rfl)
    omega
  | succ d ih =>
    intro hd
    obtain ⟨π, hD, hw, hl, hg⟩ := ih (by omega)
    have he : n - d = n - (d + 1) + 1 := by omega
    rw [he] at hg hl
    obtain ⟨π', hl', hD', hw', hg'⟩ := step F K hlt hKs b hKc (n - (d + 1)) (by omega) π hD hw hg
    refine ⟨π', hD', hw', ?_, hg'⟩
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : n - (d + 1) < n)]
    omega

end scan

end PEqualNP.Outside.L_pcx_205_aux

open PEqualNP.Outside.L_pcx_205_aux in
theorem PEqualNP.Outside.L_pcx_205 : ∀ (n w : ℕ), 0 < n →
  ∀ F : Set (PEqualNP.ProofComplexity.Clause (Fin n)),
    (∀ C ∈ F, ∃ start : Fin n, ∀ lit ∈ C, ∃ offset : Fin (w + 1),
      lit.1.val = (start.val + offset.val) % n) →
    ¬ PEqualNP.ProofComplexity.Satisfiable F →
    ∃ π : List (PEqualNP.ProofComplexity.Clause (Fin n)),
      PEqualNP.ProofComplexity.IsRefutation F π ∧
      π.length ≤ 3 * n * 4 ^ w + 1 ∧
      ∀ C ∈ π, C.card ≤ 2 * w + 1 := by
  intro n w hn F hwin hunsat
  -- memory before step `i`: the first `w` variables and the last `w` variables read
  let K : ℕ → Finset (Fin n) := fun i =>
    Finset.univ.filter (fun v : Fin n => v.val < i ∧ (v.val < w ∨ i ≤ v.val + w))
  have hlt : ∀ i ≤ n, ∀ v ∈ K i, v.val < i := by
    intro i _ v hv; simp only [K, Finset.mem_filter] at hv; exact hv.2.1
  have hKs : ∀ i < n, ∀ v ∈ K (i + 1), v.val = i ∨ v ∈ K i := by
    intro i _ v hv
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    omega
  have hKc : ∀ i < n, (K i).card ≤ 2 * w := by
    intro i _
    have hsub : K i ⊆ Finset.univ.filter (fun v : Fin n => v.val < w) ∪
        Finset.univ.filter (fun v : Fin n => i ≤ v.val + w ∧ v.val < i) := by
      intro v hv
      simp only [K, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hv ⊢
      omega
    have c1 : (Finset.univ.filter (fun v : Fin n => v.val < w)).card ≤ w := by
      have := Finset.card_le_card_of_injOn (fun v : Fin n => v.val)
        (t := Finset.range w) (s := Finset.univ.filter (fun v : Fin n => v.val < w))
        (fun v hv => by simp at hv ⊢; omega)
        (fun a _ b _ h => Fin.ext h)
      simpa using this
    have c2 : (Finset.univ.filter (fun v : Fin n => i ≤ v.val + w ∧ v.val < i)).card ≤ w := by
      have := Finset.card_le_card_of_injOn (fun v : Fin n => v.val)
        (t := Finset.Ico (i - w) i)
        (s := Finset.univ.filter (fun v : Fin n => i ≤ v.val + w ∧ v.val < i))
        (fun v hv => by simp at hv ⊢; omega)
        (fun a _ b _ h => Fin.ext h)
      simp at this; omega
    have := Finset.card_le_card hsub
    have := Finset.card_union_le (Finset.univ.filter (fun v : Fin n => v.val < w))
      (Finset.univ.filter (fun v : Fin n => i ≤ v.val + w ∧ v.val < i))
    omega
  obtain ⟨π, hD, hw, hl, hg⟩ := down F K hlt hKs (2 * w) hKc n le_rfl
  rw [Nat.sub_self] at hg hl
  have hK0 : K 0 = ∅ := by
    apply Finset.eq_empty_of_forall_notMem; intro v hv
    simp only [K, Finset.mem_filter] at hv; omega
  have hbad : Bad F K 0 (fun _ => false) := by
    intro a' _
    simp only [PEqualNP.ProofComplexity.Satisfiable, PEqualNP.ProofComplexity.Satisfies,
      not_exists, not_forall] at hunsat
    obtain ⟨C, hC, hns⟩ := hunsat a'
    obtain ⟨s, hs⟩ := hwin C hC
    -- the clause is placed at its last variable in reading order
    by_cases hwrap : s.val + w < n
    · refine ⟨C, hC, ⟨s.val + w, Nat.zero_le _, hwrap, fun l hl => ?_⟩, hns⟩
      obtain ⟨o, ho⟩ := hs l hl
      rw [Nat.mod_eq_of_lt (by omega)] at ho
      simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
      have := o.isLt
      omega
    · refine ⟨C, hC, ⟨n - 1, Nat.zero_le _, by omega, fun l hl => ?_⟩, hns⟩
      obtain ⟨o, ho⟩ := hs l hl
      have hlt' := l.1.isLt
      have ho' := o.isLt
      simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h1 : s.val + o.val < n
      · rw [Nat.mod_eq_of_lt h1] at ho; omega
      · by_cases h2 : s.val + o.val < 2 * n
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at ho; omega
        · have := s.isLt; omega
  obtain ⟨C, hC, hN⟩ := hg _ hbad
  have hCe : C = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro l hl
    have := (hN l hl).1
    rw [hK0] at this; simp at this
  refine ⟨π, ⟨hD, hCe ▸ hC⟩, ?_, hw⟩
  have hsum : ∑ j ∈ Finset.Ico 0 n, 2 ^ (K j).card ≤ n * 4 ^ w := by
    have : ∀ j ∈ Finset.Ico 0 n, 2 ^ (K j).card ≤ 4 ^ w := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      calc 2 ^ (K j).card ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (hKc j hj.2)
        _ = 4 ^ w := by rw [pow_mul]; norm_num
    have := Finset.sum_le_sum this
    simpa using this
  have : 3 * ∑ j ∈ Finset.Ico 0 n, 2 ^ (K j).card ≤ 3 * (n * 4 ^ w) := Nat.mul_le_mul_left 3 hsum
  have e : 3 * (n * 4 ^ w) = 3 * n * 4 ^ w := by ring
  omega
