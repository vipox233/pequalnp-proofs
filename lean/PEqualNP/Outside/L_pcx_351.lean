import PEqualNP.Defs

open scoped BigOperators

namespace PEqualNP.Outside.L_pcx_351_aux

abbrev UType (d : ℕ) := Fin d → ZMod 2
abbrev VType (m l r d : ℕ) := (Fin m → ZMod 2) × ((Fin r → Fin l → ZMod 2) × UType d)
abbrev OType (m l r d : ℕ) := Sum (Fin m) (Fin r × Fin l × UType d)

lemma zmod2_eq_of_decide_eq {a b c : ZMod 2}
    (h : decide (a = c) = decide (b = c)) : a = b := by
  revert a b c h
  decide

lemma zmod2_decide_eq_zero_false {a : ZMod 2} (h : decide (a = 0) = false) : a = 1 := by
  revert a h
  decide

lemma zmod2_decide_eq_zero_true {a : ZMod 2} (h : decide (a = 0) = true) : a = 0 := by
  revert a h
  decide

lemma zmod2_decide_eq_one_false {a : ZMod 2} (h : decide (a = 1) = false) : a = 0 := by
  revert a h
  decide

lemma zmod2_decide_eq_one_true {a : ZMod 2} (h : decide (a = 1) = true) : a = 1 := by
  revert a h
  decide

lemma pi_eq_sum_single {n : ℕ} (x : Fin n → ZMod 2) :
    x = ∑ i : Fin n, x i • Pi.single i (1 : ZMod 2) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

lemma linearMap_pi_eq_dot {n : ℕ} (l : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    ∃ v : Fin n → ZMod 2, ∀ x, l x = dotProduct v x := by
  refine ⟨fun i => l (Pi.single i 1), fun x => ?_⟩
  conv_lhs => rw [pi_eq_sum_single x]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma linearMap_V_decomp {m l r d : ℕ}
    (L : VType m l r d →ₗ[ZMod 2] ZMod 2) :
    ∃ (cx : Fin m → ZMod 2) (cy : Fin r → Fin l → ZMod 2) (cu : Fin d → ZMod 2),
      ∀ z : VType m l r d,
        L z = dotProduct cx z.1 + (∑ a : Fin r, dotProduct (cy a) (z.2.1 a)) + dotProduct cu z.2.2 := by
  let inX : (Fin m → ZMod 2) →ₗ[ZMod 2] VType m l r d :=
    LinearMap.inl (ZMod 2) (Fin m → ZMod 2) ((Fin r → Fin l → ZMod 2) × UType d)
  let inY : (Fin r → Fin l → ZMod 2) →ₗ[ZMod 2] VType m l r d :=
    (LinearMap.inr (ZMod 2) (Fin m → ZMod 2) ((Fin r → Fin l → ZMod 2) × UType d)).comp
      (LinearMap.inl (ZMod 2) (Fin r → Fin l → ZMod 2) (UType d))
  let inU : UType d →ₗ[ZMod 2] VType m l r d :=
    (LinearMap.inr (ZMod 2) (Fin m → ZMod 2) ((Fin r → Fin l → ZMod 2) × UType d)).comp
      (LinearMap.inr (ZMod 2) (Fin r → Fin l → ZMod 2) (UType d))
  obtain ⟨cx, hcx⟩ := linearMap_pi_eq_dot (L.comp inX)
  obtain ⟨cu, hcu⟩ := linearMap_pi_eq_dot (L.comp inU)
  have hcy_ex : ∀ a : Fin r, ∃ v : Fin l → ZMod 2,
      ∀ w : Fin l → ZMod 2, L (0, (Pi.single a w, 0)) = dotProduct v w := by
    intro a
    let inYa : (Fin l → ZMod 2) →ₗ[ZMod 2] (Fin r → Fin l → ZMod 2) :=
      LinearMap.single (R := ZMod 2) (φ := fun _ : Fin r => Fin l → ZMod 2) a
    obtain ⟨v, hv⟩ := linearMap_pi_eq_dot (L.comp (inY.comp inYa))
    exact ⟨v, fun w => hv w⟩
  choose cy hcy using hcy_ex
  refine ⟨cx, cy, cu, fun z => ?_⟩
  have hsplit : z = inX z.1 + inY z.2.1 + inU z.2.2 := by
    ext <;> simp [inX, inY, inU]
  have hy_sum : z.2.1 = ∑ a : Fin r, Pi.single a (z.2.1 a) := by
    ext a j
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne (Ne.symm hb)]
    · intro h
      exact absurd (Finset.mem_univ a) h
  conv_lhs => rw [hsplit]
  rw [map_add, map_add]
  have h1 : L (inX z.1) = dotProduct cx z.1 := hcx z.1
  have h3 : L (inU z.2.2) = dotProduct cu z.2.2 := hcu z.2.2
  have h2 : L (inY z.2.1) = ∑ a : Fin r, dotProduct (cy a) (z.2.1 a) := by
    conv_lhs => rw [hy_sum]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact hcy a (z.2.1 a)
  rw [h1, h2, h3]

def TreeShape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧
  (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
  ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

def Follows {V : Type} (q : List Bool → V → Bool) (p : List Bool) (x : V) : Prop :=
  ∀ j : Fin p.length, q (p.take j.val) x = p.get j

lemma shape_prefix_mem_J {N J : Finset (List Bool)} (hS : TreeShape N J)
    {p s : List Bool} (hmem : p ++ s ∈ N) (hne : s ≠ []) : p ∈ J := by
  induction s using List.reverseRecOn with
  | nil => exact absurd rfl hne
  | append_singleton s' b ih =>
    rw [← List.append_assoc] at hmem
    have hJ : p ++ s' ∈ J := hS.2.2.1 (p ++ s') b hmem
    cases s' with
    | nil => simpa using hJ
    | cons a t => exact ih (hS.2.1 hJ) (List.cons_ne_nil a t)

lemma shape_leaf_prefix_eq {N J : Finset (List Bool)} (hS : TreeShape N J)
    {p₁ p₂ : List Bool} (hp₁ : p₁ ∈ N \ J) (hp₂ : p₂ ∈ N) (hpre : p₁ <+: p₂) :
    p₁ = p₂ := by
  rcases hpre with ⟨s, hs⟩
  by_cases hnil : s = []
  · subst hnil; simpa using hs
  · exfalso
    exact (Finset.mem_sdiff.mp hp₁).2 (shape_prefix_mem_J hS (hs ▸ hp₂) hnil)

lemma follows_nil {V : Type} (q : List Bool → V → Bool) (x : V) :
    Follows q [] x := by
  intro j
  exact Fin.elim0 j

lemma follows_append_singleton {V : Type} (q : List Bool → V → Bool)
    (p : List Bool) (b : Bool) (x : V) :
    Follows q (p ++ [b]) x ↔ Follows q p x ∧ q p x = b := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j
      have hj : j.val < (p ++ [b]).length := by simp [Nat.lt_succ_of_lt j.isLt]
      have h1 := h ⟨j.val, hj⟩
      rw [List.take_append_of_le_length (le_of_lt j.isLt)] at h1
      have hget : (p ++ [b]).get ⟨j.val, hj⟩ = p.get j := by
        simp [List.getElem_append_left j.isLt]
      rw [hget] at h1
      exact h1
    · have hj : p.length < (p ++ [b]).length := by simp
      have h1 := h ⟨p.length, hj⟩
      rw [List.take_left] at h1
      have hget : (p ++ [b]).get ⟨p.length, hj⟩ = b := by simp
      rw [hget] at h1
      exact h1
  · rintro ⟨hp, hb⟩ j
    by_cases hlt : j.val < p.length
    · rw [List.take_append_of_le_length (le_of_lt hlt)]
      have hget : (p ++ [b]).get j = p.get ⟨j.val, hlt⟩ := by
        simp [List.getElem_append_left hlt]
      rw [hget]
      exact hp ⟨j.val, hlt⟩
    · have heq : j.val = p.length := by
        have hlen := j.isLt
        simp at hlen
        omega
      rw [heq, List.take_left]
      have hget : (p ++ [b]).get j = b := by simp [heq]
      rw [hget]
      exact hb

lemma follows_prefix {V : Type} (q : List Bool → V → Bool)
    {p p' : List Bool} (hpre : p <+: p') {x : V} (hf : Follows q p' x) :
    Follows q p x := by
  rcases hpre with ⟨s, rfl⟩
  induction s using List.reverseRecOn with
  | nil => simpa using hf
  | append_singleton s' b ih =>
    rw [← List.append_assoc] at hf
    exact ih ((follows_append_singleton q (p ++ s') b x).mp hf).1

lemma exists_leaf_follows_from {V : Type} {N J : Finset (List Bool)}
    (hS : TreeShape N J) (q : List Bool → V → Bool) (x : V) (fuel : ℕ) :
    ∀ p ∈ N, N.sup List.length - p.length ≤ fuel → Follows q p x →
      ∃ p' ∈ N \ J, p <+: p' ∧ Follows q p' x := by
  induction fuel with
  | zero =>
    intro p hp hfuel hf
    have hnotJ : p ∉ J := by
      intro hpJ
      have hchild : p ++ [false] ∈ N := (hS.2.2.2 p hpJ).1
      have hle : (p ++ [false]).length ≤ N.sup List.length :=
        Finset.le_sup (f := List.length) hchild
      simp only [List.length_append, List.length_singleton] at hle
      omega
    exact ⟨p, Finset.mem_sdiff.mpr ⟨hp, hnotJ⟩, List.prefix_refl p, hf⟩
  | succ fuel ih =>
    intro p hp hfuel hf
    by_cases hpJ : p ∈ J
    · set b := q p x
      have hc : p ++ [b] ∈ N := by
        cases hb : b
        · exact (hS.2.2.2 p hpJ).1
        · exact (hS.2.2.2 p hpJ).2
      have hfuel' : N.sup List.length - (p ++ [b]).length ≤ fuel := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hf' : Follows q (p ++ [b]) x := (follows_append_singleton q p b x).mpr ⟨hf, rfl⟩
      obtain ⟨p', hp', hpre, hfp'⟩ := ih (p ++ [b]) hc hfuel' hf'
      exact ⟨p', hp', List.IsPrefix.trans ⟨[b], rfl⟩ hpre, hfp'⟩
    · exact ⟨p, Finset.mem_sdiff.mpr ⟨hp, hpJ⟩, List.prefix_refl p, hf⟩

lemma exists_leaf_follows {V : Type} {N J : Finset (List Bool)}
    (hS : TreeShape N J) (q : List Bool → V → Bool) (x : V) :
    ∃ p ∈ N \ J, Follows q p x := by
  obtain ⟨p, hp, _, hf⟩ :=
    exists_leaf_follows_from hS q x (N.sup List.length) [] hS.1 (by simp) (follows_nil q x)
  exact ⟨p, hp, hf⟩

lemma shape_node_length_le {N J : Finset (List Bool)} (hS : TreeShape N J)
    {H : ℕ} (hH : ∀ p ∈ N \ J, p.length ≤ H) (fuel : ℕ) :
    ∀ p ∈ N, N.sup List.length - p.length ≤ fuel → p.length ≤ H := by
  induction fuel with
  | zero =>
    intro p hp hfuel
    have hnotJ : p ∉ J := by
      intro hpJ
      have hchild : p ++ [false] ∈ N := (hS.2.2.2 p hpJ).1
      have hle : (p ++ [false]).length ≤ N.sup List.length :=
        Finset.le_sup (f := List.length) hchild
      simp only [List.length_append, List.length_singleton] at hle
      omega
    exact hH p (Finset.mem_sdiff.mpr ⟨hp, hnotJ⟩)
  | succ fuel ih =>
    intro p hp hfuel
    by_cases hpJ : p ∈ J
    · have hc : p ++ [false] ∈ N := (hS.2.2.2 p hpJ).1
      have hfuel' : N.sup List.length - (p ++ [false]).length ≤ fuel := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hle := ih (p ++ [false]) hc hfuel'
      simp only [List.length_append, List.length_singleton] at hle
      omega
    · exact hH p (Finset.mem_sdiff.mpr ⟨hp, hpJ⟩)

lemma kraft_subtree {N J : Finset (List Bool)} (hS : TreeShape N J)
    {H : ℕ} (hH : ∀ p ∈ N \ J, p.length ≤ H) (rem : ℕ) :
    ∀ v ∈ N, H - v.length = rem →
      ((N \ J).filter (fun p => v <+: p)).sum (fun p => 2 ^ (H - p.length)) = 2 ^ rem := by
  induction rem with
  | zero =>
    intro v hv hrem
    have hnotJ : v ∉ J := by
      intro hvJ
      have hc : v ++ [false] ∈ N := (hS.2.2.2 v hvJ).1
      have hle := shape_node_length_le hS hH (N.sup List.length) (v ++ [false]) hc (by omega)
      simp only [List.length_append, List.length_singleton] at hle
      omega
    have hleaf : v ∈ N \ J := Finset.mem_sdiff.mpr ⟨hv, hnotJ⟩
    have hfilt : (N \ J).filter (fun p => v <+: p) = {v} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hp, hpre⟩
        exact (shape_leaf_prefix_eq hS hleaf (Finset.mem_sdiff.mp hp).1 hpre).symm
      · rintro rfl
        exact ⟨hleaf, List.prefix_refl _⟩
    rw [hfilt, Finset.sum_singleton, hrem]
  | succ rem ih =>
    intro v hv hrem
    by_cases hvJ : v ∈ J
    · have hc0 : v ++ [false] ∈ N := (hS.2.2.2 v hvJ).1
      have hc1 : v ++ [true] ∈ N := (hS.2.2.2 v hvJ).2
      have hrem0 : H - (v ++ [false]).length = rem := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hrem1 : H - (v ++ [true]).length = rem := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hsplit : (N \ J).filter (fun p => v <+: p) =
          (N \ J).filter (fun p => v ++ [false] <+: p) ∪
          (N \ J).filter (fun p => v ++ [true] <+: p) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hp, ⟨s, rfl⟩⟩
          cases s with
          | nil =>
            simp only [List.append_nil] at hp
            exact absurd hvJ (Finset.mem_sdiff.mp hp).2
          | cons b rest =>
            cases b
            · left; exact ⟨hp, ⟨rest, by simp⟩⟩
            · right; exact ⟨hp, ⟨rest, by simp⟩⟩
        · rintro (⟨hp, ⟨s, rfl⟩⟩ | ⟨hp, ⟨s, rfl⟩⟩)
          · exact ⟨hp, ⟨false :: s, by simp⟩⟩
          · exact ⟨hp, ⟨true :: s, by simp⟩⟩
      have hdisj : Disjoint
          ((N \ J).filter (fun p => v ++ [false] <+: p))
          ((N \ J).filter (fun p => v ++ [true] <+: p)) := by
        rw [Finset.disjoint_left]
        intro p h1 h2
        rcases (Finset.mem_filter.mp h1).2 with ⟨s₁, rfl⟩
        rcases (Finset.mem_filter.mp h2).2 with ⟨s₂, heq⟩
        have h' : v ++ ([false] ++ s₁) = v ++ ([true] ++ s₂) := by
          simp only [← List.append_assoc]
          exact heq.symm
        have htail := List.append_cancel_left h'
        cases htail
      rw [hsplit, Finset.sum_union hdisj, ih _ hc0 hrem0, ih _ hc1 hrem1, pow_succ, mul_two]
    · have hleaf : v ∈ N \ J := Finset.mem_sdiff.mpr ⟨hv, hvJ⟩
      have hfilt : (N \ J).filter (fun p => v <+: p) = {v} := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hp, hpre⟩
          exact (shape_leaf_prefix_eq hS hleaf (Finset.mem_sdiff.mp hp).1 hpre).symm
        · rintro rfl
          exact ⟨hleaf, List.prefix_refl _⟩
      rw [hfilt, Finset.sum_singleton, hrem]

def alphabetFinset {m l r d : ℕ} (f : UType d → Fin r) : Finset (OType m l r d) :=
  (Finset.univ : Finset (OType m l r d)).filter
    (fun o => Sum.elim (fun _ => true) (fun x : Fin r × Fin l × UType d => decide (x.1 = f x.2.2)) o = true)

lemma card_alphabetFinset {m l r d : ℕ} (f : UType d → Fin r) :
    (alphabetFinset (m := m) (l := l) f).card = m + 2 ^ d * l := by
  let leftImg : Finset (OType m l r d) := (Finset.univ : Finset (Fin m)).image Sum.inl
  let rightImg : Finset (OType m l r d) :=
    (Finset.univ : Finset (UType d × Fin l)).image (fun p => Sum.inr (f p.1, p.2, p.1))
  have heq : alphabetFinset (m := m) (l := l) f = leftImg ∪ rightImg := by
    ext o
    simp only [alphabetFinset, leftImg, rightImg, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_image]
    cases o with
    | inl i =>
      simp
    | inr x =>
      rcases x with ⟨a, j, u⟩
      simp only [Sum.elim_inr, decide_eq_true_eq, reduceCtorEq, exists_false, false_or,
        Sum.inr.injEq, Prod.mk.injEq]
      constructor
      · intro h
        exact ⟨(u, j), h.symm, rfl, rfl⟩
      · rintro ⟨⟨u', j'⟩, ha, rfl, rfl⟩
        exact ha.symm
  have hdisj : Disjoint leftImg rightImg := by
    rw [Finset.disjoint_left]
    intro o h1 h2
    simp only [leftImg, rightImg, Finset.mem_image, Finset.mem_univ, true_and] at h1 h2
    rcases h1 with ⟨i, rfl⟩
    rcases h2 with ⟨p, hEq⟩
    cases hEq
  have hinj1 : Function.Injective (Sum.inl : Fin m → OType m l r d) := fun _ _ h => Sum.inl.inj h
  have hinj2 : Function.Injective (fun p : UType d × Fin l => (Sum.inr (f p.1, p.2, p.1) : OType m l r d)) := by
    intro p₁ p₂ h
    have h' := Sum.inr.inj h
    rcases p₁ with ⟨u₁, j₁⟩
    rcases p₂ with ⟨u₂, j₂⟩
    simp only [Prod.mk.injEq] at h'
    ext
    · exact congrFun h'.2.2 _
    · exact congrArg Fin.val h'.2.1
  rw [heq, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hinj1,
    Finset.card_image_of_injective _ hinj2,
    Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_fin]

def Promised {m l r d : ℕ} (z : VType m l r d) : Prop :=
  ∀ a : Fin r, (∑ i, z.1 i) + (∑ j, z.2.1 a j) = 1

def OkProp {m l r d : ℕ} (z : VType m l r d) (o : OType m l r d) : Prop :=
  Promised z →
    Sum.elim (fun i => z.1 i = 1) (fun x : Fin r × Fin l × UType d => z.2.1 x.1 x.2.1 = 1 ∧ x.2.2 = z.2.2) o

lemma zCommon_promised {m l r d : ℕ} (i : Fin m) (u : UType d) :
    Promised (l := l) (r := r) (Pi.single i (1 : ZMod 2), (0, u)) := by
  intro a
  simp

lemma zPriv_promised {m l r d : ℕ} (g : Fin r → Fin l → ZMod 2) (u : UType d)
    (hg : ∀ a : Fin r, ∑ j : Fin l, g a j = 1) :
    Promised (m := m) (0, (g, u)) := by
  intro a
  simp [hg a]

lemma forward_dir (m l r d : ℕ) (hl : 0 < l) (_hr : 0 < r) (f : UType d → Fin r) (H : ℕ)
    (N J : Finset (List Bool))
    (q : List Bool → VType m l r d → Bool)
    (out : List Bool → OType m l r d)
    (hshape : TreeShape N J)
    (hq : ∀ p ∈ J, ∃ (L : VType m l r d →ₗ[ZMod 2] ZMod 2) (b : ZMod 2),
      q p = fun z => decide (L z = b))
    (hcert : ∀ p ∈ N \ J, ∀ z : VType m l r d, Follows q p z → OkProp z (out p))
    (hcard : (N \ J).card = m + 2 ^ d * l)
    (himg : (N \ J).image out = alphabetFinset (m := m) (l := l) f)
    (hH : ∀ p ∈ N \ J, p.length ≤ H) :
    m + 2 ^ d * l ≤ 2 ^ H ∧
      ((∃ a, ∀ u, f u = a) ∨ ∃ e : ℕ, 2 ^ d * l ≤ 2 ^ e ∧ m + 2 ^ e ≤ 2 ^ H) := by
  have hW_le : m + 2 ^ d * l ≤ 2 ^ H := by
    have hkraft := kraft_subtree hshape hH H [] hshape.1 (by simp)
    have hfilt : (N \ J).filter (fun p => [] <+: p) = N \ J := by
      ext p; simp
    rw [hfilt] at hkraft
    calc m + 2 ^ d * l = (N \ J).card := hcard.symm
      _ = (N \ J).sum (fun _ => 1) := by simp
      _ ≤ (N \ J).sum (fun p => 2 ^ (H - p.length)) :=
          Finset.sum_le_sum fun p _ => Nat.one_le_pow _ _ (by omega)
      _ = 2 ^ H := hkraft
  refine ⟨hW_le, ?_⟩
  by_cases hconst : ∃ a : Fin r, ∀ u : UType d, f u = a
  · exact Or.inl hconst
  · right
    have hinj := Finset.injOn_of_card_image_eq (s := N \ J) (f := out)
      (by rw [himg, card_alphabetFinset, hcard])
    have hex_leaf : ∀ o ∈ alphabetFinset (m := m) (l := l) f,
        ∃ p ∈ N \ J, out p = o := by
      intro o ho
      rw [← himg, Finset.mem_image] at ho
      exact ho
    have hleaf_unique : ∀ {p₁ p₂ : List Bool}, p₁ ∈ N \ J → p₂ ∈ N \ J →
        out p₁ = out p₂ → p₁ = p₂ :=
      fun hp₁ hp₂ heq => hinj hp₁ hp₂ heq
    have hcomm_mem : ∀ i : Fin m, (Sum.inl i : OType m l r d) ∈ alphabetFinset (m := m) (l := l) f := by
      intro i
      simp [alphabetFinset]
    have hpriv_mem : ∀ (u : UType d) (j : Fin l),
        (Sum.inr (f u, j, u) : OType m l r d) ∈ alphabetFinset (m := m) (l := l) f := by
      intro u j
      simp [alphabetFinset]
    choose commLeaf hcommLeaf using fun i : Fin m => hex_leaf (Sum.inl i) (hcomm_mem i)
    choose privLeaf hprivLeaf using fun (u : UType d) (j : Fin l) =>
      hex_leaf (Sum.inr (f u, j, u)) (hpriv_mem u j)
    have hcomm_forced : ∀ (i : Fin m) (u : UType d),
        Follows q (commLeaf i) (Pi.single i (1 : ZMod 2), (0, u)) := by
      intro i u
      obtain ⟨p, hp, hfp⟩ := exists_leaf_follows hshape q (Pi.single i (1 : ZMod 2), (0, u))
      have hok := hcert p hp _ hfp (zCommon_promised i u)
      have hout_eq : out p = Sum.inl i := by
        cases ho : out p with
        | inl i' =>
          rw [ho] at hok
          simp only [Sum.elim_inl, Pi.single_apply] at hok
          by_cases hii' : i' = i
          · subst hii'; rfl
          · simp [hii'] at hok
        | inr x =>
          rw [ho] at hok
          simp at hok
      have hp_eq : p = commLeaf i := hleaf_unique hp (hcommLeaf i).1 (hout_eq.trans (hcommLeaf i).2.symm)
      rw [← hp_eq]
      exact hfp
    have hpriv_forced : ∀ (u : UType d) (j : Fin l) (g : Fin r → Fin l → ZMod 2),
        (∀ a : Fin r, ∑ j' : Fin l, g a j' = 1) →
        g (f u) = Pi.single j (1 : ZMod 2) →
        Follows q (privLeaf u j) (0, (g, u)) := by
      intro u j g hsum hgf
      obtain ⟨p, hp, hfp⟩ := exists_leaf_follows hshape q (0, (g, u))
      have hok := hcert p hp _ hfp (zPriv_promised g u hsum)
      have hmem_alpha : out p ∈ alphabetFinset (m := m) (l := l) f := by
        rw [← himg]
        exact Finset.mem_image_of_mem out hp
      have hout_eq : out p = Sum.inr (f u, j, u) := by
        cases ho : out p with
        | inl i =>
          rw [ho] at hok
          simp at hok
        | inr x =>
          rcases x with ⟨a, j', u'⟩
          rw [ho] at hok hmem_alpha
          simp only [Sum.elim_inr] at hok
          simp only [alphabetFinset, Finset.mem_filter, Finset.mem_univ, true_and, Sum.elim_inr,
            decide_eq_true_eq] at hmem_alpha
          rcases hok with ⟨hgj, hu'⟩
          subst hu'
          subst hmem_alpha
          rw [hgf] at hgj
          simp only [Pi.single_apply] at hgj
          by_cases hjj' : j' = j
          · subst hjj'; rfl
          · simp [hjj'] at hgj
      have hp_eq : p = privLeaf u j :=
        hleaf_unique hp (hprivLeaf u j).1 (hout_eq.trans (hprivLeaf u j).2.symm)
      rw [← hp_eq]
      exact hfp
    have hstep_sep : ∀ v ∈ J,
        (∀ u j, v <+: privLeaf u j) →
        (∃ i₀ : Fin m, v <+: commLeaf i₀) →
        ∃ b : Bool, ∀ u j, v ++ [b] <+: privLeaf u j := by
      intro v hvJ hall_priv ⟨i₀, hi₀⟩
      obtain ⟨L, qb, hqv⟩ := hq v hvJ
      obtain ⟨cx, cy, cu, hL⟩ := linearMap_V_decomp L
      have hlen_lt_comm : v.length < (commLeaf i₀).length := by
        rcases hi₀ with ⟨s, hs⟩
        cases s with
        | nil =>
          simp only [List.append_nil] at hs
          exact absurd (hs ▸ hvJ) (Finset.mem_sdiff.mp (hcommLeaf i₀).1).2
        | cons c rest =>
          rw [← hs]; simp
      have hlen_lt_priv : ∀ u j, v.length < (privLeaf u j).length := by
        intro u j
        rcases hall_priv u j with ⟨s, hs⟩
        cases s with
        | nil =>
          simp only [List.append_nil] at hs
          exact absurd (hs ▸ hvJ) (Finset.mem_sdiff.mp (hprivLeaf u j).1).2
        | cons c rest =>
          rw [← hs]; simp
      have hqv_comm : ∀ u : UType d,
          q v (Pi.single i₀ (1 : ZMod 2), (0, u)) = (commLeaf i₀).get ⟨v.length, hlen_lt_comm⟩ := by
        intro u
        have hf := hcomm_forced i₀ u ⟨v.length, hlen_lt_comm⟩
        rcases hi₀ with ⟨s, hs⟩
        have htake : (commLeaf i₀).take v.length = v := by
          rw [← hs, List.take_left]
        rw [htake] at hf
        exact hf
      have hqv_priv : ∀ (u : UType d) (j : Fin l) (g : Fin r → Fin l → ZMod 2),
          (∀ a : Fin r, ∑ j' : Fin l, g a j' = 1) →
          g (f u) = Pi.single j (1 : ZMod 2) →
          q v (0, (g, u)) = (privLeaf u j).get ⟨v.length, hlen_lt_priv u j⟩ := by
        intro u j g hsum hgf
        have hf := hpriv_forced u j g hsum hgf ⟨v.length, hlen_lt_priv u j⟩
        rcases hall_priv u j with ⟨s, hs⟩
        have htake : (privLeaf u j).take v.length = v := by
          rw [← hs, List.take_left]
        rw [htake] at hf
        exact hf
      have hcu0 : cu = 0 := by
        ext t
        have h0 := hqv_comm 0
        have h1 := hqv_comm (Pi.single t 1)
        have heq : q v (Pi.single i₀ 1, (0, Pi.single t 1)) = q v (Pi.single i₀ 1, (0, 0)) :=
          h1.trans h0.symm
        rw [hqv] at heq
        have hLeq := zmod2_eq_of_decide_eq heq
        rw [hL, hL] at hLeq
        simp only [Pi.zero_apply, dotProduct_zero, Finset.sum_const_zero, add_zero,
          dotProduct_single, mul_one] at hLeq
        have hLeq' : cx i₀ + cu t = cx i₀ + 0 := by simpa using hLeq
        exact add_left_cancel hLeq'
      have hcy_const : ∀ (a : Fin r) (j₁ j₂ : Fin l), cy a j₁ = cy a j₂ := by
        intro a j₁ j₂
        have hex_u : ∃ u : UType d, f u ≠ a := by
          by_contra h
          push Not at h
          exact hconst ⟨a, h⟩
        rcases hex_u with ⟨u, hne_a⟩
        let j₀ : Fin l := ⟨0, hl⟩
        let g₁ : Fin r → Fin l → ZMod 2 := fun a' =>
          if a' = a then Pi.single j₁ 1 else Pi.single j₀ 1
        let g₂ : Fin r → Fin l → ZMod 2 := fun a' =>
          if a' = a then Pi.single j₂ 1 else Pi.single j₀ 1
        have hg1_sum : ∀ a' : Fin r, ∑ j' : Fin l, g₁ a' j' = 1 := by
          intro a'
          by_cases ha' : a' = a <;> simp [g₁, ha']
        have hg2_sum : ∀ a' : Fin r, ∑ j' : Fin l, g₂ a' j' = 1 := by
          intro a'
          by_cases ha' : a' = a <;> simp [g₂, ha']
        have hg1_f : g₁ (f u) = Pi.single j₀ 1 := by simp [g₁, hne_a]
        have hg2_f : g₂ (f u) = Pi.single j₀ 1 := by simp [g₂, hne_a]
        have heq : q v (0, (g₁, u)) = q v (0, (g₂, u)) :=
          (hqv_priv u j₀ g₁ hg1_sum hg1_f).trans (hqv_priv u j₀ g₂ hg2_sum hg2_f).symm
        rw [hqv] at heq
        have hLeq := zmod2_eq_of_decide_eq heq
        rw [hL, hL] at hLeq
        simp only [dotProduct_zero, zero_add, hcu0, zero_dotProduct, add_zero] at hLeq
        have hsum_eq : (∑ a' : Fin r, dotProduct (cy a') (g₁ a')) =
            (∑ a' : Fin r, dotProduct (cy a') (g₂ a')) := hLeq
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at hsum_eq
        have hrest : (∑ a' ∈ Finset.univ.erase a, dotProduct (cy a') (g₁ a')) =
            (∑ a' ∈ Finset.univ.erase a, dotProduct (cy a') (g₂ a')) := by
          refine Finset.sum_congr rfl fun a' ha' => ?_
          have hne' : a' ≠ a := (Finset.mem_erase.mp ha').1
          simp [g₁, g₂, hne']
        rw [hrest] at hsum_eq
        have hdot_eq := add_right_cancel hsum_eq
        simpa [g₁, g₂, dotProduct_single] using hdot_eq
      let b_priv : Bool := decide ((∑ a : Fin r, cy a ⟨0, hl⟩) = qb)
      refine ⟨b_priv, fun u j => ?_⟩
      let g : Fin r → Fin l → ZMod 2 := fun _ => Pi.single j 1
      have hg_sum : ∀ a : Fin r, ∑ j' : Fin l, g a j' = 1 := fun _ => by
        simp [g]
      have hbit := hqv_priv u j g hg_sum rfl
      have hval : q v (0, (g, u)) = b_priv := by
        rw [hqv]
        simp only
        rw [hL]
        simp only [dotProduct_zero, zero_add, hcu0, zero_dotProduct, add_zero]
        have hsum_cy : (∑ a : Fin r, dotProduct (cy a) (g a)) = ∑ a : Fin r, cy a ⟨0, hl⟩ := by
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [g, dotProduct_single, mul_one]
          exact hcy_const a j ⟨0, hl⟩
        rw [hsum_cy]
      have hget_eq : (privLeaf u j).get ⟨v.length, hlen_lt_priv u j⟩ = b_priv :=
        hbit.symm.trans hval
      rcases hall_priv u j with ⟨s, hs⟩
      cases s with
      | nil =>
        simp only [List.append_nil] at hs
        exact absurd (hs ▸ hvJ) (Finset.mem_sdiff.mp (hprivLeaf u j).1).2
      | cons c rest =>
        have hc_eq : c = b_priv := by
          have hget' : (privLeaf u j).get ⟨v.length, hlen_lt_priv u j⟩ = c := by
            have h1 : (v ++ c :: rest)[v.length]'(by simp) = c := by simp
            simpa [hs] using h1
          exact hget'.symm.trans hget_eq
        subst hc_eq
        exact ⟨rest, by simpa [List.append_assoc] using hs⟩
    have hex_pure_node : ∀ (rem : ℕ) (v : List Bool), v ∈ N → H - v.length = rem →
        (∀ u j, v <+: privLeaf u j) →
        ∃ w ∈ N, (∀ u j, w <+: privLeaf u j) ∧ (∀ i : Fin m, ¬ (w <+: commLeaf i)) := by
      intro rem
      induction rem with
      | zero =>
        intro v hv hrem hall_priv
        refine ⟨v, hv, hall_priv, ?_⟩
        intro i₀ hi₀
        have hvnotJ : v ∉ J := by
          intro hvJ
          have hc : v ++ [false] ∈ N := (hshape.2.2.2 v hvJ).1
          have hle := shape_node_length_le hshape hH (N.sup List.length) (v ++ [false]) hc (by omega)
          simp only [List.length_append, List.length_singleton] at hle
          omega
        have hvleaf : v ∈ N \ J := Finset.mem_sdiff.mpr ⟨hv, hvnotJ⟩
        have heq1 : v = commLeaf i₀ := shape_leaf_prefix_eq hshape hvleaf (Finset.mem_sdiff.mp (hcommLeaf i₀).1).1 hi₀
        have heq2 : v = privLeaf 0 ⟨0, hl⟩ :=
          shape_leaf_prefix_eq hshape hvleaf (Finset.mem_sdiff.mp (hprivLeaf 0 ⟨0, hl⟩).1).1 (hall_priv 0 ⟨0, hl⟩)
        have hout_eq : out (commLeaf i₀) = out (privLeaf 0 ⟨0, hl⟩) := by
          rw [← heq1, ← heq2]
        rw [(hcommLeaf i₀).2, (hprivLeaf 0 ⟨0, hl⟩).2] at hout_eq
        cases hout_eq
      | succ rem ih =>
        intro v hv hrem hall_priv
        by_cases hcomm_in : ∃ i₀ : Fin m, v <+: commLeaf i₀
        · rcases hcomm_in with ⟨i₀, hi₀⟩
          have hvJ : v ∈ J := by
            by_contra hvnotJ
            have hvleaf : v ∈ N \ J := Finset.mem_sdiff.mpr ⟨hv, hvnotJ⟩
            have heq1 : v = commLeaf i₀ :=
              shape_leaf_prefix_eq hshape hvleaf (Finset.mem_sdiff.mp (hcommLeaf i₀).1).1 hi₀
            have heq2 : v = privLeaf 0 ⟨0, hl⟩ :=
              shape_leaf_prefix_eq hshape hvleaf (Finset.mem_sdiff.mp (hprivLeaf 0 ⟨0, hl⟩).1).1 (hall_priv 0 ⟨0, hl⟩)
            have hout_eq : out (commLeaf i₀) = out (privLeaf 0 ⟨0, hl⟩) := by
              rw [← heq1, ← heq2]
            rw [(hcommLeaf i₀).2, (hprivLeaf 0 ⟨0, hl⟩).2] at hout_eq
            cases hout_eq
          obtain ⟨b, hb⟩ := hstep_sep v hvJ hall_priv ⟨i₀, hi₀⟩
          have hvc : v ++ [b] ∈ N := by
            cases b
            · exact (hshape.2.2.2 v hvJ).1
            · exact (hshape.2.2.2 v hvJ).2
          have hrem' : H - (v ++ [b]).length = rem := by
            simp only [List.length_append, List.length_singleton]
            omega
          exact ih (v ++ [b]) hvc hrem' hb
        · push Not at hcomm_in
          exact ⟨v, hv, hall_priv, hcomm_in⟩
    obtain ⟨w, hwN, hall_priv, hno_comm⟩ :=
      hex_pure_node H [] hshape.1 (by simp) (fun _ _ => List.nil_prefix)
    set e := H - w.length
    set subL := (N \ J).filter (fun p => w <+: p)
    have hsub_card : subL.card = 2 ^ d * l := by
      have heq_img : subL = (Finset.univ : Finset (UType d × Fin l)).image (fun p => privLeaf p.1 p.2) := by
        ext p
        simp only [subL, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hp, hpre⟩
          have hmem_a : out p ∈ alphabetFinset (m := m) (l := l) f := by
            rw [← himg]
            exact Finset.mem_image_of_mem out hp
          cases ho : out p with
          | inl i =>
            have hp_eq : p = commLeaf i := hleaf_unique hp (hcommLeaf i).1 (ho.trans (hcommLeaf i).2.symm)
            rw [hp_eq] at hpre
            exact absurd hpre (hno_comm i)
          | inr x =>
            rcases x with ⟨a, j, u⟩
            rw [ho] at hmem_a
            simp only [alphabetFinset, Finset.mem_filter, Finset.mem_univ, true_and, Sum.elim_inr,
              decide_eq_true_eq] at hmem_a
            subst hmem_a
            have hp_eq : p = privLeaf u j := hleaf_unique hp (hprivLeaf u j).1 (ho.trans (hprivLeaf u j).2.symm)
            exact ⟨(u, j), hp_eq.symm⟩
        · rintro ⟨⟨u, j⟩, rfl⟩
          exact ⟨(hprivLeaf u j).1, hall_priv u j⟩
      have hinj_priv : Function.Injective (fun p : UType d × Fin l => privLeaf p.1 p.2) := by
        intro p₁ p₂ heq
        have hout_eq := congrArg out heq
        rw [(hprivLeaf p₁.1 p₁.2).2, (hprivLeaf p₂.1 p₂.2).2] at hout_eq
        have h' := Sum.inr.inj hout_eq
        rcases p₁ with ⟨u₁, j₁⟩
        rcases p₂ with ⟨u₂, j₂⟩
        simp only [Prod.mk.injEq] at h'
        ext
        · exact congrFun h'.2.2 _
        · exact congrArg Fin.val h'.2.1
      rw [heq_img, Finset.card_image_of_injective _ hinj_priv, Finset.card_univ,
        Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_fin]
    have hkraft_w : subL.sum (fun p => 2 ^ (H - p.length)) = 2 ^ e :=
      kraft_subtree hshape hH e w hwN rfl
    have hP_le : 2 ^ d * l ≤ 2 ^ e := by
      calc 2 ^ d * l = subL.card := hsub_card.symm
        _ = subL.sum (fun _ => 1) := by simp
        _ ≤ subL.sum (fun p => 2 ^ (H - p.length)) :=
            Finset.sum_le_sum fun p _ => Nat.one_le_pow _ _ (by omega)
        _ = 2 ^ e := hkraft_w
    have hkraft_all : (N \ J).sum (fun p => 2 ^ (H - p.length)) = 2 ^ H := by
      have h := kraft_subtree hshape hH H [] hshape.1 (by simp)
      have hfilt : (N \ J).filter (fun p => [] <+: p) = N \ J := by ext p; simp
      rw [hfilt] at h
      exact h
    have hsub_ss : subL ⊆ N \ J := Finset.filter_subset _ _
    have hrest_card : ((N \ J) \ subL).card = m := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub_ss, hcard, hsub_card]
      omega
    have hm_add_le : m + 2 ^ e ≤ 2 ^ H := by
      have hsum_split : (N \ J).sum (fun p => 2 ^ (H - p.length)) =
          ((N \ J) \ subL).sum (fun p => 2 ^ (H - p.length)) +
          subL.sum (fun p => 2 ^ (H - p.length)) := by
        rw [← Finset.sum_union Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hsub_ss]
      have hrest_ge : m ≤ ((N \ J) \ subL).sum (fun p => 2 ^ (H - p.length)) := by
        calc m = ((N \ J) \ subL).card := hrest_card.symm
          _ = ((N \ J) \ subL).sum (fun _ => 1) := by simp
          _ ≤ ((N \ J) \ subL).sum (fun p => 2 ^ (H - p.length)) :=
              Finset.sum_le_sum fun p _ => Nat.one_le_pow _ _ (by omega)
      omega
    exact ⟨e, hP_le, hm_add_le⟩

inductive PTree (V O : Type)
  | leaf (o : O)
  | node (f : V → Bool) (lo hi : PTree V O)

def PTree.nodes {V O : Type} : PTree V O → Finset (List Bool)
  | .leaf _ => {[]}
  | .node _ lo hi => insert [] ((lo.nodes.image (false :: ·)) ∪ (hi.nodes.image (true :: ·)))

def PTree.internal {V O : Type} : PTree V O → Finset (List Bool)
  | .leaf _ => ∅
  | .node _ lo hi => insert [] ((lo.internal.image (false :: ·)) ∪ (hi.internal.image (true :: ·)))

def PTree.leaves {V O : Type} : PTree V O → Finset (List Bool)
  | .leaf _ => {[]}
  | .node _ lo hi => (lo.leaves.image (false :: ·)) ∪ (hi.leaves.image (true :: ·))

def PTree.queryAt {V O : Type} : PTree V O → List Bool → (V → Bool)
  | .leaf _, _ => fun _ => false
  | .node f _ _, [] => f
  | .node _ lo _, false :: p => lo.queryAt p
  | .node _ _ hi, true :: p => hi.queryAt p

def PTree.outAt {V O : Type} : PTree V O → List Bool → O
  | .leaf o, _ => o
  | .node _ lo _, [] => lo.outAt []
  | .node _ lo _, false :: p => lo.outAt p
  | .node _ _ hi, true :: p => hi.outAt p

def PTree.leafCount {V O : Type} : PTree V O → ℕ
  | .leaf _ => 1
  | .node _ lo hi => lo.leafCount + hi.leafCount

def PTree.leafImage {V O : Type} [DecidableEq O] : PTree V O → Finset O
  | .leaf o => {o}
  | .node _ lo hi => lo.leafImage ∪ hi.leafImage

def PTree.height {V O : Type} : PTree V O → ℕ
  | .leaf _ => 0
  | .node _ lo hi => 1 + max lo.height hi.height

def PTree.AllQueries {V O : Type} (P : (V → Bool) → Prop) : PTree V O → Prop
  | .leaf _ => True
  | .node f lo hi => P f ∧ lo.AllQueries P ∧ hi.AllQueries P

def PTree.Valid {V O : Type} (ok : V → O → Prop) : (V → Prop) → PTree V O → Prop
  | pre, .leaf o => ∀ z, pre z → ok z o
  | pre, .node f lo hi =>
      lo.Valid ok (fun z => pre z ∧ f z = false) ∧
      hi.Valid ok (fun z => pre z ∧ f z = true)

lemma PTree.nil_mem_nodes {V O : Type} (t : PTree V O) : [] ∈ t.nodes := by
  cases t <;> simp [PTree.nodes]

lemma PTree.internal_subset_nodes {V O : Type} (t : PTree V O) : t.internal ⊆ t.nodes := by
  induction t with
  | leaf _ => simp [PTree.internal]
  | node _ lo hi ihlo ihhi =>
    intro p hp
    simp only [PTree.internal, PTree.nodes, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image] at hp ⊢
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · left; rfl
    · right; left; exact ⟨q, ihlo hq, rfl⟩
    · right; right; exact ⟨q, ihhi hq, rfl⟩

lemma PTree.shape {V O : Type} (t : PTree V O) : TreeShape t.nodes t.internal := by
  refine ⟨t.nil_mem_nodes, t.internal_subset_nodes, ?_, ?_⟩
  · induction t with
    | leaf _ =>
      intro p b hmem
      simp [PTree.nodes] at hmem
    | node _ lo hi ihlo ihhi =>
      intro p b hmem
      cases p with
      | nil => simp [PTree.internal]
      | cons c p' =>
        simp only [List.cons_append, PTree.nodes, Finset.mem_insert, Finset.mem_union,
          Finset.mem_image, List.cons_ne_nil, false_or] at hmem
        simp only [PTree.internal, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
        cases c
        · rcases hmem with ⟨q, hq, hEq⟩ | ⟨q, _, hEq⟩
          · injection hEq with _ hEq'
            subst hEq'
            right; left; exact ⟨p', ihlo p' b hq, rfl⟩
          · cases hEq
        · rcases hmem with ⟨q, _, hEq⟩ | ⟨q, hq, hEq⟩
          · cases hEq
          · injection hEq with _ hEq'
            subst hEq'
            right; right; exact ⟨p', ihhi p' b hq, rfl⟩
  · induction t with
    | leaf _ =>
      intro p hp
      simp [PTree.internal] at hp
    | node _ lo hi ihlo ihhi =>
      intro p hp
      simp only [PTree.internal, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
      rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · constructor
        · simp only [List.nil_append, PTree.nodes, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          right; left; exact ⟨[], lo.nil_mem_nodes, rfl⟩
        · simp only [List.nil_append, PTree.nodes, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          right; right; exact ⟨[], hi.nil_mem_nodes, rfl⟩
      · rcases ihlo q hq with ⟨h1, h2⟩
        constructor
        · simp only [List.cons_append, PTree.nodes, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          right; left; exact ⟨q ++ [false], h1, rfl⟩
        · simp only [List.cons_append, PTree.nodes, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          right; left; exact ⟨q ++ [true], h2, rfl⟩
      · rcases ihhi q hq with ⟨h1, h2⟩
        constructor
        · simp only [List.cons_append, PTree.nodes, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          right; right; exact ⟨q ++ [false], h1, rfl⟩
        · simp only [List.cons_append, PTree.nodes, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          right; right; exact ⟨q ++ [true], h2, rfl⟩

lemma PTree.sdiff_eq_leaves {V O : Type} (t : PTree V O) : t.nodes \ t.internal = t.leaves := by
  induction t with
  | leaf _ => simp [PTree.nodes, PTree.internal, PTree.leaves]
  | node _ lo hi ihlo ihhi =>
    ext p
    simp only [Finset.mem_sdiff, PTree.nodes, PTree.internal, PTree.leaves,
      Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    cases p with
    | nil => simp
    | cons b p' =>
      cases b
      · have hmem : p' ∈ lo.nodes \ lo.internal ↔ p' ∈ lo.leaves := by rw [ihlo]
        simp only [Finset.mem_sdiff] at hmem
        simpa [List.cons_ne_nil] using hmem
      · have hmem : p' ∈ hi.nodes \ hi.internal ↔ p' ∈ hi.leaves := by rw [ihhi]
        simp only [Finset.mem_sdiff] at hmem
        simpa [List.cons_ne_nil] using hmem

lemma PTree.card_leaves {V O : Type} (t : PTree V O) : t.leaves.card = t.leafCount := by
  induction t with
  | leaf _ => simp [PTree.leaves, PTree.leafCount]
  | node _ lo hi ihlo ihhi =>
    simp only [PTree.leaves, PTree.leafCount]
    have hdisj : Disjoint (lo.leaves.image (false :: ·)) (hi.leaves.image (true :: ·)) := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨_, _, hEq⟩
      cases hEq
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2),
      Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2),
      ihlo, ihhi]

lemma PTree.image_leaves {V O : Type} [DecidableEq O] (t : PTree V O) :
    t.leaves.image t.outAt = t.leafImage := by
  induction t with
  | leaf o => simp [PTree.leaves, PTree.outAt, PTree.leafImage]
  | node _ lo hi ihlo ihhi =>
    simp only [PTree.leaves, PTree.leafImage, Finset.image_union, Finset.image_image]
    rw [← ihlo, ← ihhi]
    rfl

lemma PTree.length_le_height {V O : Type} (t : PTree V O) :
    ∀ p ∈ t.leaves, p.length ≤ t.height := by
  induction t with
  | leaf _ =>
    intro p hp
    simp [PTree.leaves] at hp
    subst hp
    simp [PTree.height]
  | node _ lo hi ihlo ihhi =>
    intro p hp
    simp only [PTree.leaves, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · have := ihlo q hq
      simp only [List.length_cons, PTree.height]
      omega
    · have := ihhi q hq
      simp only [List.length_cons, PTree.height]
      omega

lemma PTree.allQueries_spec {V O : Type} {P : (V → Bool) → Prop} (t : PTree V O)
    (h : t.AllQueries P) : ∀ p ∈ t.internal, P (t.queryAt p) := by
  induction t with
  | leaf _ =>
    intro p hp
    simp [PTree.internal] at hp
  | node f lo hi ihlo ihhi =>
    rcases h with ⟨hf, hlo, hhi⟩
    intro p hp
    simp only [PTree.internal, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact hf
    · exact ihlo hlo q hq
    · exact ihhi hhi q hq

lemma PTree.follows_node_cons {V O : Type} (f : V → Bool) (lo hi : PTree V O)
    (b : Bool) (p : List Bool) (x : V) :
    Follows (PTree.node f lo hi).queryAt (b :: p) x →
      f x = b ∧ Follows (if b then hi else lo).queryAt p x := by
  intro hf
  refine ⟨?_, ?_⟩
  · have h0 := hf ⟨0, by simp⟩
    simpa [PTree.queryAt] using h0
  · intro j
    have hj := hf ⟨j.val + 1, by simp [j.isLt]⟩
    cases b <;> simpa [PTree.queryAt] using hj

lemma PTree.valid_spec {V O : Type} {ok : V → O → Prop} (t : PTree V O) :
    ∀ (pre : V → Prop), t.Valid ok pre →
      ∀ p ∈ t.leaves, ∀ z : V, pre z → Follows t.queryAt p z → ok z (t.outAt p) := by
  induction t with
  | leaf o =>
    intro pre hv p hp z hpre _
    simp only [PTree.outAt]
    exact hv z hpre
  | node f lo hi ihlo ihhi =>
    intro pre hv p hp z hpre hf
    rcases hv with ⟨hlo, hhi⟩
    simp only [PTree.leaves, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · obtain ⟨hfb, hfq⟩ := PTree.follows_node_cons f lo hi false q z hf
      exact ihlo _ hlo q hq z ⟨hpre, hfb⟩ hfq
    · obtain ⟨hfb, hfq⟩ := PTree.follows_node_cons f lo hi true q z hf
      exact ihhi _ hhi q hq z ⟨hpre, hfb⟩ hfq

lemma PTree.valid_mono {V O : Type} {ok : V → O → Prop} (t : PTree V O) :
    ∀ {pre₁ pre₂ : V → Prop}, (∀ z, pre₁ z → pre₂ z) → t.Valid ok pre₂ → t.Valid ok pre₁ := by
  induction t with
  | leaf o =>
    intro pre₁ pre₂ himp hv z h1
    exact hv z (himp z h1)
  | node f lo hi ihlo ihhi =>
    intro pre₁ pre₂ himp ⟨hlo, hhi⟩
    exact ⟨ihlo (fun z ⟨h1, h2⟩ => ⟨himp z h1, h2⟩) hlo,
      ihhi (fun z ⟨h1, h2⟩ => ⟨himp z h1, h2⟩) hhi⟩

structure PItem (V O : Type) [AddCommGroup V] [Module (ZMod 2) V] where
  lin : V →ₗ[ZMod 2] ZMod 2
  deg : ℕ
  tree : PTree V O

def itemWeight {V O : Type} [AddCommGroup V] [Module (ZMod 2) V] (xs : List (PItem V O)) : ℕ :=
  (xs.map (fun it => 2 ^ it.deg)).sum

def insertDesc {V O : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (x : PItem V O) : List (PItem V O) → List (PItem V O)
  | [] => [x]
  | y :: ys => if y.deg ≤ x.deg then x :: y :: ys else y :: insertDesc x ys

def sortDesc {V O : Type} [AddCommGroup V] [Module (ZMod 2) V] :
    List (PItem V O) → List (PItem V O)
  | [] => []
  | x :: xs => insertDesc x (sortDesc xs)

lemma insertDesc_perm {V O : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (x : PItem V O) (ys : List (PItem V O)) : (insertDesc x ys).Perm (x :: ys) := by
  induction ys with
  | nil => simp [insertDesc]
  | cons y ys ih =>
    unfold insertDesc
    split_ifs
    · exact List.Perm.refl _
    · exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

lemma sortDesc_perm {V O : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (xs : List (PItem V O)) : (sortDesc xs).Perm xs := by
  induction xs with
  | nil => simp [sortDesc]
  | cons x xs ih =>
    exact (insertDesc_perm x (sortDesc xs)).trans (List.Perm.cons x ih)

lemma insertDesc_pairwise {V O : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (x : PItem V O) (ys : List (PItem V O))
    (h : ys.Pairwise (fun a b => b.deg ≤ a.deg)) :
    (insertDesc x ys).Pairwise (fun a b => b.deg ≤ a.deg) := by
  induction ys with
  | nil => simp [insertDesc]
  | cons y ys ih =>
    rw [List.pairwise_cons] at h
    unfold insertDesc
    split_ifs with hle
    · rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.mpr h⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hzy
      · exact hle
      · exact le_trans (h.1 z hzy) hle
    · rw [List.pairwise_cons]
      refine ⟨?_, ih h.2⟩
      intro z hz
      have hmem := (insertDesc_perm x ys).mem_iff.mp hz
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hzy
      · omega
      · exact h.1 z hzy

lemma sortDesc_pairwise {V O : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (xs : List (PItem V O)) :
    (sortDesc xs).Pairwise (fun a b => b.deg ≤ a.deg) := by
  induction xs with
  | nil => simp [sortDesc]
  | cons x xs ih => exact insertDesc_pairwise x (sortDesc xs) ih

lemma itemWeight_perm {V O : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {xs ys : List (PItem V O)} (hp : xs.Perm ys) : itemWeight xs = itemWeight ys :=
  (hp.map _).sum_eq

lemma itemWeight_append {V O : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (xs ys : List (PItem V O)) : itemWeight (xs ++ ys) = itemWeight xs + itemWeight ys := by
  simp [itemWeight]

lemma itemWeight_pos_of_ne_nil {V O : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {xs : List (PItem V O)} (hne : xs ≠ []) : 0 < itemWeight xs := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x xs =>
    simp only [itemWeight, List.map_cons, List.sum_cons]
    have h1 : 0 < 2 ^ x.deg := Nat.pos_of_ne_zero (by positivity)
    omega

lemma split_sorted_pow2 {V O : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (B : ℕ) (ys : List (PItem V O)) :
    ys.Pairwise (fun a b => b.deg ≤ a.deg) →
    (∀ y ∈ ys, y.deg ≤ B) →
    ys ≠ [] →
    itemWeight ys ≤ 2 ^ B + 2 ^ B →
    2 ≤ ys.length →
    ∃ L₁ L₂ : List (PItem V O),
      L₁ ++ L₂ = ys ∧ L₁ ≠ [] ∧ L₂ ≠ [] ∧ itemWeight L₁ ≤ 2 ^ B ∧ itemWeight L₂ ≤ 2 ^ B := by
  have haux : ∀ (acc : List (PItem V O)) (rest : List (PItem V O)),
      (acc ++ rest).Pairwise (fun a b => b.deg ≤ a.deg) →
      (∀ y ∈ acc ++ rest, y.deg ≤ B) →
      acc ≠ [] →
      rest ≠ [] →
      itemWeight acc ≤ 2 ^ B →
      itemWeight acc + itemWeight rest ≤ 2 ^ B + 2 ^ B →
      ∃ L₁ L₂ : List (PItem V O),
        L₁ ++ L₂ = acc ++ rest ∧ L₁ ≠ [] ∧ L₂ ≠ [] ∧ itemWeight L₁ ≤ 2 ^ B ∧ itemWeight L₂ ≤ 2 ^ B := by
    intro acc rest
    induction rest generalizing acc with
    | nil =>
      intro _ _ _ hne _ _
      exact absurd rfl hne
    | cons y rest' ih =>
      intro hpw hdeg hacc_ne _ hacc_le htot
      by_cases hfit : itemWeight acc + 2 ^ y.deg ≤ 2 ^ B
      · cases rest' with
        | nil =>
          refine ⟨acc, [y], rfl, hacc_ne, List.cons_ne_nil _ _, hacc_le, ?_⟩
          have hyB : y.deg ≤ B := hdeg y (by simp)
          simp only [itemWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          exact Nat.pow_le_pow_right (by omega) hyB
        | cons z zs =>
          have hacc' : itemWeight (acc ++ [y]) ≤ 2 ^ B := by
            rw [itemWeight_append]
            simpa [itemWeight] using hfit
          have htot' : itemWeight (acc ++ [y]) + itemWeight (z :: zs) ≤ 2 ^ B + 2 ^ B := by
            rw [itemWeight_append]
            simp only [itemWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at htot ⊢
            omega
          have hpw' : ((acc ++ [y]) ++ (z :: zs)).Pairwise (fun a b => b.deg ≤ a.deg) := by
            simpa [List.append_assoc] using hpw
          have hdeg' : ∀ w ∈ (acc ++ [y]) ++ (z :: zs), w.deg ≤ B := by
            intro w hw
            exact hdeg w (by simpa [List.append_assoc] using hw)
          obtain ⟨L₁, L₂, hcat, h1, h2, hw1, hw2⟩ :=
            ih (acc ++ [y]) hpw' hdeg' (by simp) (List.cons_ne_nil _ _) hacc' htot'
          exact ⟨L₁, L₂, by simpa [List.append_assoc] using hcat, h1, h2, hw1, hw2⟩
      · have hdvd_acc : 2 ^ y.deg ∣ itemWeight acc := by
          have hall : ∀ x ∈ acc, 2 ^ y.deg ∣ 2 ^ x.deg := by
            intro x hx
            have hle : y.deg ≤ x.deg := by
              have hpw_app := List.pairwise_append.mp hpw
              exact hpw_app.2.2 x hx y (by simp)
            exact Nat.pow_dvd_pow 2 hle
          clear hpw hdeg hacc_ne hacc_le htot hfit ih
          induction acc with
          | nil => simp [itemWeight]
          | cons a as iha =>
            simp only [itemWeight, List.map_cons, List.sum_cons]
            exact Nat.dvd_add (hall a (by simp)) (iha (fun x hx => hall x (by simp [hx])))
        have hyB : y.deg ≤ B := hdeg y (by simp)
        have hdvd_B : 2 ^ y.deg ∣ 2 ^ B := Nat.pow_dvd_pow 2 hyB
        rcases hdvd_acc with ⟨q₁, hq₁⟩
        rcases hdvd_B with ⟨q₂, hq₂⟩
        have hpos : 0 < 2 ^ y.deg := Nat.pos_of_ne_zero (by positivity)
        have hq_eq : q₁ = q₂ := by
          have h1 : q₁ ≤ q₂ := by
            have : 2 ^ y.deg * q₁ ≤ 2 ^ y.deg * q₂ := by omega
            exact Nat.le_of_mul_le_mul_left this hpos
          have h2 : q₂ < q₁ + 1 := by
            have : 2 ^ y.deg * q₂ < 2 ^ y.deg * (q₁ + 1) := by
              rw [mul_add, mul_one]
              omega
            exact Nat.lt_of_mul_lt_mul_left this
          omega
        have hacc_eq : itemWeight acc = 2 ^ B := by rw [hq₁, hq₂, hq_eq]
        refine ⟨acc, y :: rest', rfl, hacc_ne, List.cons_ne_nil _ _, hacc_le, by omega⟩
  intro hpw hdeg hne htot hlen
  cases ys with
  | nil => exact absurd rfl hne
  | cons y rest =>
    cases rest with
    | nil => simp at hlen
    | cons z zs =>
      have hyB : y.deg ≤ B := hdeg y (by simp)
      have hy_le : itemWeight [y] ≤ 2 ^ B := by
        simp only [itemWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        exact Nat.pow_le_pow_right (by omega) hyB
      have htot' : itemWeight [y] + itemWeight (z :: zs) ≤ 2 ^ B + 2 ^ B := by
        simpa [itemWeight] using htot
      exact haux [y] (z :: zs) hpw hdeg (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) hy_le htot'

lemma exists_power2_split {V O : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (B : ℕ) (xs : List (PItem V O))
    (hlen : 2 ≤ xs.length) (hwt : itemWeight xs ≤ 2 ^ (B + 1)) :
    ∃ L₁ L₂ : List (PItem V O),
      (L₁ ++ L₂).Perm xs ∧ L₁ ≠ [] ∧ L₂ ≠ [] ∧ itemWeight L₁ ≤ 2 ^ B ∧ itemWeight L₂ ≤ 2 ^ B := by
  let ys := sortDesc xs
  have hperm : ys.Perm xs := sortDesc_perm xs
  have hlen_y : 2 ≤ ys.length := by rw [hperm.length_eq]; exact hlen
  have hwt_y : itemWeight ys ≤ 2 ^ B + 2 ^ B := by
    rw [itemWeight_perm hperm]
    simpa [pow_succ, mul_two] using hwt
  have hdeg : ∀ y ∈ ys, y.deg ≤ B := by
    intro y hy
    by_contra hgt
    have hge : B + 1 ≤ y.deg := by omega
    have hpow : 2 ^ (B + 1) ≤ 2 ^ y.deg := Nat.pow_le_pow_right (by omega) hge
    rcases List.append_of_mem hy with ⟨s, t, hys_eq⟩
    have hlen_st : 2 ≤ s.length + 1 + t.length := by
      have := hlen_y
      rw [hys_eq] at this
      simp at this
      omega
    have hwt_eq : itemWeight ys = itemWeight s + 2 ^ y.deg + itemWeight t := by
      rw [hys_eq, itemWeight_append]
      simp [itemWeight]
      omega
    have hpos_st : 0 < itemWeight s + itemWeight t := by
      by_cases hs : s = []
      · subst hs
        have ht : t ≠ [] := by intro h; subst h; simp at hlen_st
        have := itemWeight_pos_of_ne_nil ht
        omega
      · have := itemWeight_pos_of_ne_nil hs
        omega
    have htot_y : itemWeight ys ≤ 2 ^ (B + 1) := by
      rw [itemWeight_perm hperm]
      exact hwt
    omega
  have hne_y : ys ≠ [] := by intro h; simp [h] at hlen_y
  obtain ⟨L₁, L₂, hcat, h1, h2, hw1, hw2⟩ :=
    split_sorted_pow2 B ys (sortDesc_pairwise xs) hdeg hne_y hwt_y hlen_y
  exact ⟨L₁, L₂, hcat ▸ hperm, h1, h2, hw1, hw2⟩

def listLinSum {V O : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (xs : List (PItem V O)) : V →ₗ[ZMod 2] ZMod 2 :=
  (xs.map (fun it => it.lin)).sum

lemma listLinSum_apply {V O : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (xs : List (PItem V O)) (z : V) :
    listLinSum xs z = (xs.map (fun it => it.lin z)).sum := by
  induction xs with
  | nil => simp [listLinSum]
  | cons x xs ih =>
    simp only [listLinSum, List.map_cons, List.sum_cons, LinearMap.add_apply] at ih ⊢
    rw [ih]

lemma listLinSum_perm {V O : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {xs ys : List (PItem V O)} (hp : xs.Perm ys) (z : V) :
    listLinSum xs z = listLinSum ys z := by
  rw [listLinSum_apply, listLinSum_apply]
  exact (hp.map _).sum_eq

lemma listLinSum_append {V O : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (xs ys : List (PItem V O)) (z : V) :
    listLinSum (xs ++ ys) z = listLinSum xs z + listLinSum ys z := by
  simp [listLinSum_apply]

def listLeafCount {V O : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (xs : List (PItem V O)) : ℕ :=
  (xs.map (fun it => it.tree.leafCount)).sum

def listLeafImage {V O : Type} [AddCommGroup V] [Module (ZMod 2) V] [DecidableEq O]
    (xs : List (PItem V O)) : Finset O :=
  xs.foldr (fun it acc => it.tree.leafImage ∪ acc) ∅

lemma listLeafImage_mem {V O : Type} [AddCommGroup V] [Module (ZMod 2) V] [DecidableEq O]
    (xs : List (PItem V O)) (o : O) :
    o ∈ listLeafImage xs ↔ ∃ it ∈ xs, o ∈ it.tree.leafImage := by
  induction xs with
  | nil => simp [listLeafImage]
  | cons x xs ih =>
    change o ∈ x.tree.leafImage ∪ listLeafImage xs ↔ _
    rw [Finset.mem_union, ih]
    simp only [List.mem_cons]
    constructor
    · rintro (h | ⟨it, hit, ho⟩)
      · exact ⟨x, Or.inl rfl, h⟩
      · exact ⟨it, Or.inr hit, ho⟩
    · rintro ⟨it, rfl | hit, ho⟩
      · exact Or.inl ho
      · exact Or.inr ⟨it, hit, ho⟩

lemma listLeafImage_perm {V O : Type} [AddCommGroup V] [Module (ZMod 2) V] [DecidableEq O]
    {xs ys : List (PItem V O)} (hp : xs.Perm ys) : listLeafImage xs = listLeafImage ys := by
  ext o
  rw [listLeafImage_mem, listLeafImage_mem]
  constructor
  · rintro ⟨it, hit, ho⟩; exact ⟨it, hp.subset hit, ho⟩
  · rintro ⟨it, hit, ho⟩; exact ⟨it, hp.symm.subset hit, ho⟩

lemma listLeafImage_append {V O : Type} [AddCommGroup V] [Module (ZMod 2) V] [DecidableEq O]
    (xs ys : List (PItem V O)) : listLeafImage (xs ++ ys) = listLeafImage xs ∪ listLeafImage ys := by
  ext o
  simp only [listLeafImage_mem, Finset.mem_union, List.mem_append]
  constructor
  · rintro ⟨it, h1 | h2, ho⟩
    · exact Or.inl ⟨it, h1, ho⟩
    · exact Or.inr ⟨it, h2, ho⟩
  · rintro (⟨it, h1, ho⟩ | ⟨it, h2, ho⟩)
    · exact ⟨it, Or.inl h1, ho⟩
    · exact ⟨it, Or.inr h2, ho⟩

lemma weighted_parity_tree_exists {V O : Type} [AddCommGroup V] [Module (ZMod 2) V] [DecidableEq O]
    (ok : V → O → Prop) (base : V → Prop) :
    ∀ (H : ℕ) (xs : List (PItem V O)),
      xs ≠ [] →
      itemWeight xs ≤ 2 ^ H →
      (∀ it ∈ xs, it.tree.height ≤ it.deg) →
      (∀ it ∈ xs, it.tree.AllQueries (fun f => ∃ (L : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun z => decide (L z = b))) →
      (∀ it ∈ xs, it.tree.Valid ok (fun z => base z ∧ it.lin z = 1)) →
      ∃ T : PTree V O,
        T.leafCount = listLeafCount xs ∧
        T.leafImage = listLeafImage xs ∧
        T.height ≤ H ∧
        T.AllQueries (fun f => ∃ (L : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun z => decide (L z = b)) ∧
        T.Valid ok (fun z => base z ∧ listLinSum xs z = 1) := by
  intro H
  induction H with
  | zero =>
    intro xs hne hwt hht hq hv
    cases xs with
    | nil => exact absurd rfl hne
    | cons x rest =>
      cases rest with
      | nil =>
        have hxdeg : x.deg = 0 := by
          simp only [itemWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, pow_zero] at hwt
          have : 2 ^ x.deg ≤ 1 := hwt
          by_contra hpos
          have hge : 2 ^ 1 ≤ 2 ^ x.deg := Nat.pow_le_pow_right (by omega) (Nat.pos_of_ne_zero hpos)
          omega
        refine ⟨x.tree, ?_, ?_, ?_, hq x (by simp), ?_⟩
        · simp [listLeafCount]
        · simp [listLeafImage]
        · have := hht x (by simp)
          omega
        · refine x.tree.valid_mono ?_ (hv x (by simp))
          intro z ⟨hb, hsum⟩
          refine ⟨hb, ?_⟩
          simpa [listLinSum_apply] using hsum
      | cons y ys =>
        simp only [itemWeight, List.map_cons, List.sum_cons, pow_zero] at hwt
        have h1 : 1 ≤ 2 ^ x.deg := Nat.one_le_pow _ _ (by omega)
        have h2 : 1 ≤ 2 ^ y.deg := Nat.one_le_pow _ _ (by omega)
        omega
  | succ H' ih =>
    intro xs hne hwt hht hq hv
    by_cases hlen : xs.length = 1
    · cases xs with
      | nil => simp at hlen
      | cons x rest =>
        cases rest with
        | nil =>
          have hxdeg : x.deg ≤ H' + 1 := by
            simp only [itemWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hwt
            exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hwt
          refine ⟨x.tree, ?_, ?_, ?_, hq x (by simp), ?_⟩
          · simp [listLeafCount]
          · simp [listLeafImage]
          · exact le_trans (hht x (by simp)) hxdeg
          · refine x.tree.valid_mono ?_ (hv x (by simp))
            intro z ⟨hb, hsum⟩
            refine ⟨hb, ?_⟩
            simpa [listLinSum_apply] using hsum
        | cons _ _ => simp at hlen
    · have hlen2 : 2 ≤ xs.length := by
        cases xs with
        | nil => exact absurd rfl hne
        | cons _ rest =>
          cases rest with
          | nil => simp at hlen
          | cons _ _ => simp
      obtain ⟨L₁, L₂, hperm, hne1, hne2, hwt1, hwt2⟩ := exists_power2_split H' xs hlen2 hwt
      have hsub1 : ∀ it ∈ L₁, it ∈ xs := fun it hit => hperm.subset (List.mem_append_left L₂ hit)
      have hsub2 : ∀ it ∈ L₂, it ∈ xs := fun it hit => hperm.subset (List.mem_append_right L₁ hit)
      obtain ⟨T₁, hc1, hi1, hh1, hq1, hv1⟩ :=
        ih L₁ hne1 hwt1 (fun it hit => hht it (hsub1 it hit)) (fun it hit => hq it (hsub1 it hit))
          (fun it hit => hv it (hsub1 it hit))
      obtain ⟨T₂, hc2, hi2, hh2, hq2, hv2⟩ :=
        ih L₂ hne2 hwt2 (fun it hit => hht it (hsub2 it hit)) (fun it hit => hq it (hsub2 it hit))
          (fun it hit => hv it (hsub2 it hit))
      refine ⟨PTree.node (fun z => decide (listLinSum L₁ z = 0)) T₁ T₂, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [PTree.leafCount, hc1, hc2]
        have hlc_perm : listLeafCount (L₁ ++ L₂) = listLeafCount xs := (hperm.map _).sum_eq
        rw [← hlc_perm]
        simp [listLeafCount]
      · simp only [PTree.leafImage, hi1, hi2]
        rw [← listLeafImage_append, listLeafImage_perm hperm]
      · simp only [PTree.height]
        omega
      · exact ⟨⟨listLinSum L₁, 0, rfl⟩, hq1, hq2⟩
      · constructor
        · refine T₁.valid_mono ?_ hv1
          intro z ⟨⟨hb, _⟩, hdec⟩
          exact ⟨hb, zmod2_decide_eq_zero_false hdec⟩
        · refine T₂.valid_mono ?_ hv2
          intro z ⟨⟨hb, hsum⟩, hdec⟩
          refine ⟨hb, ?_⟩
          have h1 : listLinSum L₁ z = 0 := zmod2_decide_eq_zero_true hdec
          have htot : listLinSum L₁ z + listLinSum L₂ z = 1 := by
            rw [← listLinSum_append, listLinSum_perm hperm z]
            exact hsum
          rw [h1, zero_add] at htot
          exact htot

def projU {m l r d : ℕ} (idx : Fin d) : VType m l r d →ₗ[ZMod 2] ZMod 2 where
  toFun z := z.2.2 idx
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def projX {m l r d : ℕ} (i : Fin m) : VType m l r d →ₗ[ZMod 2] ZMod 2 where
  toFun z := z.1 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def projY {m l r d : ℕ} (a : Fin r) (j : Fin l) : VType m l r d →ₗ[ZMod 2] ZMod 2 where
  toFun z := z.2.1 a j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def sumY {m l r d : ℕ} (a : Fin r) : VType m l r d →ₗ[ZMod 2] ZMod 2 where
  toFun z := ∑ j : Fin l, z.2.1 a j
  map_add' z₁ z₂ := by simp [Finset.sum_add_distrib]
  map_smul' c z := by simp [Finset.mul_sum]

def readUTree {m l r d : ℕ} {O : Type}
    (cont : UType d → PTree (VType m l r d) O) :
    (k : ℕ) → k ≤ d → UType d → PTree (VType m l r d) O
  | 0, _, u0 => cont u0
  | k + 1, hk, u0 =>
    let idx : Fin d := ⟨k, hk⟩
    PTree.node (fun z => decide (z.2.2 idx = 1))
      (readUTree cont k (Nat.le_of_lt hk) (Function.update u0 idx 0))
      (readUTree cont k (Nat.le_of_lt hk) (Function.update u0 idx 1))

lemma readUTree_leafCount {m l r d : ℕ} {O : Type}
    (cont : UType d → PTree (VType m l r d) O) (c : ℕ)
    (hc : ∀ u, (cont u).leafCount = c) :
    ∀ (k : ℕ) (hk : k ≤ d) (u0 : UType d),
      (readUTree cont k hk u0).leafCount = 2 ^ k * c := by
  intro k
  induction k with
  | zero =>
    intro hk u0
    simp [readUTree, hc]
  | succ k ih =>
    intro hk u0
    simp only [readUTree, PTree.leafCount, ih]
    ring

lemma readUTree_height {m l r d : ℕ} {O : Type}
    (cont : UType d → PTree (VType m l r d) O) (h : ℕ)
    (hh : ∀ u, (cont u).height ≤ h) :
    ∀ (k : ℕ) (hk : k ≤ d) (u0 : UType d),
      (readUTree cont k hk u0).height ≤ k + h := by
  intro k
  induction k with
  | zero =>
    intro hk u0
    simpa [readUTree] using hh u0
  | succ k ih =>
    intro hk u0
    simp only [readUTree, PTree.height]
    have h1 := ih (Nat.le_of_lt hk) (Function.update u0 ⟨k, hk⟩ 0)
    have h2 := ih (Nat.le_of_lt hk) (Function.update u0 ⟨k, hk⟩ 1)
    omega

lemma readUTree_allQueries {m l r d : ℕ} {O : Type}
    (cont : UType d → PTree (VType m l r d) O)
    (hq : ∀ u, (cont u).AllQueries (fun f => ∃ (L : VType m l r d →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun z => decide (L z = b))) :
    ∀ (k : ℕ) (hk : k ≤ d) (u0 : UType d),
      (readUTree cont k hk u0).AllQueries (fun f => ∃ (L : VType m l r d →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun z => decide (L z = b)) := by
  intro k
  induction k with
  | zero =>
    intro hk u0
    exact hq u0
  | succ k ih =>
    intro hk u0
    exact ⟨⟨projU ⟨k, hk⟩, 1, rfl⟩, ih _ _, ih _ _⟩

lemma readUTree_leafImage {m l r d : ℕ} {O : Type} [DecidableEq O]
    (cont : UType d → PTree (VType m l r d) O) :
    ∀ (k : ℕ) (hk : k ≤ d) (u0 : UType d),
      (readUTree cont k hk u0).leafImage =
        (Finset.univ.filter (fun u : UType d => ∀ t : Fin d, k ≤ t.val → u t = u0 t)).biUnion
          (fun u => (cont u).leafImage) := by
  intro k
  induction k with
  | zero =>
    intro hk u0
    have hfilt : Finset.univ.filter (fun u : UType d => ∀ t : Fin d, 0 ≤ t.val → u t = u0 t) = {u0} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Nat.zero_le,
        forall_true_left]
      exact funext_iff.symm
    rw [hfilt, Finset.singleton_biUnion]
    rfl
  | succ k ih =>
    intro hk u0
    simp only [readUTree, PTree.leafImage, ih]
    rw [← Finset.union_biUnion]
    congr 1
    ext u
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h) t ht
      · have := h t (by omega)
        have hne : t ≠ ⟨k, hk⟩ := fun heq => by subst heq; dsimp at ht; omega
        simpa [Function.update_of_ne hne] using this
      · have := h t (by omega)
        have hne : t ≠ ⟨k, hk⟩ := fun heq => by subst heq; dsimp at ht; omega
        simpa [Function.update_of_ne hne] using this
    · intro h
      have h01 : u ⟨k, hk⟩ = 0 ∨ u ⟨k, hk⟩ = 1 :=
        (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (u ⟨k, hk⟩)
      rcases h01 with hu0 | hu1
      · left
        intro t ht
        by_cases htk : t = ⟨k, hk⟩
        · subst htk; simpa using hu0
        · have hgt : k + 1 ≤ t.val := by
            have : t.val ≠ k := fun heq => htk (Fin.ext heq)
            omega
          simpa [Function.update_of_ne htk] using h t hgt
      · right
        intro t ht
        by_cases htk : t = ⟨k, hk⟩
        · subst htk; simpa using hu1
        · have hgt : k + 1 ≤ t.val := by
            have : t.val ≠ k := fun heq => htk (Fin.ext heq)
            omega
          simpa [Function.update_of_ne htk] using h t hgt

lemma readUTree_valid {m l r d : ℕ} {O : Type}
    (ok : VType m l r d → O → Prop) (base : VType m l r d → Prop)
    (cont : UType d → PTree (VType m l r d) O)
    (hv : ∀ u : UType d, (cont u).Valid ok (fun z => base z ∧ z.2.2 = u)) :
    ∀ (k : ℕ) (hk : k ≤ d) (u0 : UType d),
      (readUTree cont k hk u0).Valid ok (fun z => base z ∧ ∀ t : Fin d, k ≤ t.val → z.2.2 t = u0 t) := by
  intro k
  induction k with
  | zero =>
    intro hk u0
    refine (cont u0).valid_mono ?_ (hv u0)
    intro z ⟨hb, hall⟩
    exact ⟨hb, funext fun t => hall t (Nat.zero_le _)⟩
  | succ k ih =>
    intro hk u0
    constructor
    · refine (readUTree cont k (Nat.le_of_lt hk) (Function.update u0 ⟨k, hk⟩ 0)).valid_mono ?_
        (ih (Nat.le_of_lt hk) (Function.update u0 ⟨k, hk⟩ 0))
      intro z ⟨⟨hb, hall⟩, hdec⟩
      refine ⟨hb, fun t ht => ?_⟩
      by_cases htk : t = ⟨k, hk⟩
      · subst htk
        simpa using zmod2_decide_eq_one_false hdec
      · have hgt : k + 1 ≤ t.val := by
          have : t.val ≠ k := fun heq => htk (Fin.ext heq)
          omega
        simpa [Function.update_of_ne htk] using hall t hgt
    · refine (readUTree cont k (Nat.le_of_lt hk) (Function.update u0 ⟨k, hk⟩ 1)).valid_mono ?_
        (ih (Nat.le_of_lt hk) (Function.update u0 ⟨k, hk⟩ 1))
      intro z ⟨⟨hb, hall⟩, hdec⟩
      refine ⟨hb, fun t ht => ?_⟩
      by_cases htk : t = ⟨k, hk⟩
      · subst htk
        simpa using zmod2_decide_eq_one_true hdec
      · have hgt : k + 1 ≤ t.val := by
          have : t.val ≠ k := fun heq => htk (Fin.ext heq)
          omega
        simpa [Function.update_of_ne htk] using hall t hgt

lemma list_sum_finRange_zmod {n : ℕ} (g : Fin n → ZMod 2) :
    ((List.finRange n).map g).sum = ∑ i : Fin n, g i := by
  have hnodup : (List.finRange n).Nodup := List.nodup_finRange n
  have htoFinset : (List.finRange n).toFinset = Finset.univ := by
    ext i; simp
  rw [← htoFinset, List.sum_toFinset _ hnodup]

lemma backward_dir (m l r d : ℕ) (hl : 0 < l) (hr : 0 < r) (f : UType d → Fin r) (H : ℕ)
    (hW : m + 2 ^ d * l ≤ 2 ^ H)
    (hcase : (∃ a : Fin r, ∀ u, f u = a) ∨ ∃ e : ℕ, 2 ^ d * l ≤ 2 ^ e ∧ m + 2 ^ e ≤ 2 ^ H) :
    ∃ (N J : Finset (List Bool))
      (q : List Bool → VType m l r d → Bool)
      (out : List Bool → OType m l r d),
      TreeShape N J ∧
      (∀ p ∈ J, ∃ (L : VType m l r d →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), q p = fun z => decide (L z = b)) ∧
      (∀ p ∈ N \ J, ∀ z : VType m l r d, Follows q p z → OkProp z (out p)) ∧
      (N \ J).card = m + 2 ^ d * l ∧
      (N \ J).image out = alphabetFinset (m := m) (l := l) f ∧
      ∀ p ∈ N \ J, p.length ≤ H := by
  rcases hcase with ⟨a₀, ha₀⟩ | ⟨e, hPe, hmeH⟩
  · let commItems : List (PItem (VType m l r d) (OType m l r d)) :=
      (List.finRange m).map (fun i => ⟨projX i, 0, PTree.leaf (Sum.inl i)⟩)
    let privItems : List (PItem (VType m l r d) (OType m l r d)) :=
      (List.finRange l).map (fun j =>
        ⟨projY a₀ j, d, readUTree (fun u => PTree.leaf (Sum.inr (a₀, j, u))) d (le_refl d) 0⟩)
    let items := commItems ++ privItems
    have hne : items ≠ [] := by
      intro hnil
      have hlen := congrArg List.length hnil
      simp [items, commItems, privItems] at hlen
      omega
    have hwt : itemWeight items ≤ 2 ^ H := by
      rw [itemWeight_append]
      have hw1 : itemWeight commItems = m := by
        simp [itemWeight, commItems, List.map_map, Function.comp_def]
      have hw2 : itemWeight privItems = 2 ^ d * l := by
        simp [itemWeight, privItems, List.map_map, Function.comp_def, mul_comm]
      rw [hw1, hw2]
      exact hW
    have hht : ∀ it ∈ items, it.tree.height ≤ it.deg := by
      intro it hit
      simp only [items, List.mem_append, commItems, privItems, List.mem_map, List.mem_finRange,
        true_and] at hit
      rcases hit with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · simp [PTree.height]
      · simpa using readUTree_height (fun u => PTree.leaf (Sum.inr (a₀, j, u))) 0
          (fun _ => le_refl 0) d (le_refl d) 0
    have hq : ∀ it ∈ items, it.tree.AllQueries
        (fun fn => ∃ (L : VType m l r d →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), fn = fun z => decide (L z = b)) := by
      intro it hit
      simp only [items, List.mem_append, commItems, privItems, List.mem_map, List.mem_finRange,
        true_and] at hit
      rcases hit with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · trivial
      · exact readUTree_allQueries (fun u => PTree.leaf (Sum.inr (a₀, j, u))) (fun _ => trivial) d (le_refl d) 0
    have hv : ∀ it ∈ items, it.tree.Valid OkProp (fun z => Promised z ∧ it.lin z = 1) := by
      intro it hit
      simp only [items, List.mem_append, commItems, privItems, List.mem_map, List.mem_finRange,
        true_and] at hit
      rcases hit with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · intro z ⟨_, hxi⟩ _
        exact hxi
      · have hval := readUTree_valid (m := m) (l := l) (r := r) (d := d)
          OkProp (fun z : VType m l r d => Promised z ∧ projY a₀ j z = 1)
          (fun u => PTree.leaf (Sum.inr (a₀, j, u)))
          (fun u z h _ => ⟨h.1.2, h.2.symm⟩) d (le_refl d) 0
        exact (readUTree (fun u => PTree.leaf (Sum.inr (a₀, j, u))) d (le_refl d) 0).valid_mono
          (fun z hz => ⟨hz, fun t ht => by omega⟩) hval
    obtain ⟨T, hcardT, himgT, hhtT, hqT, hvT⟩ :=
      weighted_parity_tree_exists OkProp Promised H items hne hwt hht hq hv
    refine ⟨T.nodes, T.internal, T.queryAt, T.outAt, T.shape, T.allQueries_spec hqT, ?_, ?_, ?_, ?_⟩
    · intro p hp z hf
      rw [PTree.sdiff_eq_leaves] at hp
      intro hprom
      have hsum1 : listLinSum items z = 1 := by
        rw [listLinSum_append, listLinSum_apply, listLinSum_apply]
        have h1 : (commItems.map (fun it => it.lin z)).sum = ∑ i : Fin m, z.1 i := by
          simp only [commItems, List.map_map, Function.comp_def]
          exact list_sum_finRange_zmod (fun i => z.1 i)
        have h2 : (privItems.map (fun it => it.lin z)).sum = ∑ j : Fin l, z.2.1 a₀ j := by
          simp only [privItems, List.map_map, Function.comp_def]
          exact list_sum_finRange_zmod (fun j => z.2.1 a₀ j)
        rw [h1, h2]
        exact hprom a₀
      exact T.valid_spec _ hvT p hp z ⟨hprom, hsum1⟩ hf hprom
    · rw [PTree.sdiff_eq_leaves, T.card_leaves, hcardT]
      simp only [listLeafCount, items, List.map_append, List.sum_append]
      have hc1 : (commItems.map (fun it => it.tree.leafCount)).sum = m := by
        simp [commItems, List.map_map, Function.comp_def, PTree.leafCount]
      have hc2 : (privItems.map (fun it => it.tree.leafCount)).sum = 2 ^ d * l := by
        have hpt : ∀ j : Fin l,
            (readUTree (m := m) (l := l) (r := r) (O := OType m l r d)
              (fun u => PTree.leaf (Sum.inr (a₀, j, u))) d (le_refl d) 0).leafCount = 2 ^ d := by
          intro j
          simpa [PTree.leafCount] using readUTree_leafCount (m := m) (l := l) (r := r) (O := OType m l r d)
            (fun u => PTree.leaf (Sum.inr (a₀, j, u))) 1
            (fun _ => rfl) d (le_refl d) 0
        simp only [privItems, List.map_map, Function.comp_def, hpt]
        simp [mul_comm]
      rw [hc1, hc2]
    · rw [PTree.sdiff_eq_leaves, T.image_leaves, himgT]
      ext o
      rw [listLeafImage_mem]
      simp only [items, List.mem_append, commItems, privItems, List.mem_map, List.mem_finRange,
        true_and, alphabetFinset, Finset.mem_filter, Finset.mem_univ]
      constructor
      · rintro ⟨it, ⟨i, rfl⟩ | ⟨j, rfl⟩, ho⟩
        · simp only [PTree.leafImage, Finset.mem_singleton] at ho
          subst ho
          simp
        · rw [readUTree_leafImage] at ho
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
            PTree.leafImage, Finset.mem_singleton] at ho
          rcases ho with ⟨u, _, rfl⟩
          simp [ha₀ u]
      · intro ho
        cases o with
        | inl i =>
          exact ⟨⟨projX i, 0, PTree.leaf (Sum.inl i)⟩, Or.inl ⟨i, rfl⟩, by simp [PTree.leafImage]⟩
        | inr x =>
          rcases x with ⟨a, j, u⟩
          simp only [Sum.elim_inr, decide_eq_true_eq] at ho
          have ha : a = a₀ := ho.trans (ha₀ u)
          rw [ha]
          refine ⟨⟨projY a₀ j, d, readUTree (fun u' => PTree.leaf (Sum.inr (a₀, j, u'))) d (le_refl d) 0⟩,
            Or.inr ⟨j, rfl⟩, ?_⟩
          rw [readUTree_leafImage]
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
            PTree.leafImage, Finset.mem_singleton]
          exact ⟨u, fun t ht => by omega, rfl⟩
    · intro p hp
      rw [PTree.sdiff_eq_leaves] at hp
      exact le_trans (T.length_le_height p hp) hhtT
  · have hd_le_e : d ≤ e := by
      have h1 : 2 ^ d ≤ 2 ^ e := calc
        2 ^ d = 2 ^ d * 1 := (mul_one _).symm
        _ ≤ 2 ^ d * l := Nat.mul_le_mul_left _ hl
        _ ≤ 2 ^ e := hPe
      exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp h1
    have hl_le : l ≤ 2 ^ (e - d) := by
      have hmul : 2 ^ d * l ≤ 2 ^ d * 2 ^ (e - d) := by
        rw [← pow_add, Nat.add_sub_of_le hd_le_e]
        exact hPe
      exact Nat.le_of_mul_le_mul_left hmul (Nat.pos_of_ne_zero (by positivity))
    have hsub_u : ∀ u : UType d,
        ∃ Tu : PTree (VType m l r d) (OType m l r d),
          Tu.leafCount = l ∧
          Tu.leafImage = (Finset.univ : Finset (Fin l)).image (fun j => Sum.inr (f u, j, u)) ∧
          Tu.height ≤ e - d ∧
          Tu.AllQueries (fun fn => ∃ (L : VType m l r d →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), fn = fun z => decide (L z = b)) ∧
          Tu.Valid OkProp (fun z => (Promised z ∧ (∑ j : Fin l, z.2.1 (f u) j) = 1) ∧ z.2.2 = u) := by
      intro u
      let uItems : List (PItem (VType m l r d) (OType m l r d)) :=
        (List.finRange l).map (fun j => ⟨projY (f u) j, 0, PTree.leaf (Sum.inr (f u, j, u))⟩)
      have hne_u : uItems ≠ [] := by
        intro hnil
        have := congrArg List.length hnil
        simp [uItems] at this
        omega
      have hwt_u : itemWeight uItems ≤ 2 ^ (e - d) := by
        have : itemWeight uItems = l := by simp [itemWeight, uItems, List.map_map, Function.comp_def]
        rw [this]
        exact hl_le
      obtain ⟨Tu, hc, hi, hh, hqu, hvu⟩ :=
        weighted_parity_tree_exists OkProp (fun z => Promised z ∧ z.2.2 = u) (e - d) uItems
          hne_u hwt_u
          (fun it hit => by
            simp only [uItems, List.mem_map, List.mem_finRange, true_and] at hit
            rcases hit with ⟨j, rfl⟩; simp [PTree.height])
          (fun it hit => by
            simp only [uItems, List.mem_map, List.mem_finRange, true_and] at hit
            rcases hit with ⟨j, rfl⟩; trivial)
          (fun it hit => by
            simp only [uItems, List.mem_map, List.mem_finRange, true_and] at hit
            rcases hit with ⟨j, rfl⟩
            intro z ⟨⟨_, hu⟩, hy⟩ _
            exact ⟨hy, hu.symm⟩)
      refine ⟨Tu, ?_, ?_, hh, hqu, ?_⟩
      · rw [hc]; simp [listLeafCount, uItems, List.map_map, Function.comp_def, PTree.leafCount]
      · rw [hi]
        ext o
        rw [listLeafImage_mem]
        simp [uItems, PTree.leafImage, eq_comm]
      · refine Tu.valid_mono ?_ hvu
        intro z ⟨⟨hprom, hsum⟩, hu⟩
        refine ⟨⟨hprom, hu⟩, ?_⟩
        rw [listLinSum_apply]
        simp only [uItems, List.map_map, Function.comp_def]
        exact (list_sum_finRange_zmod (fun j => z.2.1 (f u) j)).trans hsum
    choose cont hcont using hsub_u
    let a₀ : Fin r := ⟨0, hr⟩
    let Tpriv : PTree (VType m l r d) (OType m l r d) := readUTree cont d (le_refl d) 0
    have hTpriv_card : Tpriv.leafCount = 2 ^ d * l :=
      readUTree_leafCount cont l (fun u => (hcont u).1) d (le_refl d) 0
    have hTpriv_ht : Tpriv.height ≤ e := by
      have h := readUTree_height cont (e - d) (fun u => (hcont u).2.2.1) d (le_refl d) 0
      dsimp only [Tpriv]
      omega
    have hTpriv_q : Tpriv.AllQueries
        (fun fn => ∃ (L : VType m l r d →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), fn = fun z => decide (L z = b)) :=
      readUTree_allQueries cont (fun u => (hcont u).2.2.2.1) d (le_refl d) 0
    have hTpriv_valid : Tpriv.Valid OkProp (fun z => Promised z ∧ sumY a₀ z = 1) := by
      have hval : Tpriv.Valid OkProp
          (fun z => (Promised z ∧ sumY a₀ z = 1) ∧ ∀ t : Fin d, d ≤ t.val → z.2.2 t = 0) := by
        refine readUTree_valid OkProp (fun z => Promised z ∧ sumY a₀ z = 1) cont ?_ d (le_refl d) 0
        intro u
        refine (cont u).valid_mono ?_ (hcont u).2.2.2.2
        intro z ⟨⟨hprom, hsum_a0⟩, hu⟩
        have hx0 : (∑ i : Fin m, z.1 i) = 0 := by
          have h0 := hprom a₀
          change (∑ j : Fin l, z.2.1 a₀ j) = 1 at hsum_a0
          rw [hsum_a0] at h0
          have : (∑ i : Fin m, z.1 i) + 1 = 0 + 1 := by simpa using h0
          exact add_right_cancel this
        have hsum_fu : (∑ j : Fin l, z.2.1 (f u) j) = 1 := by
          have hfu := hprom (f u)
          rw [hx0, zero_add] at hfu
          exact hfu
        exact ⟨⟨hprom, hsum_fu⟩, hu⟩
      exact Tpriv.valid_mono (fun z hz => ⟨hz, fun t ht => by omega⟩) hval
    let commItems : List (PItem (VType m l r d) (OType m l r d)) :=
      (List.finRange m).map (fun i => ⟨projX i, 0, PTree.leaf (Sum.inl i)⟩)
    let items : List (PItem (VType m l r d) (OType m l r d)) :=
      commItems ++ [⟨sumY a₀, e, Tpriv⟩]
    have hne : items ≠ [] := by simp [items]
    have hwt : itemWeight items ≤ 2 ^ H := by
      rw [itemWeight_append]
      have hw1 : itemWeight commItems = m := by
        simp [itemWeight, commItems, List.map_map, Function.comp_def]
      have hw2 : itemWeight [⟨sumY a₀, e, Tpriv⟩] = 2 ^ e := by simp [itemWeight]
      rw [hw1, hw2]
      exact hmeH
    have hht : ∀ it ∈ items, it.tree.height ≤ it.deg := by
      intro it hit
      simp only [items, List.mem_append, commItems, List.mem_map, List.mem_finRange, true_and,
        List.mem_singleton] at hit
      rcases hit with ⟨i, rfl⟩ | rfl
      · simp [PTree.height]
      · exact hTpriv_ht
    have hq : ∀ it ∈ items, it.tree.AllQueries
        (fun fn => ∃ (L : VType m l r d →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), fn = fun z => decide (L z = b)) := by
      intro it hit
      simp only [items, List.mem_append, commItems, List.mem_map, List.mem_finRange, true_and,
        List.mem_singleton] at hit
      rcases hit with ⟨i, rfl⟩ | rfl
      · trivial
      · exact hTpriv_q
    have hv : ∀ it ∈ items, it.tree.Valid OkProp (fun z => Promised z ∧ it.lin z = 1) := by
      intro it hit
      simp only [items, List.mem_append, commItems, List.mem_map, List.mem_finRange, true_and,
        List.mem_singleton] at hit
      rcases hit with ⟨i, rfl⟩ | rfl
      · intro z ⟨_, hxi⟩ _; exact hxi
      · exact hTpriv_valid
    obtain ⟨T, hcardT, himgT, hhtT, hqT, hvT⟩ :=
      weighted_parity_tree_exists OkProp Promised H items hne hwt hht hq hv
    refine ⟨T.nodes, T.internal, T.queryAt, T.outAt, T.shape, T.allQueries_spec hqT, ?_, ?_, ?_, ?_⟩
    · intro p hp z hf
      rw [PTree.sdiff_eq_leaves] at hp
      intro hprom
      have hsum1 : listLinSum items z = 1 := by
        rw [listLinSum_append, listLinSum_apply, listLinSum_apply]
        have h1 : (commItems.map (fun it => it.lin z)).sum = ∑ i : Fin m, z.1 i := by
          simp only [commItems, List.map_map, Function.comp_def]
          exact list_sum_finRange_zmod (fun i => z.1 i)
        rw [h1]
        simpa [sumY] using hprom a₀
      exact T.valid_spec _ hvT p hp z ⟨hprom, hsum1⟩ hf hprom
    · rw [PTree.sdiff_eq_leaves, T.card_leaves, hcardT]
      simp only [listLeafCount, items, List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have hc1 : (commItems.map (fun it => it.tree.leafCount)).sum = m := by
        simp [commItems, List.map_map, Function.comp_def, PTree.leafCount]
      rw [hc1, hTpriv_card]
    · rw [PTree.sdiff_eq_leaves, T.image_leaves, himgT]
      ext o
      rw [listLeafImage_mem]
      simp only [items, List.mem_append, commItems, List.mem_map, List.mem_finRange, true_and,
        List.mem_singleton, alphabetFinset, Finset.mem_filter, Finset.mem_univ]
      constructor
      · rintro ⟨it, ⟨i, rfl⟩ | rfl, ho⟩
        · simp only [PTree.leafImage, Finset.mem_singleton] at ho
          subst ho
          simp
        · dsimp only [Tpriv] at ho
          rw [readUTree_leafImage] at ho
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at ho
          rcases ho with ⟨u, _, hou⟩
          rw [(hcont u).2.1] at hou
          rcases Finset.mem_image.mp hou with ⟨j, _, rfl⟩
          simp
      · intro ho
        cases o with
        | inl i =>
          exact ⟨⟨projX i, 0, PTree.leaf (Sum.inl i)⟩, Or.inl ⟨i, rfl⟩, by simp [PTree.leafImage]⟩
        | inr x =>
          rcases x with ⟨a, j, u⟩
          simp only [Sum.elim_inr, decide_eq_true_eq] at ho
          subst ho
          refine ⟨⟨sumY a₀, e, Tpriv⟩, Or.inr rfl, ?_⟩
          dsimp only [Tpriv]
          rw [readUTree_leafImage]
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨u, fun t ht => by omega, ?_⟩
          rw [(hcont u).2.1]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
    · intro p hp
      rw [PTree.sdiff_eq_leaves] at hp
      exact le_trans (T.length_le_height p hp) hhtT


def FitsProp (m l r d H : ℕ) (B : Finset (OType m l r d)) : Prop :=
  ∃ (N J : Finset (List Bool)) (q : List Bool → VType m l r d → Bool) (out : List Bool → OType m l r d),
    (TreeShape N J ∧
      (∀ p ∈ J, ∃ (L : VType m l r d →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), q p = fun z => decide (L z = b)) ∧
      ∀ p ∈ N \ J, ∀ z : VType m l r d, Follows q p z → OkProp z (out p)) ∧
    (N \ J).card = m + 2 ^ d * l ∧ (N \ J).image out = B ∧ ∀ p ∈ N \ J, p.length ≤ H

lemma fits_exists_selector {m l r d H : ℕ} {B : Finset (OType m l r d)}
    (hB : FitsProp m l r d H B) :
    ∃ f : UType d → Fin r, B = alphabetFinset (m := m) (l := l) f := by
  rcases hB with ⟨N, J, q, out, ⟨hshape, _, hcert⟩, hcard, himg, _⟩
  have hcomm : ∀ i : Fin m, (Sum.inl i : OType m l r d) ∈ B := by
    intro i
    obtain ⟨p, hp, hfp⟩ := exists_leaf_follows hshape q (Pi.single i (1 : ZMod 2), (0, 0))
    have hok := hcert p hp _ hfp (zCommon_promised i 0)
    have hout : out p = Sum.inl i := by
      cases ho : out p with
      | inl i' =>
        rw [ho] at hok
        simp only [Sum.elim_inl, Pi.single_apply] at hok
        by_cases hii' : i' = i
        · subst hii'; rfl
        · simp [hii'] at hok
      | inr x =>
        rw [ho] at hok
        simp at hok
    rw [← himg, ← hout]
    exact Finset.mem_image_of_mem out hp
  have hpriv : ∀ u : UType d, ∃ a : Fin r, ∀ j : Fin l, (Sum.inr (a, j, u) : OType m l r d) ∈ B := by
    intro u
    by_contra h
    push Not at h
    choose miss hmiss using h
    let g : Fin r → Fin l → ZMod 2 := fun a => Pi.single (miss a) 1
    have hg : ∀ a : Fin r, ∑ j : Fin l, g a j = 1 := fun a => by simp [g]
    obtain ⟨p, hp, hfp⟩ := exists_leaf_follows hshape q (0, (g, u))
    have hok := hcert p hp _ hfp (zPriv_promised g u hg)
    have hmemB : out p ∈ B := by
      rw [← himg]
      exact Finset.mem_image_of_mem out hp
    cases ho : out p with
    | inl i =>
      rw [ho] at hok
      simp at hok
    | inr x =>
      rcases x with ⟨a, j, u'⟩
      rw [ho] at hok hmemB
      simp only [Sum.elim_inr] at hok
      rcases hok with ⟨hgj, hu'⟩
      subst hu'
      simp only [g, Pi.single_apply] at hgj
      by_cases hjm : j = miss a
      · subst hjm
        exact hmiss a hmemB
      · simp [hjm] at hgj
  choose f hf using hpriv
  refine ⟨f, ?_⟩
  have hsub : alphabetFinset (m := m) (l := l) f ⊆ B := by
    intro o ho
    simp only [alphabetFinset, Finset.mem_filter, Finset.mem_univ, true_and] at ho
    cases o with
    | inl i => exact hcomm i
    | inr x =>
      rcases x with ⟨a, j, u⟩
      simp only [Sum.elim_inr, decide_eq_true_eq] at ho
      subst ho
      exact hf u j
  have hcard_le : B.card ≤ (alphabetFinset (m := m) (l := l) f).card := by
    rw [card_alphabetFinset, ← himg, ← hcard]
    exact Finset.card_image_le
  exact (Finset.eq_of_subset_of_card_le hsub hcard_le).symm

lemma alphabetFinset_injective {m l r d : ℕ} (hl : 0 < l) :
    Function.Injective (alphabetFinset (m := m) (l := l) (r := r) (d := d)) := by
  intro f₁ f₂ heq
  ext u
  have hmem : (Sum.inr (f₁ u, ⟨0, hl⟩, u) : OType m l r d) ∈ alphabetFinset (m := m) (l := l) f₁ := by
    simp [alphabetFinset]
  rw [heq] at hmem
  simp only [alphabetFinset, Finset.mem_filter, Finset.mem_univ, true_and, Sum.elim_inr,
    decide_eq_true_eq] at hmem
  exact congrArg Fin.val hmem

lemma canPack_iff (m l d H : ℕ) :
    ((Finset.range (H + 1)).filter (fun e => 2 ^ d * l ≤ 2 ^ e ∧ m + 2 ^ e ≤ 2 ^ H)).Nonempty ↔
      ∃ e : ℕ, 2 ^ d * l ≤ 2 ^ e ∧ m + 2 ^ e ≤ 2 ^ H := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, (Finset.mem_filter.mp he).2⟩
  · rintro ⟨e, h1, h2⟩
    have hpow : 2 ^ e ≤ 2 ^ H := by omega
    have heH : e ≤ H := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h1, h2⟩⟩

lemma count_fits (m l r d H : ℕ) (hl : 0 < l) (hr : 0 < r) :
    let canPack := ((Finset.range (H + 1)).filter
      (fun e => 2 ^ d * l ≤ 2 ^ e ∧ m + 2 ^ e ≤ 2 ^ H)).Nonempty
    Nat.card {B : Finset (OType m l r d) // FitsProp m l r d H B} =
      if 2 ^ H < m + 2 ^ d * l then 0 else if canPack then r ^ (2 ^ d) else r := by
  classical
  intro canPack
  by_cases hlt : 2 ^ H < m + 2 ^ d * l
  · simp only [hlt, ↓reduceIte]
    have hempty : IsEmpty {B : Finset (OType m l r d) // FitsProp m l r d H B} := by
      refine ⟨fun ⟨B, hB⟩ => ?_⟩
      obtain ⟨f, rfl⟩ := fits_exists_selector hB
      rcases hB with ⟨N, J, q, out, ⟨hshape, hq, hcert⟩, hcard, himg, hH⟩
      have hfwd := forward_dir m l r d hl hr f H N J q out hshape hq hcert hcard himg hH
      omega
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero]
  · simp only [hlt, ↓reduceIte]
    have hW : m + 2 ^ d * l ≤ 2 ^ H := by omega
    by_cases hpack : canPack
    · simp only [hpack, ↓reduceIte]
      have hex_e : ∃ e : ℕ, 2 ^ d * l ≤ 2 ^ e ∧ m + 2 ^ e ≤ 2 ^ H :=
        (canPack_iff m l d H).mp hpack
      let toSub : (UType d → Fin r) → {B : Finset (OType m l r d) // FitsProp m l r d H B} :=
        fun f => ⟨alphabetFinset (m := m) (l := l) f, by
          obtain ⟨N, J, q, out, hshape, hq, hcert, hcard, himg, hH⟩ :=
            backward_dir m l r d hl hr f H hW (Or.inr hex_e)
          exact ⟨N, J, q, out, ⟨hshape, hq, hcert⟩, hcard, himg, hH⟩⟩
      have hbij : Function.Bijective toSub := by
        constructor
        · intro f₁ f₂ h
          exact alphabetFinset_injective hl (congrArg Subtype.val h)
        · rintro ⟨B, hB⟩
          obtain ⟨f, hf⟩ := fits_exists_selector hB
          exact ⟨f, Subtype.ext hf.symm⟩
      let e := Equiv.ofBijective toSub hbij
      rw [Nat.card_congr e.symm, Nat.card_eq_fintype_card, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    · simp only [hpack, ↓reduceIte]
      have hno_e : ¬ ∃ e : ℕ, 2 ^ d * l ≤ 2 ^ e ∧ m + 2 ^ e ≤ 2 ^ H :=
        fun h => hpack ((canPack_iff m l d H).mpr h)
      let toSub : Fin r → {B : Finset (OType m l r d) // FitsProp m l r d H B} :=
        fun a => ⟨alphabetFinset (m := m) (l := l) (fun _ => a), by
          obtain ⟨N, J, q, out, hshape, hq, hcert, hcard, himg, hH⟩ :=
            backward_dir m l r d hl hr (fun _ => a) H hW (Or.inl ⟨a, fun _ => rfl⟩)
          exact ⟨N, J, q, out, ⟨hshape, hq, hcert⟩, hcard, himg, hH⟩⟩
      have hbij : Function.Bijective toSub := by
        constructor
        · intro a₁ a₂ h
          have hval : alphabetFinset (m := m) (l := l) (fun _ : UType d => a₁) =
              alphabetFinset (m := m) (l := l) (fun _ : UType d => a₂) := congrArg Subtype.val h
          have hfn := alphabetFinset_injective hl hval
          exact congrFun hfn 0
        · rintro ⟨B, hB⟩
          obtain ⟨f, rfl⟩ := fits_exists_selector hB
          rcases hB with ⟨N, J, q, out, ⟨hshape, hq, hcert⟩, hcard, himg, hH⟩
          have hfwd := forward_dir m l r d hl hr f H N J q out hshape hq hcert hcard himg hH
          rcases hfwd.2 with ⟨a, ha⟩ | he
          · refine ⟨a, Subtype.ext ?_⟩
            have hfeq : (fun _ : UType d => a) = f := funext fun u => (ha u).symm
            change alphabetFinset (m := m) (l := l) (fun _ : UType d => a) =
              alphabetFinset (m := m) (l := l) f
            rw [hfeq]
          · exact absurd he hno_e
      let e := Equiv.ofBijective toSub hbij
      rw [Nat.card_congr e.symm, Nat.card_eq_fintype_card, Fintype.card_fin]

end PEqualNP.Outside.L_pcx_351_aux

theorem PEqualNP.Outside.L_pcx_351 :
    ∀ (m l r d : ℕ), 0 < l → 0 < r →
      let U := Fin d → ZMod 2
      let V := (Fin m → ZMod 2) × ((Fin r → Fin l → ZMod 2) × U)
      let O := Sum (Fin m) (Fin r × Fin l × U)
      let shape := fun (N J : Finset (List Bool)) =>
        [] ∈ N ∧ J ⊆ N ∧
        (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
        ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
      let queries := fun (V : Type) [AddCommGroup V] [Module (ZMod 2) V] =>
        {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}
      let cert := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
          (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) =>
        shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
          (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)
      let promised := fun (z : V) => ∀ a : Fin r, (∑ i, z.1 i) + (∑ j, z.2.1 a j) = 1
      let ok := fun (z : V) (o : O) => promised z →
        Sum.elim (fun i => z.1 i = 1)
          (fun x : Fin r × Fin l × U => z.2.1 x.1 x.2.1 = 1 ∧ x.2.2 = z.2.2) o
      let P := 2^d * l
      let W := m + P
      let fits := fun (H : ℕ) (B : Finset O) =>
        ∃ (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O),
          cert (queries V) ok N J q out ∧ (N \ J).card = W ∧ (N \ J).image out = B ∧
          ∀ p ∈ N \ J, p.length ≤ H
      ∀ H : ℕ,
        let canPack := ((Finset.range (H+1)).filter
          (fun e => P ≤ 2^e ∧ m + 2^e ≤ 2^H)).Nonempty
        Nat.card {B : Finset O // fits H B} =
          if 2^H < W then 0 else if canPack then r^(2^d) else r := by
  intro m l r d hl hr U V O shape queries cert promised ok P W fits H canPack
  exact PEqualNP.Outside.L_pcx_351_aux.count_fits m l r d H hl hr
