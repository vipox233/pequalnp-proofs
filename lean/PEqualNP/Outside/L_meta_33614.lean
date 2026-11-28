import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33614

def wstep (N : Finset (List Bool)) (q : List Bool → Bool) (p : List Bool) : List Bool :=
  if p ∈ N then p ++ [q p] else p

def walk (N : Finset (List Bool)) (q : List Bool → Bool) (n : ℕ) : List Bool :=
  (List.range n).foldl (fun p _ => wstep N q p) []

lemma walk_succ (N : Finset (List Bool)) (q : List Bool → Bool) (n : ℕ) :
    walk N q (n+1) = wstep N q (walk N q n) := by
  simp [walk, List.range_succ, List.foldl_append]

def Valid (N : Finset (List Bool)) (q : List Bool → Bool) (n : ℕ) (w : List Bool) : Prop :=
  w.length ≤ n ∧ (∀ j < w.length, w.take j ∈ N) ∧ (w.length = n ∨ w ∉ N) ∧
    (∀ (j : ℕ) (h : j < w.length), w[j] = q (w.take j))

lemma walk_valid (N : Finset (List Bool)) (q : List Bool → Bool) (n : ℕ) :
    Valid N q n (walk N q n) := by
  induction n with
  | zero => exact ⟨by simp [walk], by simp [walk], by simp [walk], by simp [walk]⟩
  | succ n ih =>
    rw [walk_succ]
    set w := walk N q n
    unfold wstep
    by_cases hw : w ∈ N
    · have hl : w.length = n := by
        rcases ih.2.2.1 with h | h
        · exact h
        · exact absurd hw h
      simp only [hw, ite_true]
      refine ⟨by simp [hl], ?_, by simp [hl], ?_⟩
      · intro j hj
        simp only [List.length_append, List.length_singleton] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · rw [List.take_append_of_le_length (by omega)]; exact ih.2.1 j h
        · subst h; rw [List.take_left' rfl]; exact hw
      · intro j hj
        simp only [List.length_append, List.length_singleton] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · rw [List.getElem_append_left h, List.take_append_of_le_length (by omega)]
          exact ih.2.2.2 j h
        · subst h
          rw [List.getElem_append_right (by omega), List.take_left' rfl]
          simp
    · simp only [hw, ite_false]
      exact ⟨by have := ih.1; omega, ih.2.1, Or.inr hw, ih.2.2.2⟩

lemma valid_unique {N : Finset (List Bool)} {q : List Bool → Bool} {n : ℕ} {w v : List Bool}
    (hw : Valid N q n w) (hv : Valid N q n v) : w = v := by

  have agree : ∀ j, j ≤ min w.length v.length → w.take j = v.take j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have h1 : j < w.length := by omega
      have h2 : j < v.length := by omega
      have e := ih (by omega)
      rw [← List.take_concat_get' w j h1, ← List.take_concat_get' v j h2, e,
        hw.2.2.2 j h1, hv.2.2.2 j h2, e]
  have key : ∀ {a b : List Bool}, Valid N q n a → Valid N q n b → a.length < b.length →
      a = b.take a.length → False := by
    intro a b ha hb hlt he
    have : a ∈ N := by rw [he]; exact hb.2.1 _ hlt
    rcases ha.2.2.1 with h | h
    · have := hb.1; omega
    · exact h this
  rcases lt_trichotomy w.length v.length with h | h | h
  · exfalso
    exact key hw hv h (by
      have := agree w.length (by omega); rwa [List.take_length] at this)
  · have := agree w.length (by omega)
    rwa [List.take_length, h, List.take_length] at this
  · exfalso
    have := agree v.length (by omega)
    rw [List.take_length] at this
    exact key hv hw h this.symm

lemma walk_eq_iff {N : Finset (List Bool)} {q : List Bool → Bool} {n : ℕ} {ℓ : List Bool}
    (hℓ : ℓ.length ≤ n ∧ (∀ j < ℓ.length, ℓ.take j ∈ N) ∧ (ℓ.length = n ∨ ℓ ∉ N)) :
    walk N q n = ℓ ↔ ∀ (j : ℕ) (h : j < ℓ.length), q (ℓ.take j) = ℓ[j] := by
  constructor
  · rintro rfl j h; exact ((walk_valid N q n).2.2.2 j h).symm
  · intro hb
    exact valid_unique (walk_valid N q n) ⟨hℓ.1, hℓ.2.1, hℓ.2.2, fun j h => (hb j h).symm⟩

lemma card_leaves (N Λ : Finset (List Bool))
    (hpre : ∀ ℓ ∈ Λ, ∀ j < ℓ.length, ℓ.take j ∈ N)
    (hanti : ∀ ℓ ∈ Λ, ∀ ℓ' ∈ Λ, ℓ <+: ℓ' → ℓ = ℓ') : Λ.card ≤ N.card + 1 := by
  induction h : N.card using Nat.strong_induction_on generalizing N Λ with
  | _ c ih =>
  subst h
  by_cases hnil : [] ∈ Λ
  · have : Λ = {[]} := by
      ext ℓ; simp only [Finset.mem_singleton]
      constructor
      · intro hl; exact (hanti [] hnil ℓ hl (List.nil_prefix)).symm
      · rintro rfl; exact hnil
    rw [this]; simp
  by_cases hΛ : Λ = ∅
  · simp [hΛ]
  obtain ⟨ℓ0, hℓ0⟩ := Finset.nonempty_iff_ne_empty.mpr hΛ
  have hNnil : [] ∈ N := by
    have hne : ℓ0 ≠ [] := fun h => hnil (h ▸ hℓ0)
    have := hpre ℓ0 hℓ0 0 (List.length_pos_iff.mpr hne)
    simpa using this

  let Lb : Bool → Finset (List Bool) := fun b => (Λ.filter (fun l => l.head? = some b)).image List.tail
  let Nb : Bool → Finset (List Bool) := fun b => (N.filter (fun l => l.head? = some b)).image List.tail
  have tail_inj : ∀ (S : Finset (List Bool)) (b : Bool),
      Set.InjOn List.tail (↑(S.filter (fun l => l.head? = some b)) : Set (List Bool)) := by
    intro S b x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
    match x, y, hx, hy with
    | a :: x', c :: y', ⟨_, hx⟩, ⟨_, hy⟩ =>
      simp at hx hy hxy; subst hx; subst hy; subst hxy; rfl
  have cardLb : ∀ b, (Lb b).card = (Λ.filter (fun l => l.head? = some b)).card :=
    fun b => Finset.card_image_of_injOn (tail_inj Λ b)
  have cardNb : ∀ b, (Nb b).card = (N.filter (fun l => l.head? = some b)).card :=
    fun b => Finset.card_image_of_injOn (tail_inj N b)
  have splitΛ : Λ.card = (Λ.filter (fun l => l.head? = some false)).card +
      (Λ.filter (fun l => l.head? = some true)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext l; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hl
        match l, hl with
        | [], hl => exact absurd hl hnil
        | false :: _, hl => exact Or.inl ⟨hl, rfl⟩
        | true :: _, hl => exact Or.inr ⟨hl, rfl⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · rw [Finset.disjoint_filter]; intro l _ h1 h2; rw [h1] at h2; simp at h2
  have splitN : (N.filter (fun l => l.head? = some false)).card +
      (N.filter (fun l => l.head? = some true)).card + 1 ≤ N.card := by
    have hd : Disjoint (N.filter (fun l => l.head? = some false))
        (N.filter (fun l => l.head? = some true)) := by
      rw [Finset.disjoint_filter]; intro l _ h1 h2; rw [h1] at h2; simp at h2
    rw [← Finset.card_union_of_disjoint hd]
    have hsub : insert [] (N.filter (fun l => l.head? = some false) ∪
        N.filter (fun l => l.head? = some true)) ⊆ N := by
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter] at hl
      rcases hl with rfl | ⟨h, _⟩ | ⟨h, _⟩
      · exact hNnil
      · exact h
      · exact h
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp)] at this
    exact this
  have sub : ∀ b, (Lb b).card ≤ (Nb b).card + 1 := by
    intro b
    apply ih (Nb b).card _ (Nb b) (Lb b) _ _ rfl
    · rw [cardNb]; cases b <;> omega
    · intro t ht j hj
      simp only [Lb, Finset.mem_image, Finset.mem_filter] at ht
      obtain ⟨l, ⟨hl, hh⟩, rfl⟩ := ht
      match l, hl, hh with
      | a :: l', hl, hh =>
        simp at hh; subst hh
        simp only [List.tail_cons] at hj ⊢
        have := hpre _ hl (j+1) (by simp; omega)
        simp only [Nb, Finset.mem_image, Finset.mem_filter]
        exact ⟨a :: l'.take j, ⟨by simpa using this, rfl⟩, rfl⟩
    · intro t ht t' ht' hpf
      simp only [Lb, Finset.mem_image, Finset.mem_filter] at ht ht'
      obtain ⟨l, ⟨hl, hh⟩, rfl⟩ := ht
      obtain ⟨l', ⟨hl', hh'⟩, rfl⟩ := ht'
      match l, l', hl, hl', hh, hh' with
      | a :: x, c :: y, hl, hl', hh, hh' =>
        simp at hh hh'; subst hh; subst hh'
        simp only [List.tail_cons] at hpf ⊢
        have := hanti _ hl _ hl' ((List.prefix_cons_inj _).mpr hpf)
        simpa using this
  have := sub false; have := sub true
  have := cardNb false; have := cardNb true
  rw [splitΛ, ← cardLb, ← cardLb]
  omega

lemma card_reached {X : Type*} [Fintype X] [DecidableEq X] (N : Finset (List Bool))
    (q : X → List Bool → Bool) :
    (Finset.univ.image (fun x => walk N (q x) N.card)).card ≤ N.card + 1 := by
  apply card_leaves N
  · intro ℓ hℓ
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hℓ
    obtain ⟨x, rfl⟩ := hℓ
    exact (walk_valid N (q x) N.card).2.1
  · intro ℓ hℓ ℓ' hℓ' hpf
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hℓ hℓ'
    obtain ⟨x, rfl⟩ := hℓ
    obtain ⟨x', rfl⟩ := hℓ'
    have hv := walk_valid N (q x) N.card
    have hv' := walk_valid N (q x') N.card
    set w := walk N (q x) N.card
    set w' := walk N (q x') N.card
    by_contra hne
    have hlt : w.length < w'.length := by
      have := hpf.length_le
      rcases this.lt_or_eq with h | h
      · exact h
      · exact absurd (hpf.eq_of_length h) hne
    have hmem : w ∈ N := by
      have e : w'.take w.length = w := (List.prefix_iff_eq_take.mp hpf).symm
      have := hv'.2.1 w.length hlt
      rwa [e] at this
    rcases hv.2.2.1 with h | h
    · have := hv'.1; omega
    · exact h hmem

lemma allwrong {K ι V : Type*} [CommRing K] [AddCommGroup V] [Module K V] [DecidableEq ι]
    (α β : ι → V →ₗ[K] K) (p q : ι → K) (N : Finset ι)
    (hs : ∀ z : ι → K × K, ∃ v, ∀ i ∈ N, α i v = (z i).1 ∧ β i v = (z i).2)
    (g : ι → V →ₗ[K] K) (c : ι → K) :
    ∃ v, ∀ i ∈ N, (α i v + p i) * (β i v + q i) + g i v + c i = 1 := by
  induction N using Finset.induction_on generalizing g c with
  | empty => exact ⟨0, by simp⟩
  | insert i0 N hi0 ih =>
    obtain ⟨Ua, hUa⟩ := hs (fun i => if i = i0 then (1,0) else (0,0))
    obtain ⟨Ub, hUb⟩ := hs (fun i => if i = i0 then (0,1) else (0,0))
    have hsN : ∀ z : ι → K × K, ∃ v, ∀ i ∈ N, α i v = (z i).1 ∧ β i v = (z i).2 := fun z => by
      obtain ⟨v, hv⟩ := hs z; exact ⟨v, fun i hi => hv i (Finset.mem_insert_of_mem hi)⟩
    have a1 := hUa i0 (Finset.mem_insert_self _ _)
    have b1 := hUb i0 (Finset.mem_insert_self _ _)
    simp only [ite_true] at a1 b1
    let a0 := α i0
    let b0 := β i0
    let δ := g i0
    let s : K := 1 - p i0 - δ Ub
    let Rl : V →ₗ[K] K := δ - (δ Ua) • a0 - (δ Ub) • b0
    let Rc : K := (s + p i0) * q i0 + s * δ Ua + c i0
    let g' : ι → V →ₗ[K] K := fun i => g i - (g i Ua) • a0 - (g i Ub) • (Rl + b0)
    let c' : ι → K := fun i => c i + s * g i Ua + (1 - Rc) * g i Ub
    obtain ⟨v', hv'⟩ := ih hsN g' c'
    let t : K := 1 - (Rl v' + Rc)
    refine ⟨v' + (s - a0 v') • Ua + (t - b0 v') • Ub, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simp only [map_add, map_smul, smul_eq_mul]
      simp only [a0, b0, a1.1, a1.2, b1.1, b1.2]
      simp only [t, Rl, Rc, s, δ, a0, b0, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    · have hne : i ≠ i0 := fun h => hi0 (h ▸ hi)
      have a2 := hUa i (Finset.mem_insert_of_mem hi)
      have b2 := hUb i (Finset.mem_insert_of_mem hi)
      simp only [hne, ite_false] at a2 b2
      have h := hv' i hi
      simp only [map_add, map_smul, smul_eq_mul, a2.1, a2.2, b2.1, b2.2]
      simp only [g', c', t, Rl, Rc, s, δ, a0, b0, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.add_apply, smul_eq_mul] at h ⊢
      linear_combination h

variable {k : ℕ}

def supp (P : Finset (Fin k)) : Submodule (ZMod 2) (Fin k → ZMod 2) :=
  { carrier := {w | ∀ j, j ∉ P → w j = 0},
    zero_mem' := by intro j _; rfl,
    smul_mem' := by intro c x hx j hj; simp [hx j hj], add_mem' := by
      intro x y hx hy j hj; simp [hx j hj, hy j hj] }

lemma mem_supp {P : Finset (Fin k)} {w : Fin k → ZMod 2} : w ∈ supp P ↔ ∀ j, j ∉ P → w j = 0 :=
  Iff.rfl

lemma supp_mono {P Q : Finset (Fin k)} (h : P ⊆ Q) : supp P ≤ supp Q := by
  intro w hw j hj; exact hw j (fun h' => hj (h h'))

def pairsOf (T : Finset (Fin k)) (a b : Fin k → Fin k) : Finset (Fin k) :=
  T.biUnion (fun i => {a i, b i})

lemma pairsOf_mono {T T' : Finset (Fin k)} (a b : Fin k → Fin k) (h : T ⊆ T') :
    pairsOf T a b ⊆ pairsOf T' a b := Finset.biUnion_subset_biUnion_of_subset_left _ h

def PairsDisjoint (S : Finset (Fin k)) (a b : Fin k → Fin k) : Prop :=
  ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → a i ≠ a i' ∧ a i ≠ b i' ∧ b i ≠ a i' ∧ b i ≠ b i'

lemma pivot (a b : Fin k → Fin k) :
    ∀ (d : ℕ) (P : Submodule (ZMod 2) (Fin k → ZMod 2)) (S : Finset (Fin k)),
      PairsDisjoint S a b → Module.finrank (ZMod 2) P ≤ d →
      ∃ X ⊆ S, X.card ≤ d ∧ P ⊓ supp (pairsOf (S \ X) a b) = ⊥ := by
  intro d
  induction d with
  | zero =>
    intro P S _ hP
    refine ⟨∅, by simp, by simp, ?_⟩
    have : P = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    simp [this]
  | succ d ih =>
    intro P S hD hP
    by_cases h0 : P ⊓ supp (pairsOf S a b) = ⊥
    · exact ⟨∅, by simp, by simp, by simpa using h0⟩
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    rw [Submodule.mem_inf] at hw
    obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
      by_contra hc; push Not at hc; exact hw0 (funext hc)
    have hjP : j ∈ pairsOf S a b := by
      by_contra hc; exact hj (hw.2 j hc)
    simp only [pairsOf, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hjP
    obtain ⟨i0, hi0, hji⟩ := hjP
    let P' := P ⊓ supp (pairsOf (S.erase i0) a b)
    have hjnot : j ∉ pairsOf (S.erase i0) a b := by
      simp only [pairsOf, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_insert,
        Finset.mem_singleton, not_exists, not_and]
      rintro i ⟨hne, hi⟩ hj'
      have := hD i0 hi0 i hi (Ne.symm hne)
      rcases hji with rfl | rfl <;> rcases hj' with h | h <;> simp_all
    have hlt : P' < P := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro heq
      have : w ∈ P' := heq ▸ hw.1
      exact hj ((Submodule.mem_inf.mp this).2 j hjnot)
    have hfr := Submodule.finrank_lt_finrank_of_lt hlt
    have hD' : PairsDisjoint (S.erase i0) a b := fun i hi i' hi' hne =>
      hD i (Finset.mem_of_mem_erase hi) i' (Finset.mem_of_mem_erase hi') hne
    obtain ⟨X', hX'S, hX'c, hX'⟩ := ih P' (S.erase i0) hD' (by omega)
    refine ⟨insert i0 X', ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hi0
      · exact Finset.mem_of_mem_erase (hX'S hx)
    · exact (Finset.card_insert_le _ _).trans (by omega)
    · have hset : S \ insert i0 X' = S.erase i0 \ X' := by
        ext x; simp [Finset.mem_sdiff, Finset.mem_erase]; tauto
      rw [hset, eq_bot_iff]
      intro x hx
      rw [← hX']
      refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx).1, ?_⟩,
        (Submodule.mem_inf.mp hx).2⟩
      exact supp_mono (pairsOf_mono a b Finset.sdiff_subset) (Submodule.mem_inf.mp hx).2

noncomputable def Psi (Y : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] Module.Dual (ZMod 2) (Fin k → ZMod 2) :=
  ∑ j, (LinearMap.proj j : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2).smulRight
    ((LinearMap.proj j).comp Y)

lemma Psi_apply (Y : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) (w z : Fin k → ZMod 2) :
    Psi Y w z = ∑ j, w j * Y z j := by
  simp [Psi, LinearMap.sum_apply, LinearMap.smulRight_apply]

lemma phi_expand {N : Type*} [Fintype N] [DecidableEq N]
    (φ : (N → ZMod 2 × ZMod 2) →ₗ[ZMod 2] ZMod 2) (z : N → ZMod 2 × ZMod 2) :
    φ z = ∑ i, ((z i).1 * φ (Pi.single i (1, 0)) + (z i).2 * φ (Pi.single i (0, 1))) := by
  conv_lhs => rw [← Finset.univ_sum_single z]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : (z i) = (z i).1 • ((1 : ZMod 2), (0 : ZMod 2)) + (z i).2 • ((0 : ZMod 2), (1 : ZMod 2)) := by
    ext <;> simp
  rw [this, Pi.single_add, Pi.single_smul', Pi.single_smul', map_add, map_smul, map_smul]
  simp [smul_eq_mul]

theorem core (Y : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) (y0 : Fin k → ZMod 2)
    (S : Finset (Fin k)) (a b : Fin k → Fin k) (hD : PairsDisjoint S a b)
    (hab : ∀ i ∈ S, a i ≠ b i) (sav : ℕ)
    (hC : ∀ w : Fin k → ZMod 2, w ∈ supp (pairsOf S a b) → (∀ z, ∑ j, w j * Y z j = 0) → w ≠ 0 →
      sav = 1 ∧ ∀ i ∈ S, w (a i) ≠ 0 ∨ w (b i) ≠ 0)
    {d : ℕ} (f : Fin d → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) (cst : Fin d → ZMod 2)
    (x0 : Fin k → ZMod 2) (hx0 : ∀ j, f j x0 = cst j)
    (g : Fin k → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) (c : Fin k → ZMod 2) :
    ∃ x, (∀ j, f j x = cst j) ∧
      S.card - d - sav ≤ (S.filter (fun i =>
        (Y x (a i) + y0 (a i)) * (Y x (b i) + y0 (b i)) + g i x + c i ≠ 0)).card := by
  classical
  set E := pairsOf S a b
  let Cs : Submodule (ZMod 2) (Fin k → ZMod 2) := supp E ⊓ LinearMap.ker (Psi Y)
  let R : Submodule (ZMod 2) (Fin k → ZMod 2) :=
    supp E ⊓ (Submodule.span (ZMod 2) (Set.range f)).comap (Psi Y)
  have hCR : Cs ≤ R := by
    intro w hw
    refine Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hw).1, ?_⟩
    rw [Submodule.mem_comap, LinearMap.mem_ker.mp (Submodule.mem_inf.mp hw).2]
    exact Submodule.zero_mem _

  have hnot : ∀ i0 ∈ S, ∀ T ⊆ S.erase i0, a i0 ∉ pairsOf T a b ∧ b i0 ∉ pairsOf T a b := by
    intro i0 hi0 T hT
    simp only [pairsOf, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, not_exists,
      not_and]
    constructor <;> intro i hi <;> have hi' := hT hi <;>
      have hne := (Finset.mem_erase.mp hi').1 <;>
      have := hD i0 hi0 i (Finset.mem_erase.mp hi').2 (Ne.symm hne) <;> tauto

  obtain ⟨X0, hX0S, hX0c, hX0⟩ : ∃ X0 ⊆ S, X0.card ≤ sav ∧ Cs ⊓ supp (pairsOf (S \ X0) a b) = ⊥ := by
    by_cases hc : Cs = ⊥
    · exact ⟨∅, by simp, by simp, by simp [hc]⟩
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
    have hw' := hC w (Submodule.mem_inf.mp hw).1
      (fun z => by rw [← Psi_apply, LinearMap.mem_ker.mp (Submodule.mem_inf.mp hw).2]; rfl) hw0
    by_cases hS : S = ∅
    · refine ⟨∅, by simp, by simp, ?_⟩
      rw [eq_bot_iff]; intro x hx
      have h2 := (Submodule.mem_inf.mp hx).2
      simp only [hS, Finset.empty_sdiff, pairsOf, Finset.biUnion_empty] at h2
      exact (Submodule.mem_bot _).mpr (funext fun j => h2 j (by simp))
    obtain ⟨i0, hi0⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    refine ⟨{i0}, by simpa using hi0, by simp [hw'.1], ?_⟩
    rw [eq_bot_iff]; intro x hx
    rw [Submodule.mem_bot]
    by_contra hx0
    have hx1 := (Submodule.mem_inf.mp hx).1
    have := (hC x (Submodule.mem_inf.mp hx1).1
      (fun z => by rw [← Psi_apply, LinearMap.mem_ker.mp (Submodule.mem_inf.mp hx1).2]; rfl) hx0).2
      i0 hi0
    have hsub : S \ {i0} ⊆ S.erase i0 := by intro y hy; simp at hy ⊢; tauto
    have hn := hnot i0 hi0 _ hsub
    have h2 := (Submodule.mem_inf.mp hx).2
    rcases this with h | h
    · exact h (h2 _ hn.1)
    · exact h (h2 _ hn.2)

  let R' := R ⊓ supp (pairsOf (S \ X0) a b)
  have hRd : Module.finrank (ZMod 2) R ≤ Module.finrank (ZMod 2) Cs + d := by
    have h1 := LinearMap.finrank_range_add_finrank_ker ((Psi Y).domRestrict R)
    have h2 : Module.finrank (ZMod 2) (LinearMap.range ((Psi Y).domRestrict R)) ≤ d := by
      have hle : LinearMap.range ((Psi Y).domRestrict R) ≤ Submodule.span (ZMod 2) (Set.range f) := by
        rintro _ ⟨x, rfl⟩
        exact (Submodule.mem_inf.mp x.2).2
      refine (Submodule.finrank_mono hle).trans ?_
      have := finrank_range_le_card (R := ZMod 2) f
      simpa [Set.finrank] using this
    have h3 : Module.finrank (ZMod 2) (LinearMap.ker ((Psi Y).domRestrict R)) ≤
        Module.finrank (ZMod 2) Cs := by
      rw [← Submodule.finrank_map_subtype_eq]
      apply Submodule.finrank_mono
      rintro _ ⟨x, hx, rfl⟩
      refine Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp x.2).1, ?_⟩
      simpa [LinearMap.mem_ker] using hx
    omega
  have hR'd : Module.finrank (ZMod 2) R' ≤ d := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq R' Cs
    have hinf : R' ⊓ Cs = ⊥ := by
      rw [eq_bot_iff, ← hX0]
      intro x hx
      exact Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx).2,
        (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx).1).2⟩
    rw [hinf, finrank_bot] at h
    have hsup : R' ⊔ Cs ≤ R := sup_le inf_le_left hCR
    have := Submodule.finrank_mono hsup
    omega

  have hDX : PairsDisjoint (S \ X0) a b := fun i hi i' hi' hne =>
    hD i (Finset.mem_sdiff.mp hi).1 i' (Finset.mem_sdiff.mp hi').1 hne
  obtain ⟨X1, hX1S, hX1c, hX1⟩ := pivot a b d R' (S \ X0) hDX hR'd
  set N := (S \ X0) \ X1 with hN
  have hNS : N ⊆ S := fun i hi => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hi).1).1
  have hNcard : S.card - d - sav ≤ N.card := by
    have e1 : (S \ X0).card = S.card - X0.card := Finset.card_sdiff_of_subset hX0S
    have e2 : N.card = (S \ X0).card - X1.card := Finset.card_sdiff_of_subset hX1S
    omega
  have hRN : R ⊓ supp (pairsOf N a b) = ⊥ := by
    rw [eq_bot_iff, ← hX1]
    intro x hx
    have hxR := (Submodule.mem_inf.mp hx).1
    have hxN := (Submodule.mem_inf.mp hx).2
    exact Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hxR,
      supp_mono (pairsOf_mono a b Finset.sdiff_subset) hxN⟩, hxN⟩

  let V : Submodule (ZMod 2) (Fin k → ZMod 2) := ⨅ j, LinearMap.ker (f j)
  have hsurj : ∀ z : Fin k → ZMod 2 × ZMod 2, ∃ v : V, ∀ i ∈ N,
      Y v (a i) = (z i).1 ∧ Y v (b i) = (z i).2 := by
    let T : V →ₗ[ZMod 2] (N → ZMod 2 × ZMod 2) :=
      LinearMap.pi (fun i => LinearMap.prod
        ((LinearMap.proj (a i)).comp (Y.comp V.subtype))
        ((LinearMap.proj (b i)).comp (Y.comp V.subtype)))
    have hT : LinearMap.range T = ⊤ := by
      by_contra hne
      obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
      let w : Fin k → ZMod 2 := fun j => ∑ i : N,
        ((if a i = j then φ (Pi.single i (1, 0)) else 0) +
          (if b i = j then φ (Pi.single i (0, 1)) else 0))
      have hwsum : ∀ x : Fin k → ZMod 2, ∑ j, w j * Y x j = ∑ i : N,
          (φ (Pi.single i (1, 0)) * Y x (a i) + φ (Pi.single i (0, 1)) * Y x (b i)) := by
        intro x
        simp only [w, Finset.sum_mul, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib]
        rw [Finset.sum_comm, Finset.sum_comm (f := fun j (i : N) => _ )]
        simp [Finset.sum_ite_eq]
      have hwR : w ∈ R := by
        refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
        · intro j hj
          simp only [w]
          apply Finset.sum_eq_zero
          intro i _
          have hiS := hNS i.2
          have ha : a i ≠ j := fun h => hj (by
            simp only [E, pairsOf, Finset.mem_biUnion]; exact ⟨i, hiS, by simp [h]⟩)
          have hb : b i ≠ j := fun h => hj (by
            simp only [E, pairsOf, Finset.mem_biUnion]; exact ⟨i, hiS, by simp [h]⟩)
          simp [ha, hb]
        · rw [Submodule.mem_comap]
          apply mem_span_of_iInf_ker_le_ker
          intro x hx
          rw [LinearMap.mem_ker, Psi_apply, hwsum]
          have hxV : x ∈ V := hx
          have := hφ (LinearMap.mem_range_self T ⟨x, hxV⟩)
          rw [LinearMap.mem_ker, phi_expand] at this
          refine Eq.trans ?_ this
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp [T]; ring
      have hwN : w ∈ supp (pairsOf N a b) := by
        intro j hj
        simp only [w]
        apply Finset.sum_eq_zero
        intro i _
        have ha : a i ≠ j := fun h => hj (by
          simp only [pairsOf, Finset.mem_biUnion]; exact ⟨i, i.2, by simp [h]⟩)
        have hb : b i ≠ j := fun h => hj (by
          simp only [pairsOf, Finset.mem_biUnion]; exact ⟨i, i.2, by simp [h]⟩)
        simp [ha, hb]
      have hw0 : w = 0 := by
        have := Submodule.mem_inf.mpr ⟨hwR, hwN⟩
        rw [hRN] at this
        exact (Submodule.mem_bot _).mp this
      apply hφ0
      refine LinearMap.ext (fun z => ?_)
      rw [phi_expand]
      simp only [LinearMap.zero_apply]
      apply Finset.sum_eq_zero
      intro i _
      have hval : ∀ (i : N), w (a i) = φ (Pi.single i (1, 0)) ∧ w (b i) = φ (Pi.single i (0, 1)) := by
        intro i
        have hiS := hNS i.2
        constructor
        · simp only [w]
          rw [Finset.sum_eq_single i]
          · simp [Ne.symm (hab i hiS)]
          · intro i' _ hne
            have hne' : (i' : Fin k) ≠ i := fun h => hne (Subtype.ext h)
            have := hD i' (hNS i'.2) i hiS hne'
            simp [this.1, this.2.2.1]
          · simp
        · simp only [w]
          rw [Finset.sum_eq_single i]
          · simp [hab i hiS]
          · intro i' _ hne
            have hne' : (i' : Fin k) ≠ i := fun h => hne (Subtype.ext h)
            have := hD i' (hNS i'.2) i hiS hne'
            simp [this.2.1, this.2.2.2]
          · simp
      rw [← (hval i).1, ← (hval i).2, hw0]
      simp
    intro z
    obtain ⟨v, hv⟩ : (fun i : N => z i) ∈ LinearMap.range T := hT ▸ Submodule.mem_top
    refine ⟨v, fun i hi => ?_⟩
    have := congrFun hv ⟨i, hi⟩
    simp only [T, LinearMap.pi_apply, LinearMap.prod_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.coe_proj, Function.eval, Submodule.coe_subtype] at this
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

  obtain ⟨v, hv⟩ := allwrong (V := V)
    (fun i => (LinearMap.proj (a i)).comp (Y.comp V.subtype))
    (fun i => (LinearMap.proj (b i)).comp (Y.comp V.subtype))
    (fun i => Y x0 (a i) + y0 (a i)) (fun i => Y x0 (b i) + y0 (b i)) N
    (fun z => by
      obtain ⟨v, hv⟩ := hsurj z
      exact ⟨v, fun i hi => by simpa using hv i hi⟩)
    (fun i => (g i).comp V.subtype) (fun i => g i x0 + c i)
  refine ⟨x0 + v, ?_, ?_⟩
  · intro j
    have : (v : Fin k → ZMod 2) ∈ LinearMap.ker (f j) := (Submodule.mem_iInf _).mp v.2 j
    rw [map_add, LinearMap.mem_ker.mp this, add_zero, hx0]
  · refine hNcard.trans (Finset.card_le_card ?_)
    intro i hi
    refine Finset.mem_filter.mpr ⟨hNS hi, ?_⟩
    have := hv i hi
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
      Submodule.coe_subtype] at this
    rw [map_add, map_add]
    simp only [Pi.add_apply]
    intro h0
    have h1 : (Y (↑v) (a i) + (Y x0 (a i) + y0 (a i))) * (Y (↑v) (b i) + (Y x0 (b i) + y0 (b i))) +
        (g i) ↑v + (g i x0 + c i) =
        (Y x0 (a i) + Y (↑v) (a i) + y0 (a i)) * (Y x0 (b i) + Y (↑v) (b i) + y0 (b i)) +
        (g i x0 + g i ↑v) + c i := by ring
    rw [h1, h0] at this
    exact zero_ne_one this

def ixf (k : ℕ) (hk : 0 < k) (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

def pr (k : ℕ) (j : Fin k) : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 := LinearMap.proj j

noncomputable def Ymap (k : ℕ) (hk : 0 < k) (s sp : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
  LinearMap.pi (fun u : Fin k => pr k (ixf k hk (u.val + k - s % k)) +
    pr k (ixf k hk ((ixf k hk (u.val + sp)).val + k - s % k)) +
    pr k (ixf k hk ((ixf k hk (u.val + k - sp % k)).val + k - s % k)))

lemma Ymap_apply (k : ℕ) (hk : 0 < k) (s sp : ℕ) (z : Fin k → ZMod 2) (u : Fin k) :
    Ymap k hk s sp z u = z (ixf k hk (u.val + k - s % k)) +
      z (ixf k hk ((ixf k hk (u.val + sp)).val + k - s % k)) +
      z (ixf k hk ((ixf k hk (u.val + k - sp % k)).val + k - s % k)) := by
  simp [Ymap, pr]

section Part1
open Fin.NatCast Fin.CommRing
variable {k : ℕ} [NeZero k]

lemma ixf_eq (hk : 0 < k) (n : ℕ) : ixf k hk n = (n : Fin k) := by
  ext; simp [ixf, Fin.val_natCast]

lemma natCast_sub_mod (n : ℕ) : (((k - n % k : ℕ)) : Fin k) = -(n : Fin k) := by
  have h : n % k < k := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne k))
  rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add]
  rw [Fin.natCast_eq_zero]
  have : k - n % k + n = k * (n / k + 1) := by
    have := Nat.div_add_mod n k
    rw [Nat.mul_add, Nat.mul_one]; omega
  rw [this]; exact Nat.dvd_mul_right _ _

lemma ixf_add (hk : 0 < k) (u : Fin k) (c : ℕ) : ixf k hk (u.val + c) = u + (c : Fin k) := by
  rw [ixf_eq, Nat.cast_add, Fin.cast_val_eq_self]

lemma ixf_sub (hk : 0 < k) (u : Fin k) (c : ℕ) : ixf k hk (u.val + k - c % k) = u - (c : Fin k) := by
  have h : c % k < k := Nat.mod_lt _ hk
  rw [show u.val + k - c % k = u.val + (k - c % k) by omega, ixf_add, natCast_sub_mod, sub_eq_add_neg]

lemma Ymap_apply' (hk : 0 < k) (s sp : ℕ) (z : Fin k → ZMod 2) (u : Fin k) :
    Ymap k hk s sp z u = z (u - s) + z (u + sp - s) + z (u - sp - s) := by
  rw [Ymap_apply, ixf_sub, ixf_add, ixf_sub, ixf_sub, ixf_sub]

lemma sum_shift (w z : Fin k → ZMod 2) (c : Fin k) :
    ∑ j, w j * z (j + c) = ∑ i, w (i - c) * z i := by
  exact Fintype.sum_equiv (Equiv.addRight c) _ _ (fun j => by simp)

lemma transposed (hk : 0 < k) (s sp : ℕ) (w : Fin k → ZMod 2)
    (hw : ∀ z, ∑ j, w j * Ymap k hk s sp z j = 0) (u : Fin k) :
    w u + w (u - sp) + w (u + sp) = 0 := by
  have h := hw (Pi.single (u - s) 1)
  simp only [Ymap_apply', mul_add, Finset.sum_add_distrib] at h
  have e1 : ∀ c : Fin k, ∑ j, w j * (Pi.single (u - s) (1 : ZMod 2) : Fin k → ZMod 2) (j + c) =
      w (u - s - c) := by
    intro c
    rw [sum_shift]
    simp [Pi.single_apply]
  have r1 : (∑ x, w x * (Pi.single (u - s) (1 : ZMod 2) : Fin k → ZMod 2) (x - s)) = w u := by
    have := e1 (-(s : Fin k))
    rw [show u - (s : Fin k) - -(s : Fin k) = u by abel] at this
    rw [← this]; refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 2; abel
  have r2 : (∑ x, w x * (Pi.single (u - s) (1 : ZMod 2) : Fin k → ZMod 2) (x + sp - s)) =
      w (u - sp) := by
    have := e1 ((sp : Fin k) - s)
    rw [show u - (s : Fin k) - ((sp : Fin k) - s) = u - sp by abel] at this
    rw [← this]; refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 2; abel
  have r3 : (∑ x, w x * (Pi.single (u - s) (1 : ZMod 2) : Fin k → ZMod 2) (x - sp - s)) =
      w (u + sp) := by
    have := e1 (-(sp : Fin k) - s)
    rw [show u - (s : Fin k) - (-(sp : Fin k) - s) = u + sp by abel] at this
    rw [← this]; refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 2; abel
  rw [r1, r2, r3] at h
  exact h

lemma period (hk : 0 < k) (s sp : ℕ) (w : Fin k → ZMod 2)
    (hw : ∀ z, ∑ j, w j * Ymap k hk s sp z j = 0) (u : Fin k) :
    w (u + 3 * sp) = w u := by
  have h1 := transposed hk s sp w hw (u + 2 * sp)
  have h2 := transposed hk s sp w hw (u + sp)
  have e1 : u + 2 * (sp : Fin k) - sp = u + sp := by ring
  have e2 : u + 2 * (sp : Fin k) + sp = u + 3 * sp := by ring
  have e3 : u + (sp : Fin k) - sp = u := by ring
  have e4 : u + (sp : Fin k) + sp = u + 2 * sp := by ring
  rw [e1, e2] at h1; rw [e3, e4] at h2
  linear_combination h1 - h2

lemma period_iter (hk : 0 < k) (s sp : ℕ) (w : Fin k → ZMod 2)
    (hw : ∀ z, ∑ j, w j * Ymap k hk s sp z j = 0) (u : Fin k) (n : ℕ) :
    w (u + (n : Fin k) * (3 * sp)) = w u := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, period hk s sp w hw, ih]

lemma cast_mod (n : ℕ) : (((n % k : ℕ)) : Fin k) = (n : Fin k) := Fin.ext (by simp [Nat.mod_mod])

lemma shift_inv (hk1 : 1 < k) (sp : ℕ) (hcop : Nat.Coprime k sp) :
    ∃ n : ℕ, (n : Fin k) * (3 * (sp : Fin k)) = (if Nat.Coprime k 3 then 1 else 3) := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop.symm hk1
  have hspm : (sp : Fin k) * (m : Fin k) = 1 := by
    rw [← Nat.cast_mul, ← cast_mod, hm, Nat.cast_one]
  split_ifs with h3
  · obtain ⟨m3, -, hm3⟩ := Nat.exists_mul_mod_eq_one_of_coprime h3.symm hk1
    have h3m : (3 : Fin k) * (m3 : Fin k) = 1 := by
      have : ((3 * m3 : ℕ) : Fin k) = 1 := by rw [← cast_mod, hm3, Nat.cast_one]
      simpa using this
    refine ⟨m * m3, ?_⟩
    rw [Nat.cast_mul]
    linear_combination (3 * (m3 : Fin k)) * hspm + h3m
  · refine ⟨m, ?_⟩
    linear_combination 3 * hspm

lemma const_of_shift1 (w : Fin k → ZMod 2) (h : ∀ u, w (u + 1) = w u) (u : Fin k) : w u = w 0 := by
  have : ∀ j : ℕ, w (j : Fin k) = w 0 := by
    intro j; induction j with
    | zero => simp
    | succ j ih => rw [Nat.cast_succ, h, ih]
  rw [← this u.val, Fin.cast_val_eq_self]

lemma mod3_of_shift3 (h3 : 3 ∣ k) (w : Fin k → ZMod 2) (h : ∀ u, w (u + 3) = w u) (u : Fin k) :
    w u = w ((u.val % 3 : ℕ) : Fin k) := by
  have : ∀ r q : ℕ, w ((r + 3 * q : ℕ) : Fin k) = w (r : Fin k) := by
    intro r q; induction q with
    | zero => simp
    | succ q ih =>
      rw [show r + 3 * (q + 1) = (r + 3 * q) + 3 by ring, Nat.cast_add, Nat.cast_ofNat, h, ih]
  conv_lhs => rw [← Fin.cast_val_eq_self u, ← Nat.mod_add_div u.val 3]
  exact this _ _

lemma classes (hk : 0 < k) (hk1 : 1 < k) (s sp : ℕ) (hcop : Nat.Coprime k sp) (w : Fin k → ZMod 2)
    (hw : ∀ z, ∑ j, w j * Ymap k hk s sp z j = 0) (hw0 : w ≠ 0) :
    3 ∣ k ∧ (∀ u : Fin k, w u = w ((u.val % 3 : ℕ) : Fin k)) ∧
      w ((0 : ℕ) : Fin k) + w ((1 : ℕ) : Fin k) + w ((2 : ℕ) : Fin k) = 0 := by
  obtain ⟨n, hn⟩ := shift_inv hk1 sp hcop
  have hper := period_iter hk s sp w hw
  by_cases h3 : Nat.Coprime k 3
  · exfalso
    rw [if_pos h3] at hn
    have h1 : ∀ u, w (u + 1) = w u := fun u => by rw [← hn]; exact hper u n
    have hc := const_of_shift1 w h1
    have := transposed hk s sp w hw 0
    rw [hc (0 - sp), hc (0 + sp)] at this
    have hz : w 0 = 0 := by
      have e : ∀ x : ZMod 2, x + x + x = x := by decide
      rw [e] at this; exact this
    exact hw0 (funext fun u => by rw [hc u, hz]; rfl)
  · have hdvd : 3 ∣ k := by
      by_contra hd
      exact h3 (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hd))
    rw [if_neg h3] at hn
    have hs3 : ∀ u, w (u + 3) = w u := fun u => by rw [← hn]; exact hper u n
    have hm := mod3_of_shift3 hdvd w hs3
    refine ⟨hdvd, hm, ?_⟩
    have hrel := transposed hk s sp w hw 0

    have e1 : w (0 - (sp : Fin k)) = w (2 * (sp : Fin k)) := by
      have := hper (0 - (sp : Fin k)) 1
      rw [Nat.cast_one, one_mul, show (0 : Fin k) - sp + 3 * sp = 2 * sp by ring] at this
      exact this.symm
    rw [e1, zero_add] at hrel
    have hsp3 : ¬ 3 ∣ sp := by
      intro hd
      have := Nat.Coprime.coprime_dvd_left hdvd hcop
      exact absurd (Nat.Coprime.coprime_dvd_right hd this) (by decide)
    have v1 : w (sp : Fin k) = w ((sp % 3 : ℕ) : Fin k) := by
      rw [hm]; congr 2; simp [Fin.val_natCast, Nat.mod_mod_of_dvd _ hdvd]
    have v2 : w (2 * (sp : Fin k)) = w ((2 * sp % 3 : ℕ) : Fin k) := by
      rw [show (2 : Fin k) * (sp : Fin k) = ((2 * sp : ℕ) : Fin k) by push_cast; ring, hm]
      congr 2; rw [Fin.val_natCast, Nat.mod_mod_of_dvd _ hdvd]
    rw [v1, v2] at hrel
    have hr : sp % 3 = 1 ∨ sp % 3 = 2 := by omega
    rcases hr with hr | hr
    · rw [hr, show 2 * sp % 3 = 2 by omega] at hrel
      rw [Nat.cast_zero]; linear_combination hrel
    · rw [hr, show 2 * sp % 3 = 1 by omega] at hrel
      rw [Nat.cast_zero]; linear_combination hrel

lemma hC_spec (hk : 0 < k) (hk1 : 1 < k) (s sp : ℕ) (hcop : Nat.Coprime k sp)
    (sites : Finset (Fin k)) (w : Fin k → ZMod 2)
    (hsupp : ∀ j, j ∉ sites.biUnion (fun i => ({ixf k hk (i.val+1), ixf k hk (i.val+2)} : Finset (Fin k))) →
      w j = 0)
    (hw : ∀ z, ∑ j, w j * Ymap k hk s sp z j = 0) (hw0 : w ≠ 0) :
    (3 ∣ k ∧ 2 ≤ ((Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 3 = r →
        j ∈ sites.biUnion (fun i => ({ixf k hk (i.val+1), ixf k hk (i.val+2)} : Finset (Fin k))))).card) ∧
    ∀ i ∈ sites, w (ixf k hk (i.val+1)) ≠ 0 ∨ w (ixf k hk (i.val+2)) ≠ 0 := by
  obtain ⟨h3, hm, hsum⟩ := classes hk hk1 s sp hcop w hw hw0
  set c : ℕ → ZMod 2 := fun r => w ((r : ℕ) : Fin k) with hc
  obtain ⟨u, hu⟩ : ∃ u, w u ≠ 0 := by
    by_contra h; push Not at h; exact hw0 (funext h)
  have hnz : c 0 ≠ 0 ∨ c 1 ≠ 0 ∨ c 2 ≠ 0 := by
    rw [hm] at hu
    have : u.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases h : u.val % 3 <;> simp_all [c]
  have hs : c 0 + c 1 + c 2 = 0 := hsum
  have two : ∀ x y z : ZMod 2, x + y + z = 0 → (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) →
      ((x ≠ 0 ∧ y ≠ 0) ∨ (x ≠ 0 ∧ z ≠ 0) ∨ (y ≠ 0 ∧ z ≠ 0)) ∧
      (x ≠ 0 ∨ y ≠ 0) ∧ (x ≠ 0 ∨ z ≠ 0) ∧ (y ≠ 0 ∨ z ≠ 0) := by decide
  obtain ⟨hpair, h01, h02, h12⟩ := two _ _ _ hs hnz
  have hval : ∀ j : Fin k, w j = c (j.val % 3) := fun j => hm j
  have hmod : ∀ n : ℕ, (ixf k hk n).val % 3 = n % 3 := fun n => by
    simp [ixf, Nat.mod_mod_of_dvd _ h3]
  refine ⟨⟨h3, ?_⟩, ?_⟩
  · have mem : ∀ r < 3, c r ≠ 0 → r ∈ (Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 3 = r →
        j ∈ sites.biUnion (fun i => ({ixf k hk (i.val+1), ixf k hk (i.val+2)} : Finset (Fin k)))) := by
      intro r hr hcr
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, fun j hj => ?_⟩
      by_contra hn
      have := hsupp j hn
      rw [hval j, hj] at this
      exact hcr this
    rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have := Finset.card_le_card (Finset.insert_subset (mem 0 (by norm_num) ha)
        (Finset.singleton_subset_iff.mpr (mem 1 (by norm_num) hb)))
      simpa using this
    · have := Finset.card_le_card (Finset.insert_subset (mem 0 (by norm_num) ha)
        (Finset.singleton_subset_iff.mpr (mem 2 (by norm_num) hb)))
      simpa using this
    · have := Finset.card_le_card (Finset.insert_subset (mem 1 (by norm_num) ha)
        (Finset.singleton_subset_iff.mpr (mem 2 (by norm_num) hb)))
      simpa using this
  · intro i _
    rw [hval, hval, hmod, hmod]
    have : i.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have e1 : (i.val + 1) % 3 = (i.val % 3 + 1) % 3 := by omega
    have e2 : (i.val + 2) % 3 = (i.val % 3 + 2) % 3 := by omega
    rw [e1, e2]
    interval_cases i.val % 3
    · exact h12
    · simpa using h02.symm
    · exact h01

end Part1

section Part2
open Fin.NatCast Fin.CommRing

def rotf (k : ℕ) (hk : 0 < k) (n : ℕ) (word : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  word (ixf k hk (i.val + k - n % k))

def y0f (k : ℕ) (hk : 0 < k) (sp : ℕ) (name : Fin k → ZMod 2) (u : Fin k) : ZMod 2 :=
  name u + name (ixf k hk (u.val + sp)) + name (ixf k hk (u.val + k - sp % k))

def outF (k : ℕ) (hk : 0 < k) (spacing s t : ℕ) (name constant : Fin k → ZMod 2)
    (raw : Fin k → ZMod 2) (site : Fin k) : ZMod 2 :=
  let old := rotf k hk s raw + name
  let y := fun u : Fin k =>
    old u + old (ixf k hk (u.val+spacing)) + old (ixf k hk (u.val+k-spacing % k))
  y site + (1+y (ixf k hk (site.val+1)))*y (ixf k hk (site.val+2)) + rotf k hk t raw site + constant site

lemma y_eq (k : ℕ) (hk : 0 < k) (spacing s : ℕ) (name raw : Fin k → ZMod 2) (u : Fin k) :
    (rotf k hk s raw + name) u + (rotf k hk s raw + name) (ixf k hk (u.val+spacing)) +
      (rotf k hk s raw + name) (ixf k hk (u.val+k-spacing % k)) =
    Ymap k hk s spacing raw u + y0f k hk spacing name u := by
  simp only [Pi.add_apply, rotf, y0f, Ymap_apply]; ring

lemma outF_eq (k : ℕ) (hk : 0 < k) (spacing s t : ℕ) (name constant raw : Fin k → ZMod 2)
    (site : Fin k) :
    outF k hk spacing s t name constant raw site =
      (Ymap k hk s spacing raw (ixf k hk (site.val+1)) + y0f k hk spacing name (ixf k hk (site.val+1))) *
      (Ymap k hk s spacing raw (ixf k hk (site.val+2)) + y0f k hk spacing name (ixf k hk (site.val+2))) +
      (Ymap k hk s spacing raw site + y0f k hk spacing name site +
        Ymap k hk s spacing raw (ixf k hk (site.val+2)) + y0f k hk spacing name (ixf k hk (site.val+2)) +
        raw (ixf k hk (site.val + k - t % k)) + constant site) := by
  simp only [outF]
  rw [y_eq, y_eq, y_eq]
  simp only [rotf]
  ring

def predictF {k : ℕ} (tree : Finset (List Bool) × (List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) ×
      (List Bool → ZMod 2) × (List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) ×
      (List Bool → (Fin k → ZMod 2)))
    (raw : Fin k → ZMod 2) : Fin k → ZMod 2 :=
  tree.2.2.2.1 (walk tree.1 (fun p => decide (tree.2.1 p raw + tree.2.2.1 p ≠ 0)) tree.1.card) raw +
    tree.2.2.2.2 (walk tree.1 (fun p => decide (tree.2.1 p raw + tree.2.2.1 p ≠ 0)) tree.1.card)

def endsF {k : ℕ} (hk : 0 < k) (sites : Finset (Fin k)) : Finset (Fin k) :=
  sites.biUnion (fun i => ({ixf k hk (i.val+1), ixf k hk (i.val+2)} : Finset (Fin k)))

def savingF {k : ℕ} (hk : 0 < k) (sites : Finset (Fin k)) : ℕ :=
  if 3 ∣ k ∧ 2 ≤ ((Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 3 = r →
    j ∈ endsF hk sites)).card then 1 else 0

lemma pow_split (D d : ℕ) : 2 ^ (D - d) ≤ 2 ^ (D - (d+1)) + 2 ^ (D - (d+1)) := by
  by_cases h : D ≤ d
  · rw [Nat.sub_eq_zero_of_le h, Nat.sub_eq_zero_of_le (by omega)]; norm_num
  · rw [show D - d = (D - (d+1)) + 1 by omega, pow_succ]; omega

lemma tree_count {k : ℕ} (N : Finset (List Bool)) (q : (Fin k → ZMod 2) → List Bool → Bool)
    (ask : List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) (bias : List Bool → ZMod 2)
    (hq : ∀ x p, q x p = decide (ask p x + bias p ≠ 0)) (D : ℕ)
    (leafbound : ∀ (p : List Bool) (d : ℕ) (f : Fin d → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)
      (cst : Fin d → ZMod 2), (∃ x0, ∀ j, f j x0 = cst j) →
      (∀ x, (∀ j, f j x = cst j) → walk N (q x) N.card = p) → D ≤ d) :
    ∀ (m : ℕ) (p : List Bool), N.card - p.length = m →
      ∀ (d : ℕ) (f : Fin d → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) (cst : Fin d → ZMod 2),
      (∃ x0, ∀ j, f j x0 = cst j) → (∀ x, (∀ j, f j x = cst j) → p <+: walk N (q x) N.card) →
      2 ^ (D - d) ≤ ((Finset.univ.filter (fun x => ∀ j, f j x = cst j)).image
        (fun x => walk N (q x) N.card)).card := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro p hm d f cst hne hpre
  by_cases hp : p ∈ N ∧ p.length < N.card
  · have hnext : ∀ x, (∀ j, f j x = cst j) → p ++ [q x p] <+: walk N (q x) N.card := by
      intro x hx
      have hv := walk_valid N (q x) N.card
      have hpf := hpre x hx
      set w := walk N (q x) N.card
      have hwne : w ≠ p := by
        intro h; rw [h] at hv
        rcases hv.2.2.1 with h1 | h1
        · omega
        · exact h1 hp.1
      have hlt : p.length < w.length :=
        lt_of_le_of_ne hpf.length_le (fun h => hwne (hpf.eq_of_length h).symm)
      have htake : w.take p.length = p := (List.prefix_iff_eq_take.mp hpf).symm
      have hbit := hv.2.2.2 p.length hlt
      rw [htake] at hbit
      have : p ++ [q x p] = w.take (p.length + 1) := by
        rw [← List.take_concat_get' w p.length hlt, htake, hbit]
      rw [this]; exact List.take_prefix _ _
    let fb : Fin (d+1) → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 := Fin.cons (ask p) f
    let cb : Bool → Fin (d+1) → ZMod 2 := fun b => Fin.cons ((if b then 1 else 0) - bias p) cst
    have key : ∀ A B : ZMod 2, ∀ b : Bool, (A = (if b then 1 else 0) - B) ↔ decide (A + B ≠ 0) = b := by
      decide
    have hiff : ∀ x b, (∀ j, fb j x = cb b j) ↔ (∀ j, f j x = cst j) ∧ q x p = b := by
      intro x b
      simp only [Fin.forall_fin_succ, fb, cb, Fin.cons_zero, Fin.cons_succ, hq]
      rw [key]; tauto
    have hm' : N.card - (p ++ [true]).length < m ∧ N.card - (p ++ [false]).length < m := by
      simp only [List.length_append, List.length_singleton]; omega
    have hsub : ∀ b, ((Finset.univ.filter (fun x => ∀ j, fb j x = cb b j)).image
        (fun x => walk N (q x) N.card)) ⊆ ((Finset.univ.filter (fun x => ∀ j, f j x = cst j)).image
        (fun x => walk N (q x) N.card)) := by
      intro b w hw
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      obtain ⟨x, hx, rfl⟩ := hw
      exact ⟨x, ((hiff x b).mp hx).1, rfl⟩
    have hpb : ∀ b, ∀ x, (∀ j, fb j x = cb b j) → p ++ [b] <+: walk N (q x) N.card := by
      intro b x hx
      have := (hiff x b).mp hx
      rw [← this.2]; exact hnext x this.1
    by_cases ht : ∃ x, (∀ j, f j x = cst j) ∧ q x p = true
    · by_cases hf : ∃ x, (∀ j, f j x = cst j) ∧ q x p = false
      · have IT := ih _ hm'.1 (p ++ [true]) rfl (d+1) fb (cb true)
          (by obtain ⟨x, hx⟩ := ht; exact ⟨x, (hiff x true).mpr hx⟩) (hpb true)
        have IF := ih _ hm'.2 (p ++ [false]) rfl (d+1) fb (cb false)
          (by obtain ⟨x, hx⟩ := hf; exact ⟨x, (hiff x false).mpr hx⟩) (hpb false)
        have hdis : Disjoint ((Finset.univ.filter (fun x => ∀ j, fb j x = cb true j)).image
            (fun x => walk N (q x) N.card)) ((Finset.univ.filter (fun x => ∀ j, fb j x = cb false j)).image
            (fun x => walk N (q x) N.card)) := by
          rw [Finset.disjoint_left]
          intro w h1 h2
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          obtain ⟨x1, hx1, e1⟩ := h1
          obtain ⟨x2, hx2, e2⟩ := h2
          have p1 := hpb true x1 hx1
          have p2 := hpb false x2 hx2
          rw [e1] at p1; rw [e2] at p2
          have g1 := List.prefix_iff_eq_take.mp p1
          have g2 := List.prefix_iff_eq_take.mp p2
          simp only [List.length_append, List.length_singleton] at g1 g2
          rw [← g2] at g1
          simp at g1
        have := Finset.card_le_card (Finset.union_subset (hsub true) (hsub false))
        rw [Finset.card_union_of_disjoint hdis] at this
        exact (pow_split D d).trans (by omega)
      · push Not at hf
        have hall : ∀ x, (∀ j, f j x = cst j) → p ++ [true] <+: walk N (q x) N.card := by
          intro x hx
          have h1 := hnext x hx
          cases hqx : q x p
          · exact absurd hqx (hf x hx)
          · rw [hqx] at h1; exact h1
        exact ih _ hm'.1 (p ++ [true]) rfl d f cst hne hall
    · push Not at ht
      have hall : ∀ x, (∀ j, f j x = cst j) → p ++ [false] <+: walk N (q x) N.card := by
        intro x hx
        have h1 := hnext x hx
        cases hqx : q x p
        · rw [hqx] at h1; exact h1
        · exact absurd hqx (ht x hx)
      exact ih _ hm'.2 (p ++ [false]) rfl d f cst hne hall
  · have hall : ∀ x, (∀ j, f j x = cst j) → walk N (q x) N.card = p := by
      intro x hx
      by_contra hwne
      have hv := walk_valid N (q x) N.card
      have hpf := hpre x hx
      have hlt : p.length < (walk N (q x) N.card).length :=
        lt_of_le_of_ne hpf.length_le (fun h => hwne (hpf.eq_of_length h).symm)
      have htake : (walk N (q x) N.card).take p.length = p := (List.prefix_iff_eq_take.mp hpf).symm
      have hpN := hv.2.1 p.length hlt
      rw [htake] at hpN
      exact hp ⟨hpN, lt_of_lt_of_le hlt hv.1⟩
    have hD := leafbound p d f cst hne hall
    rw [Nat.sub_eq_zero_of_le hD, pow_zero, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero,
      Finset.image_eq_empty, Finset.filter_eq_empty_iff]
    push Not
    obtain ⟨x0, hx0⟩ := hne
    exact ⟨x0, Finset.mem_univ _, hx0⟩

end Part2

def Nset (D : ℕ) : Finset (List Bool) :=
  (Finset.range D).biUnion (fun n => Finset.univ.image (fun f : Fin n → Bool => List.ofFn f))

lemma mem_Nset {D : ℕ} {p : List Bool} : p ∈ Nset D ↔ p.length < D := by
  simp only [Nset, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨n, hn, f, rfl⟩; simpa using hn
  · intro h; exact ⟨p.length, h, fun i => p[i], List.ofFn_getElem⟩

lemma card_Nset (D : ℕ) : (Nset D).card = 2 ^ D - 1 := by
  induction D with
  | zero => simp [Nset]
  | succ D ih =>
    have hsplit : Nset (D+1) = Nset D ∪ Finset.univ.image (fun f : Fin D → Bool => List.ofFn f) := by
      ext p; simp only [Finset.mem_union, mem_Nset, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro h
        rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
        · exact Or.inl h
        · right; subst h; exact ⟨fun i => p[i], List.ofFn_getElem⟩
      · rintro (h | ⟨f, rfl⟩)
        · omega
        · simp
    have hdis : Disjoint (Nset D) (Finset.univ.image (fun f : Fin D → Bool => List.ofFn f)) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      rw [mem_Nset] at h1
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at h2
      obtain ⟨f, rfl⟩ := h2; simp at h1
    rw [hsplit, Finset.card_union_of_disjoint hdis, ih,
      Finset.card_image_of_injective _ List.ofFn_injective, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, pow_succ]
    have : 1 ≤ 2 ^ D := Nat.one_le_two_pow
    omega

lemma bit_val (Q : ZMod 2) : (if decide (Q ≠ 0) = true then (1 : ZMod 2) else 0) = Q := by
  revert Q; decide

lemma L1 : ∀ qa qb ya yb : ZMod 2, (qa ≠ 0 ∨ qb ≠ 0) →
    ya * yb = ((1 - qa) * qb * (qa * ya + qb * yb) + qa * qb * ((qa * ya + qb * yb) - 1)) * ya +
      qa * (1 - qb) * (qa * ya + qb * yb) * yb := by decide

lemma L2 : ∀ ya yb pa pb : ZMod 2, (ya + pa + 1) * (yb + pb + 1) ≠ 0 → ya = pa ∧ yb = pb := by decide

lemma L3 : ∀ qa qb : ZMod 2, (qa ≠ 0 ∨ qb ≠ 0) → qa * qa + qb * (1 - qa) = 1 := by decide

lemma two_zero (x : ZMod 2) : x + x = 0 := by revert x; decide

theorem upper_generic {k : ℕ} (hk : 0 < k) (yl : Fin k → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (yc : Fin k → ZMod 2) (Al : Fin k → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) (Ac : Fin k → ZMod 2)
    (a b : Fin k → Fin k) (qa qb : Fin k → ZMod 2) (sites : Finset (Fin k)) (T : List (Fin k))
    (hT : T.Nodup) (hTs : ∀ i ∈ T, i ∈ sites) (hq : ∀ i ∈ sites, qa i ≠ 0 ∨ qb i ≠ 0) (e : ℕ)
    (r0 : Fin k) (κ flag : ZMod 2)
    (hmode : (flag = 0 ∧ (sites.filter (· ∉ T)).card ≤ e) ∨
      (flag = 1 ∧ (sites.filter (· ∉ T)).card ≤ e + 1 ∧ r0 ∈ sites.filter (· ∉ T) ∧
        ∀ x, ∑ i ∈ sites, (qa i * (yl (a i) x + yc (a i)) + qb i * (yl (b i) x + yc (b i))) = κ))
    (out : (Fin k → ZMod 2) → Fin k → ZMod 2)
    (hout : ∀ x i, out x i = (yl (a i) x + yc (a i)) * (yl (b i) x + yc (b i)) + (Al i x + Ac i)) :
    ∃ tree : Finset (List Bool) × (List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) ×
      (List Bool → ZMod 2) × (List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) ×
      (List Bool → (Fin k → ZMod 2)),
      tree.1.card ≤ 2 ^ T.length - 1 ∧
      ∀ x, (sites.filter (fun i => predictF tree x i ≠ out x i)).card ≤ e := by
  classical
  set D := T.length
  let d0 : Fin k := ⟨0, hk⟩
  let tq : List Bool → Fin k := fun p => T.getD p.length d0
  let Qv : Fin k → (Fin k → ZMod 2) → ZMod 2 := fun i x =>
    qa i * (yl (a i) x + yc (a i)) + qb i * (yl (b i) x + yc (b i))
  let ask : List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 := fun p =>
    qa (tq p) • yl (a (tq p)) + qb (tq p) • yl (b (tq p))
  let bias : List Bool → ZMod 2 := fun p => qa (tq p) * yc (a (tq p)) + qb (tq p) * yc (b (tq p))
  let bitv : List Bool → ℕ → ZMod 2 := fun ℓ j => if ℓ.getD j false then 1 else 0
  let cpar : List Bool → ZMod 2 := fun ℓ => flag * (1 + κ + ∑ j ∈ Finset.range D, bitv ℓ j)
  let β : Fin k → List Bool → ZMod 2 := fun i ℓ => bitv ℓ (T.idxOf i)
  let pa : Fin k → List Bool → ZMod 2 := fun i ℓ => if i = r0 then cpar ℓ * qa i else 0
  let pb : Fin k → List Bool → ZMod 2 := fun i ℓ => if i = r0 then cpar ℓ * (1 - qa i) else 0
  let u : Fin k → List Bool → ZMod 2 := fun i ℓ => if i ∈ T then
    (1 - qa i) * qb i * β i ℓ + qa i * qb i * (β i ℓ - 1) else -(pb i ℓ + 1)
  let v : Fin k → List Bool → ZMod 2 := fun i ℓ => if i ∈ T then
    qa i * (1 - qb i) * β i ℓ else -(pa i ℓ + 1)
  let w : Fin k → List Bool → ZMod 2 := fun i ℓ => if i ∈ T then 0 else -(pa i ℓ + 1) * (pb i ℓ + 1)
  let aff : List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) := fun ℓ =>
    LinearMap.pi (fun i => Al i + u i ℓ • yl (a i) + v i ℓ • yl (b i))
  let cc : List Bool → Fin k → ZMod 2 := fun ℓ i =>
    Ac i + u i ℓ * yc (a i) + v i ℓ * yc (b i) + w i ℓ
  refine ⟨(Nset D, ask, bias, aff, cc), by simp [card_Nset], ?_⟩
  intro x

  let ℓx : List Bool := List.ofFn (fun j : Fin D => decide (Qv T[j] x ≠ 0))
  have hwalk : walk (Nset D) (fun p => decide (ask p x + bias p ≠ 0)) (Nset D).card = ℓx := by
    have hlen : ℓx.length = D := by simp [ℓx]
    rw [walk_eq_iff]
    · intro j hj
      rw [hlen] at hj
      have htq : tq (ℓx.take j) = T[j] := by
        simp only [tq, List.length_take, hlen, min_eq_left hj.le]
        exact List.getD_eq_getElem _ _ hj
      have hval : ask (ℓx.take j) x + bias (ℓx.take j) = Qv T[j] x := by
        simp only [ask, bias, htq, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, Qv]
        ring
      show decide (ask (ℓx.take j) x + bias (ℓx.take j) ≠ 0) = ℓx[j]
      rw [hval]
      simp only [ℓx, List.getElem_ofFn]
      rfl
    · refine ⟨?_, ?_, Or.inr ?_⟩
      · rw [hlen, card_Nset]; have := Nat.lt_two_pow_self (n := D); omega
      · intro j hj; rw [mem_Nset]; simp only [List.length_take]; omega
      · rw [mem_Nset, hlen]; omega
  have hpred : ∀ i, predictF (Nset D, ask, bias, aff, cc) x i =
      Al i x + Ac i + u i ℓx * (yl (a i) x + yc (a i)) + v i ℓx * (yl (b i) x + yc (b i)) + w i ℓx := by
    intro i
    simp only [predictF]
    rw [hwalk]
    simp only [aff, cc, Pi.add_apply, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul]
    ring
  have hbit : ∀ (j : ℕ) (hj : j < D), bitv ℓx j = Qv T[j] x := by
    intro j hj
    simp only [bitv, ℓx]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
    exact bit_val _

  have hsub : sites.filter (fun i => predictF (Nset D, ask, bias, aff, cc) x i ≠ out x i) ⊆
      sites.filter (· ∉ T) := by
    intro i hi
    simp only [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, fun hiT => hi.2 ?_⟩
    rw [hpred, hout]
    have hβ : β i ℓx = Qv i x := by
      have hidx : T.idxOf i < D := List.idxOf_lt_length_iff.mpr hiT
      simp only [β]; rw [hbit _ hidx, List.getElem_idxOf]
    simp only [u, v, w, hiT, ↓reduceIte, hβ, Qv]
    have := L1 (qa i) (qb i) (yl (a i) x + yc (a i)) (yl (b i) x + yc (b i)) (hq i hi.1)
    linear_combination (-1 : ZMod 2) * this
  have hwrong : ∀ i ∈ sites.filter (fun i => predictF (Nset D, ask, bias, aff, cc) x i ≠ out x i),
      yl (a i) x + yc (a i) = pa i ℓx ∧ yl (b i) x + yc (b i) = pb i ℓx := by
    intro i hi
    have hiT : i ∉ T := (Finset.mem_filter.mp (hsub hi)).2
    have hne := (Finset.mem_filter.mp hi).2
    rw [hpred, hout] at hne
    apply L2
    intro h0; apply hne
    simp only [u, v, w, hiT, ↓reduceIte] at h0 ⊢
    linear_combination (-1 : ZMod 2) * h0
  rcases hmode with ⟨_, hR⟩ | ⟨hflag, hR, hr0, hrel⟩
  · exact (Finset.card_le_card hsub).trans hR
  · by_contra hcon
    push Not at hcon
    have heq : sites.filter (fun i => predictF (Nset D, ask, bias, aff, cc) x i ≠ out x i) =
        sites.filter (· ∉ T) := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hall : ∀ i ∈ sites.filter (· ∉ T),
        yl (a i) x + yc (a i) = pa i ℓx ∧ yl (b i) x + yc (b i) = pb i ℓx := by
      rw [← heq]; exact hwrong
    have hsum := hrel x
    rw [← Finset.sum_filter_add_sum_filter_not sites (· ∈ T)] at hsum
    have hT1 : ∑ i ∈ sites.filter (· ∈ T), Qv i x = ∑ j ∈ Finset.range D, bitv ℓx j := by
      have hfs : sites.filter (· ∈ T) = T.toFinset := by
        ext i; simp only [Finset.mem_filter, List.mem_toFinset]
        exact ⟨fun h => h.2, fun h => ⟨hTs i h, h⟩⟩
      rw [hfs, List.sum_toFinset _ hT, ← Fin.sum_univ_eq_sum_range]
      rw [show (T.map (fun i => Qv i x)).sum = ∑ j : Fin D, Qv T[j] x by
        rw [← List.sum_ofFn]; congr 1; apply List.ext_getElem <;> simp [D]]
      exact Finset.sum_congr rfl (fun j _ => (hbit j j.2).symm)
    have hT2 : ∑ i ∈ sites.filter (fun i => ¬ i ∈ T), Qv i x = cpar ℓx := by
      rw [Finset.sum_eq_single r0]
      · have h := hall r0 hr0
        simp only [Qv, h.1, h.2, pa, pb, ↓reduceIte]
        have := L3 (qa r0) (qb r0) (hq r0 (Finset.mem_filter.mp hr0).1)
        linear_combination (cpar ℓx) * this
      · intro i hi hne
        have h := hall i hi
        simp only [Qv, h.1, h.2, pa, pb, hne, ↓reduceIte]; ring
      · intro h; exact absurd hr0 h
    simp only [Qv] at hT1 hT2
    rw [hT1, hT2] at hsum
    simp only [cpar, hflag, one_mul] at hsum
    have h2 := two_zero (∑ j ∈ Finset.range D, bitv ℓx j)
    have : (1 : ZMod 2) = 0 := by linear_combination hsum - h2
    exact one_ne_zero this

section Part3
open Fin.NatCast Fin.CommRing

lemma ab_facts (k : ℕ) (hk : 0 < k) (hk1 : 1 < k) (sites : Finset (Fin k))
    (hdisj : ∀ i ∈ sites, ixf k hk (i.val+1) ∉ sites) :
    (∀ i ∈ sites, ixf k hk (i.val+1) ≠ ixf k hk (i.val+2)) ∧
    PairsDisjoint sites (fun i => ixf k hk (i.val+1)) (fun i => ixf k hk (i.val+2)) := by
  haveI : NeZero k := ⟨hk.ne'⟩
  have h12 : ((1 : ℕ) : Fin k) ≠ ((2 : ℕ) : Fin k) := by
    intro h
    have h' : ((1 : ℕ) : Fin k) = 0 := by
      have : ((2 : ℕ) : Fin k) - ((1 : ℕ) : Fin k) = ((1 : ℕ) : Fin k) := by push_cast; ring
      rw [← h, sub_self] at this; exact this.symm
    rw [Fin.natCast_eq_zero] at h'
    exact absurd (Nat.le_of_dvd one_pos h') (by omega)
  refine ⟨fun i _ h => ?_, fun i hi i' hi' hne => ?_⟩
  · rw [ixf_add, ixf_add] at h; exact h12 (add_left_cancel h)
  · simp only [ixf_add]
    refine ⟨fun h => hne (add_right_cancel h), fun h => ?_, fun h => ?_, fun h => hne (add_right_cancel h)⟩
    · apply hdisj i' hi'
      have : i = i' + ((1 : ℕ) : Fin k) := by
        have : i = i' + ((2 : ℕ) : Fin k) - ((1 : ℕ) : Fin k) := by rw [← h]; ring
        rw [this]; push_cast; ring
      rw [ixf_add, ← this]; exact hi
    · apply hdisj i hi
      have : i' = i + ((1 : ℕ) : Fin k) := by
        have : i' = i + ((2 : ℕ) : Fin k) - ((1 : ℕ) : Fin k) := by rw [h]; ring
        rw [this]; push_cast; ring
      rw [ixf_add, ← this]; exact hi'

lemma lower (k : ℕ) (hk : 0 < k) (hk1 : 1 < k) (spacing s t : ℕ) (name constant : Fin k → ZMod 2)
    (sites : Finset (Fin k)) (e : ℕ) (hcop : Nat.Coprime k spacing)
    (hdisj : ∀ i ∈ sites, ixf k hk (i.val+1) ∉ sites)
    (tree : Finset (List Bool) × (List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) ×
      (List Bool → ZMod 2) × (List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) ×
      (List Bool → (Fin k → ZMod 2)))
    (herr : ∀ x, (sites.filter (fun i =>
      predictF tree x i ≠ outF k hk spacing s t name constant x i)).card ≤ e) :
    2 ^ (sites.card - e - savingF hk sites) ≤ tree.1.card + 1 := by
  classical
  haveI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨hab, hD⟩ := ab_facts k hk hk1 sites hdisj
  have hC : ∀ w : Fin k → ZMod 2,
      w ∈ supp (pairsOf sites (fun i => ixf k hk (i.val+1)) (fun i => ixf k hk (i.val+2))) →
      (∀ z, ∑ j, w j * Ymap k hk s spacing z j = 0) → w ≠ 0 →
      savingF hk sites = 1 ∧ ∀ i ∈ sites, w (ixf k hk (i.val+1)) ≠ 0 ∨ w (ixf k hk (i.val+2)) ≠ 0 := by
    intro w hw hz hw0
    obtain ⟨h1, h2⟩ := hC_spec hk hk1 s spacing hcop sites w (fun j hj => hw j hj) hz hw0
    exact ⟨by unfold savingF; rw [if_pos]; exact h1, h2⟩
  let q : (Fin k → ZMod 2) → List Bool → Bool := fun x p => decide (tree.2.1 p x + tree.2.2.1 p ≠ 0)
  have leafbound : ∀ (p : List Bool) (d : ℕ) (f : Fin d → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)
      (cst : Fin d → ZMod 2), (∃ x0, ∀ j, f j x0 = cst j) →
      (∀ x, (∀ j, f j x = cst j) → walk tree.1 (q x) tree.1.card = p) →
      sites.card - e - savingF hk sites ≤ d := by
    intro p d f cst hne hall
    obtain ⟨x0, hx0⟩ := hne
    let G : Fin k → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 := fun i =>
      (pr k i).comp (Ymap k hk s spacing) + (pr k (ixf k hk (i.val+2))).comp (Ymap k hk s spacing) +
        pr k (ixf k hk (i.val + k - t % k)) - (pr k i).comp (tree.2.2.2.1 p)
    let C : Fin k → ZMod 2 := fun i => y0f k hk spacing name i +
      y0f k hk spacing name (ixf k hk (i.val+2)) + constant i - tree.2.2.2.2 p i
    obtain ⟨x, hx, hcnt⟩ := core (Ymap k hk s spacing) (y0f k hk spacing name) sites
      (fun i => ixf k hk (i.val+1)) (fun i => ixf k hk (i.val+2)) hD hab (savingF hk sites) hC
      f cst x0 hx0 G C
    have hsub : sites.filter (fun i =>
        (Ymap k hk s spacing x (ixf k hk (i.val+1)) + y0f k hk spacing name (ixf k hk (i.val+1))) *
        (Ymap k hk s spacing x (ixf k hk (i.val+2)) + y0f k hk spacing name (ixf k hk (i.val+2))) +
        G i x + C i ≠ 0) ⊆
        sites.filter (fun i => predictF tree x i ≠ outF k hk spacing s t name constant x i) := by
      intro i hi
      simp only [Finset.mem_filter] at hi ⊢
      refine ⟨hi.1, fun heq => hi.2 ?_⟩
      have hw : walk tree.1 (q x) tree.1.card = p := hall x hx
      have hp : predictF tree x i = tree.2.2.2.1 p x i + tree.2.2.2.2 p i := by
        simp only [predictF]
        change (tree.2.2.2.1 (walk tree.1 (q x) tree.1.card) x +
          tree.2.2.2.2 (walk tree.1 (q x) tree.1.card)) i = _
        rw [hw]; rfl
      rw [hp, outF_eq] at heq
      simp only [G, C, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, pr,
        LinearMap.coe_proj, Function.eval]
      linear_combination (-1 : ZMod 2) * heq
    have := (Finset.card_le_card hsub).trans (herr x)
    omega
  have hcount := tree_count tree.1 q tree.2.1 tree.2.2.1 (fun _ _ => rfl)
    (sites.card - e - savingF hk sites) leafbound tree.1.card [] (by simp) 0 (fun j => j.elim0)
    (fun j => j.elim0) ⟨0, fun j => j.elim0⟩ (fun x _ => List.nil_prefix)
  have hr := card_reached tree.1 q
  have hfu : (Finset.univ.filter (fun x : Fin k → ZMod 2 => ∀ j : Fin 0,
      (fun j : Fin 0 => j.elim0 : Fin 0 → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) j x =
      (fun j : Fin 0 => j.elim0 : Fin 0 → ZMod 2) j)) = Finset.univ := by
    ext x; simp
  rw [hfu, Nat.sub_zero] at hcount
  exact hcount.trans hr

lemma sum_Ymap {k : ℕ} [NeZero k] (hk : 0 < k) (s sp : ℕ) (w z : Fin k → ZMod 2) :
    ∑ j, w j * Ymap k hk s sp z j =
      ∑ i, z i * (w (i + s) + w (i + s - sp) + w (i + s + sp)) := by
  have e : ∀ c : Fin k, ∑ j, w j * z (j + c) = ∑ i, w (i - c) * z i := fun c => sum_shift w z c
  simp only [Ymap_apply', mul_add, Finset.sum_add_distrib]
  have h1 : ∑ j, w j * z (j - s) = ∑ i, w (i + s) * z i := by
    rw [show (fun j => w j * z (j - (s : Fin k))) = fun j => w j * z (j + -(s : Fin k)) by
      funext j; rw [sub_eq_add_neg], e]; simp
  have h2 : ∑ j, w j * z (j + sp - s) = ∑ i, w (i + s - sp) * z i := by
    rw [show (fun j => w j * z (j + (sp : Fin k) - s)) = fun j => w j * z (j + ((sp : Fin k) - s)) by
      funext j; rw [add_sub_assoc], e]
    exact Finset.sum_congr rfl (fun i _ => by congr 2; abel)
  have h3 : ∑ j, w j * z (j - sp - s) = ∑ i, w (i + s + sp) * z i := by
    rw [show (fun j => w j * z (j - (sp : Fin k) - s)) = fun j => w j * z (j + (-(sp : Fin k) - s)) by
      funext j; congr 2; abel, e]
    exact Finset.sum_congr rfl (fun i _ => by congr 2; abel)
  rw [h1, h2, h3]
  simp only [mul_comm (z _)]

lemma ind_three : ∀ c1 s3 r1 r2 : Fin 3, s3 ≠ 0 → r1 ≠ r2 →
    ((if (c1 + s3) = r1 ∨ (c1 + s3) = r2 then 1 else 0 : ZMod 2) +
     (if c1 = r1 ∨ c1 = r2 then 1 else 0) +
     (if (c1 + s3 + s3) = r1 ∨ (c1 + s3 + s3) = r2 then 1 else 0)) = 0 := by decide

lemma bracket {k : ℕ} [NeZero k] (h3 : 3 ∣ k) (sp : ℕ) (hsp : ¬ 3 ∣ sp) (r1 r2 : ℕ) (hr1 : r1 < 3)
    (hr2 : r2 < 3) (hne : r1 ≠ r2) (u : Fin k) :
    (fun j : Fin k => if j.val % 3 = r1 ∨ j.val % 3 = r2 then (1 : ZMod 2) else 0) u +
    (fun j : Fin k => if j.val % 3 = r1 ∨ j.val % 3 = r2 then (1 : ZMod 2) else 0) (u - sp) +
    (fun j : Fin k => if j.val % 3 = r1 ∨ j.val % 3 = r2 then (1 : ZMod 2) else 0) (u + sp) = 0 := by
  have cls_add : ∀ x y : Fin k, (x + y).val % 3 = (x.val % 3 + y.val % 3) % 3 := by
    intro x y; rw [Fin.val_add, Nat.mod_mod_of_dvd _ h3, Nat.add_mod]
  have csp : (sp : Fin k).val % 3 = sp % 3 := by rw [Fin.val_natCast, Nat.mod_mod_of_dvd _ h3]
  have e0 : u.val % 3 = ((u - sp).val % 3 + sp % 3) % 3 := by
    rw [← csp, ← cls_add, sub_add_cancel]
  have e2 : (u + sp).val % 3 = ((u - sp).val % 3 + sp % 3 + sp % 3) % 3 := by
    rw [cls_add, csp, e0]; omega
  simp only
  rw [e0, e2]
  have hc1 : (u - sp).val % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hs3 : sp % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hs0 : sp % 3 ≠ 0 := fun h => hsp (Nat.dvd_of_mod_eq_zero h)
  generalize (u - sp).val % 3 = c at *
  generalize sp % 3 = s3 at *
  interval_cases c <;> interval_cases s3 <;> interval_cases r1 <;> interval_cases r2 <;>
    first | omega | decide

lemma upper_one (k : ℕ) (hk : 0 < k) (hk1 : k = 1) (spacing s t : ℕ) (name constant : Fin k → ZMod 2)
    (sites : Finset (Fin k)) (e L : ℕ) (hL : 1 ≤ L) :
    ∃ tree : Finset (List Bool) × (List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) ×
      (List Bool → ZMod 2) × (List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) ×
      (List Bool → (Fin k → ZMod 2)), tree.1.card < L ∧ ∀ x : Fin k → ZMod 2,
      (sites.filter (fun i => predictF tree x i ≠ outF k hk spacing s t name constant x i)).card ≤ e := by
  subst hk1
  let aff : List Bool → (Fin 1 → ZMod 2) →ₗ[ZMod 2] (Fin 1 → ZMod 2) := fun _ =>
    LinearMap.pi (fun i => (pr 1 i).comp (Ymap 1 hk s spacing) + pr 1 (ixf 1 hk (i.val + 1 - t % 1)))
  let cc : List Bool → Fin 1 → ZMod 2 := fun _ i => y0f 1 hk spacing name i + constant i
  refine ⟨(∅, fun _ => 0, fun _ => 0, aff, cc), by simp; omega, fun x => ?_⟩
  have hsq : ∀ z : ZMod 2, z * z + z + z = z := by decide
  have : sites.filter (fun i => predictF (∅, fun _ => 0, fun _ => 0, aff, cc) x i ≠
      outF 1 hk spacing s t name constant x i) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i _ hne; apply hne
    have ha : ixf 1 hk (i.val+1) = i := Subsingleton.elim _ _
    have hb : ixf 1 hk (i.val+2) = i := Subsingleton.elim _ _
    rw [outF_eq, ha, hb]
    simp only [predictF, aff, cc, Pi.add_apply, LinearMap.pi_apply, LinearMap.add_apply,
      LinearMap.comp_apply, pr, LinearMap.coe_proj, Function.eval]
    have := hsq (Ymap 1 hk s spacing x i + y0f 1 hk spacing name i)
    linear_combination (-1 : ZMod 2) * this
  rw [this]; simp

lemma upper_main (k : ℕ) (hk : 0 < k) (hk1 : 1 < k) (spacing s t : ℕ) (name constant : Fin k → ZMod 2)
    (sites : Finset (Fin k)) (e L : ℕ) (hcop : Nat.Coprime k spacing)
    (hdisj : ∀ i ∈ sites, ixf k hk (i.val+1) ∉ sites)
    (hL : 2 ^ (sites.card - e - savingF hk sites) ≤ L) :
    ∃ tree : Finset (List Bool) × (List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) ×
      (List Bool → ZMod 2) × (List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) ×
      (List Bool → (Fin k → ZMod 2)), tree.1.card < L ∧ ∀ x : Fin k → ZMod 2,
      (sites.filter (fun i => predictF tree x i ≠ outF k hk spacing s t name constant x i)).card ≤ e := by
  classical
  haveI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨hab, hD⟩ := ab_facts k hk hk1 sites hdisj
  set Dn := sites.card - e - savingF hk sites with hDn
  let T : List (Fin k) := sites.toList.take Dn
  have hT : T.Nodup := (Finset.nodup_toList sites).sublist (List.take_sublist _ _)
  have hTs : ∀ i ∈ T, i ∈ sites := fun i hi => Finset.mem_toList.mp (List.mem_of_mem_take hi)
  have hTlen : T.length = Dn := by
    simp only [T, List.length_take, Finset.length_toList]; omega
  have hRcard : (sites.filter (· ∉ T)).card = sites.card - Dn := by
    have h1 := Finset.card_filter_add_card_filter_not (s := sites) (fun i => i ∈ T)
    have h2 : sites.filter (fun i => i ∈ T) = T.toFinset := by
      ext i; simp only [Finset.mem_filter, List.mem_toFinset]
      exact ⟨fun h => h.2, fun h => ⟨hTs i h, h⟩⟩
    rw [h2, List.toFinset_card_of_nodup hT, hTlen] at h1
    have : Dn ≤ sites.card := by omega
    omega
  let a : Fin k → Fin k := fun i => ixf k hk (i.val+1)
  let b : Fin k → Fin k := fun i => ixf k hk (i.val+2)
  let yl : Fin k → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 := fun j => (pr k j).comp (Ymap k hk s spacing)
  let yc : Fin k → ZMod 2 := y0f k hk spacing name
  let Al : Fin k → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 := fun i =>
    (pr k i).comp (Ymap k hk s spacing) + (pr k (b i)).comp (Ymap k hk s spacing) +
      pr k (ixf k hk (i.val + k - t % k))
  let Ac : Fin k → ZMod 2 := fun i =>
    y0f k hk spacing name i + y0f k hk spacing name (b i) + constant i
  have hout : ∀ x i, outF k hk spacing s t name constant x i =
      (yl (a i) x + yc (a i)) * (yl (b i) x + yc (b i)) + (Al i x + Ac i) := by
    intro x i; rw [outF_eq]
    simp only [yl, yc, Al, Ac, a, b, LinearMap.add_apply, LinearMap.comp_apply, pr,
      LinearMap.coe_proj, Function.eval]
    ring
  have finish : ∀ (qa qb : Fin k → ZMod 2) (r0 : Fin k) (κ flag : ZMod 2),
      (∀ i ∈ sites, qa i ≠ 0 ∨ qb i ≠ 0) →
      ((flag = 0 ∧ (sites.filter (· ∉ T)).card ≤ e) ∨
        (flag = 1 ∧ (sites.filter (· ∉ T)).card ≤ e + 1 ∧ r0 ∈ sites.filter (· ∉ T) ∧
          ∀ x, ∑ i ∈ sites, (qa i * (yl (a i) x + yc (a i)) + qb i * (yl (b i) x + yc (b i))) = κ)) →
      ∃ tree : Finset (List Bool) × (List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) ×
        (List Bool → ZMod 2) × (List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) ×
        (List Bool → (Fin k → ZMod 2)), tree.1.card < L ∧ ∀ x : Fin k → ZMod 2,
        (sites.filter (fun i => predictF tree x i ≠ outF k hk spacing s t name constant x i)).card ≤ e := by
    intro qa qb r0 κ flag hq hmode
    obtain ⟨tree, hcard, herr⟩ := upper_generic hk yl yc Al Ac a b qa qb sites T hT hTs hq e r0 κ flag
      hmode _ hout
    refine ⟨tree, ?_, herr⟩
    rw [hTlen] at hcard
    have : 1 ≤ 2 ^ Dn := Nat.one_le_two_pow
    omega
  by_cases hsav : savingF hk sites = 1
  · have hsav' := hsav
    unfold savingF at hsav'
    split_ifs at hsav' with hc
    · obtain ⟨h3, hcov⟩ := hc
      obtain ⟨r1, hr1, r2, hr2, hne⟩ := Finset.one_lt_card.mp (by omega :
        1 < ((Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 3 = r → j ∈ endsF hk sites)).card)
      simp only [Finset.mem_filter, Finset.mem_range] at hr1 hr2
      let Sset : Finset (Fin k) := Finset.univ.filter (fun j => j.val % 3 = r1 ∨ j.val % 3 = r2)
      let qa : Fin k → ZMod 2 := fun i => if a i ∈ Sset then 1 else 0
      let qb : Fin k → ZMod 2 := fun i => if b i ∈ Sset then 1 else 0
      have hmod : ∀ n : ℕ, (ixf k hk n).val % 3 = n % 3 := fun n => by
        simp [ixf, Nat.mod_mod_of_dvd _ h3]
      have hq : ∀ i ∈ sites, qa i ≠ 0 ∨ qb i ≠ 0 := by
        intro i _
        simp only [qa, qb, Sset, a, b, Finset.mem_filter, Finset.mem_univ, true_and, hmod]
        have : (i.val+1) % 3 = r1 ∨ (i.val+1) % 3 = r2 ∨ (i.val+2) % 3 = r1 ∨ (i.val+2) % 3 = r2 := by
          omega
        rcases this with h | h | h | h <;> simp [h]
      by_cases hme : sites.card ≤ e
      · exact finish qa qb ⟨0, hk⟩ 0 0 hq (Or.inl ⟨rfl, by rw [hRcard]; omega⟩)
      · have hR : (sites.filter (· ∉ T)).card = e + 1 := by rw [hRcard]; omega
        obtain ⟨r0, hr0⟩ : (sites.filter (· ∉ T)).Nonempty := by
          rw [← Finset.card_pos, hR]; omega
        refine finish qa qb r0 (∑ j ∈ Sset, y0f k hk spacing name j) 1 hq
          (Or.inr ⟨rfl, by omega, hr0, ?_⟩)
        intro x
        have hSsub : Sset ⊆ endsF hk sites := by
          intro j hj
          simp only [Sset, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rcases hj with h | h
          · exact hr1.2 j h
          · exact hr2.2 j h
        have step : ∑ i ∈ sites, (qa i * (yl (a i) x + yc (a i)) + qb i * (yl (b i) x + yc (b i))) =
            ∑ j ∈ Sset, (yl j x + yc j) := by
          have e1 : ∀ i ∈ sites, qa i * (yl (a i) x + yc (a i)) + qb i * (yl (b i) x + yc (b i)) =
              ∑ j ∈ ({a i, b i} : Finset (Fin k)), (if j ∈ Sset then yl j x + yc j else 0) := by
            intro i hi; rw [Finset.sum_pair (hab i hi)]; simp only [qa, qb]; split_ifs <;> ring
          rw [Finset.sum_congr rfl e1, ← Finset.sum_biUnion]
          · rw [← Finset.sum_filter]
            congr 1
            ext j; simp only [Finset.mem_filter]
            exact ⟨fun h => h.2, fun h => ⟨hSsub h, h⟩⟩
          · intro i hi i' hi' hne
            obtain ⟨g1, g2, g3, g4⟩ := hD i hi i' hi' hne
            rw [Function.onFun, Finset.disjoint_left]
            intro j hj hj'
            simp only [Finset.mem_insert, Finset.mem_singleton] at hj hj'
            rcases hj with rfl | rfl <;> rcases hj' with h | h
            · exact g1 h
            · exact g2 h
            · exact g3 h
            · exact g4 h
        rw [step, Finset.sum_add_distrib]
        have hsp : ¬ 3 ∣ spacing := by
          intro hd
          have := Nat.Coprime.coprime_dvd_left h3 hcop
          exact absurd (Nat.Coprime.coprime_dvd_right hd this) (by decide)
        have hz : ∑ j ∈ Sset, yl j x = 0 := by
          have : ∑ j ∈ Sset, yl j x = ∑ j, (fun j : Fin k =>
              if j.val % 3 = r1 ∨ j.val % 3 = r2 then (1 : ZMod 2) else 0) j * Ymap k hk s spacing x j := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            simp only [yl, LinearMap.comp_apply, pr, LinearMap.coe_proj, Function.eval]
            split_ifs <;> ring
          rw [this, sum_Ymap]
          apply Finset.sum_eq_zero
          intro i _
          rw [bracket h3 spacing hsp r1 r2 hr1.1 hr2.1 hne (i + s), mul_zero]
        rw [hz, zero_add]
  · have hs0 : savingF hk sites = 0 := by
      unfold savingF at hsav ⊢; split_ifs at hsav ⊢ <;> simp_all
    exact finish (fun _ => 1) (fun _ => 0) ⟨0, hk⟩ 0 0 (fun _ _ => Or.inl one_ne_zero)
      (Or.inl ⟨rfl, by rw [hRcard]; omega⟩)

lemma main_iff (k : ℕ) (hk : 0 < k) (spacing s t : ℕ) (name constant : Fin k → ZMod 2)
    (sites : Finset (Fin k)) (e L : ℕ) (hcop : Nat.Coprime k spacing)
    (hdisj : 1 < k → ∀ i ∈ sites, ixf k hk (i.val+1) ∉ sites) :
    (∃ tree : Finset (List Bool) × (List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) ×
      (List Bool → ZMod 2) × (List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) ×
      (List Bool → (Fin k → ZMod 2)), tree.1.card < L ∧ ∀ x : Fin k → ZMod 2,
      (sites.filter (fun i => predictF tree x i ≠ outF k hk spacing s t name constant x i)).card ≤ e) ↔
    (if k = 1 then 1 else 2^(sites.card - e - savingF hk sites)) ≤ L := by
  constructor
  · rintro ⟨tree, hcard, herr⟩
    split_ifs with hk1
    · omega
    · have := lower k hk (by omega) spacing s t name constant sites e hcop (hdisj (by omega)) tree herr
      omega
  · intro hL
    split_ifs at hL with hk1
    · exact upper_one k hk hk1 spacing s t name constant sites e L hL
    · exact upper_main k hk (by omega) spacing s t name constant sites e L hcop (hdisj (by omega)) hL

end Part3

end PEqualNP.Outside.L_meta_33614

theorem PEqualNP.Outside.L_meta_33614 : (∀ (k : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (n : Nat) (word : W) (i : Fin k) => word (ix (i.val+k-n % k))
  ∀ (spacing s t : Nat) (name constant : W),
    let out := fun (raw : W) (site : Fin k) =>
      let old := rot s raw + name
      let y := fun u : Fin k =>
        old u + old (ix (u.val+spacing)) + old (ix (u.val+k-spacing % k))
      y site + (1+y (ix (site.val+1)))*y (ix (site.val+2)) + rot t raw site + constant site
    let H := List Bool
    let Tree := Finset H × (H → W →ₗ[F] F) × (H → F) × (H → W →ₗ[F] W) × (H → W)
    let predict : Tree → W → W := fun tree raw =>
      let nodes := tree.1
      let ask := tree.2.1
      let bias := tree.2.2.1
      let aff := tree.2.2.2.1
      let c := tree.2.2.2.2
      let leaf := (List.range nodes.card).foldl (fun (p : H) _ =>
        if p ∈ nodes then p ++ [decide (ask p raw + bias p ≠ 0)] else p) []
      aff leaf raw + c leaf
    ∀ (sites : Finset (Fin k)) (e L : Nat), Nat.Coprime k spacing →
      (1 < k → ∀ i ∈ sites, ix (i.val+1) ∉ sites) →
      let ends := sites.biUnion (fun i => ({ix (i.val+1), ix (i.val+2)} : Finset (Fin k)))
      let covered := (Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 3 = r → j ∈ ends)
      let saving := if 3 ∣ k ∧ 2 ≤ covered.card then 1 else 0
      let price := if k = 1 then 1 else 2^(sites.card-e-saving)
      (∃ tree : Tree, tree.1.card < L ∧ ∀ x : W,
        (sites.filter (fun i => predict tree x i ≠ out x i)).card ≤ e) ↔ price ≤ L) := by
  intro k hk F W ix rot spacing s t name constant out H Tree predict sites e L hcop hdisj ends covered saving price
  exact PEqualNP.Outside.L_meta_33614.main_iff k hk spacing s t name constant sites e L hcop hdisj
