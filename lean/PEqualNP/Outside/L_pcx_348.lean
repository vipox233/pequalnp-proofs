import Mathlib.Data.Nat.Log
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_348

section Half1

open PEqualNP.Expanders

section GraphBasics

variable {m n : ℕ} {G : BipGraph m n}

abbrev Vert (m n : ℕ) : Type := Fin m ⊕ Fin n

def endL (e : GEdge G) : Vert m n := Sum.inl e.1.1
def endR (e : GEdge G) : Vert m n := Sum.inr e.1.2

lemma endL_ne_endR (e : GEdge G) : endL e ≠ endR e := by
  simp [endL, endR]

def verts (s : Finset (GEdge G)) : Finset (Vert m n) :=
  s.image endL ∪ s.image endR

lemma verts_card (s : Finset (GEdge G)) :
    (verts s).card = (s.image (fun e => e.1.1)).card + (s.image (fun e => e.1.2)).card := by
  have hdisj : Disjoint (s.image endL) (s.image endR) := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    rcases Finset.mem_image.mp hv1 with ⟨a, _, rfl⟩
    rcases Finset.mem_image.mp hv2 with ⟨b, _, hb⟩
    exact endL_ne_endR a (by simpa [endL, endR] using hb.symm)
  rw [verts, Finset.card_union_of_disjoint hdisj]
  have hL : s.image endL = (s.image (fun e => e.1.1)).image Sum.inl := by
    rw [Finset.image_image]; rfl
  have hR : s.image endR = (s.image (fun e => e.1.2)).image Sum.inr := by
    rw [Finset.image_image]; rfl
  rw [hL, hR, Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective]

lemma verts_empty : verts (∅ : Finset (GEdge G)) = ∅ := by
  simp [verts]

lemma verts_union (A B : Finset (GEdge G)) : verts (A ∪ B) = verts A ∪ verts B := by
  simp only [verts, Finset.image_union]
  ac_rfl

lemma verts_mono {A B : Finset (GEdge G)} (h : A ⊆ B) : verts A ⊆ verts B := by
  intro v hv
  simp only [verts, Finset.mem_union, Finset.mem_image] at hv ⊢
  rcases hv with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
  · exact Or.inl ⟨e, h he, rfl⟩
  · exact Or.inr ⟨e, h he, rfl⟩

lemma verts_inter_subset (A B : Finset (GEdge G)) : verts (A ∩ B) ⊆ verts A ∩ verts B :=
  Finset.subset_inter (verts_mono Finset.inter_subset_left) (verts_mono Finset.inter_subset_right)

def dense (s : Finset (GEdge G)) : Prop :=
  (verts s).card < s.card

lemma dense_iff (s : Finset (GEdge G)) :
    dense s ↔ (s.image (fun e => e.1.1)).card + (s.image (fun e => e.1.2)).card < s.card := by
  rw [dense, verts_card]

def ex (s : Finset (GEdge G)) : ℤ :=
  (s.card : ℤ) - ((verts s).card : ℤ)

lemma ex_empty : ex (∅ : Finset (GEdge G)) = 0 := by
  simp [ex, verts_empty]

lemma ex_supermod (A B : Finset (GEdge G)) :
    ex A + ex B ≤ ex (A ∪ B) + ex (A ∩ B) := by
  have he : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  have hv1 : (verts (A ∩ B)).card ≤ (verts A ∩ verts B).card :=
    Finset.card_le_card (verts_inter_subset A B)
  have hv2 : (verts (A ∪ B)).card + (verts A ∩ verts B).card = (verts A).card + (verts B).card := by
    rw [verts_union]
    exact Finset.card_union_add_card_inter (verts A) (verts B)
  simp only [ex]
  omega

def maxEx (F : Finset (GEdge G)) : ℕ :=
  F.powerset.sup (fun s => s.card - (verts s).card)

lemma sub_le_maxEx {F s : Finset (GEdge G)} (hs : s ⊆ F) :
    s.card - (verts s).card ≤ maxEx F :=
  Finset.le_sup (f := fun t => t.card - (verts t).card) (Finset.mem_powerset.mpr hs)

lemma ex_le_maxEx {F s : Finset (GEdge G)} (hs : s ⊆ F) :
    ex s ≤ (maxEx F : ℤ) := by
  have h := sub_le_maxEx hs
  simp only [ex]
  omega

lemma exists_maxEx_witness (F : Finset (GEdge G)) :
    ∃ s ⊆ F, s.card - (verts s).card = maxEx F := by
  have hne : F.powerset.Nonempty := ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset F)⟩
  rcases Finset.exists_mem_eq_sup F.powerset hne (fun s => s.card - (verts s).card) with ⟨s, hs, hval⟩
  exact ⟨s, Finset.mem_powerset.mp hs, hval.symm⟩

lemma maxEx_eq_zero_iff (F : Finset (GEdge G)) :
    maxEx F = 0 ↔ ∀ s ⊆ F, ¬ dense s := by
  constructor
  · intro h0 s hs hden
    have hle := sub_le_maxEx hs
    rw [h0] at hle
    unfold dense at hden
    omega
  · intro hall
    rcases exists_maxEx_witness F with ⟨s, hs, hval⟩
    have hnd := hall s hs
    unfold dense at hnd
    omega

lemma maxEx_mono {F₁ F₂ : Finset (GEdge G)} (h : F₁ ⊆ F₂) : maxEx F₁ ≤ maxEx F₂ := by
  rcases exists_maxEx_witness F₁ with ⟨s, hs, hval⟩
  rw [← hval]
  exact sub_le_maxEx (hs.trans h)

lemma exists_min_maximizer (F : Finset (GEdge G)) (hpos : 0 < maxEx F) :
    ∃ S ⊆ F,
      ex S = (maxEx F : ℤ) ∧
      (∀ t ⊆ F, ex t = (maxEx F : ℤ) → S ⊆ t) ∧
      (∀ A ⊂ S, ex A < ex S) := by
  let M : Finset (Finset (GEdge G)) :=
    F.powerset.filter (fun s => s.card - (verts s).card = maxEx F)
  have hMne : M.Nonempty := by
    rcases exists_maxEx_witness F with ⟨s, hs, hval⟩
    exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs, hval⟩⟩
  rcases Finset.exists_min_image M Finset.card hMne with ⟨S, hSM, hSmin⟩
  rcases Finset.mem_filter.mp hSM with ⟨hSp, hSval⟩
  have hSF : S ⊆ F := Finset.mem_powerset.mp hSp
  have hSex : ex S = (maxEx F : ℤ) := by
    simp only [ex]; omega
  have hSub : ∀ t ⊆ F, ex t = (maxEx F : ℤ) → S ⊆ t := by
    intro t htF htex
    have hsup := ex_supermod S t
    have hU : ex (S ∪ t) ≤ (maxEx F : ℤ) := ex_le_maxEx (Finset.union_subset hSF htF)
    have hI : ex (S ∩ t) ≤ (maxEx F : ℤ) :=
      ex_le_maxEx (Finset.inter_subset_left.trans hSF)
    have hIeq : ex (S ∩ t) = (maxEx F : ℤ) := by omega
    have hIM : S ∩ t ∈ M := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.inter_subset_left.trans hSF), ?_⟩
      simp only [ex] at hIeq
      omega
    have hcard : S.card ≤ (S ∩ t).card := hSmin (S ∩ t) hIM
    exact Finset.eq_of_subset_of_card_le Finset.inter_subset_left hcard ▸ Finset.inter_subset_right
  refine ⟨S, hSF, hSex, hSub, ?_⟩
  intro A hAS
  have hAF : A ⊆ F := hAS.1.trans hSF
  have hAle : ex A ≤ (maxEx F : ℤ) := ex_le_maxEx hAF
  by_contra hge
  have hAeq : ex A = (maxEx F : ℤ) := by omega
  have hSA : S ⊆ A := hSub A hAF hAeq
  exact hAS.2 hSA

lemma hitting_le_maxEx : ∀ (d : ℕ) (F : Finset (GEdge G)),
    maxEx F ≤ d →
    ∃ Z ⊆ F, Z.card ≤ d ∧ ∀ s ⊆ F, Disjoint s Z → ¬ dense s := by
  intro d
  induction d with
  | zero =>
    intro F hle
    have h0 : maxEx F = 0 := by omega
    refine ⟨∅, Finset.empty_subset F, by simp, ?_⟩
    intro s hs _
    exact (maxEx_eq_zero_iff F).mp h0 s hs
  | succ d ih =>
    intro F hle
    by_cases h0 : maxEx F = 0
    · refine ⟨∅, Finset.empty_subset F, by simp, ?_⟩
      intro s hs _
      exact (maxEx_eq_zero_iff F).mp h0 s hs
    · rcases exists_min_maximizer F (by omega) with ⟨S, hSF, hSex, hSub, _⟩
      have hSne : S.Nonempty := by
        by_contra hEmpty
        rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
        subst hEmpty
        rw [ex_empty] at hSex
        omega
      rcases hSne with ⟨e, heS⟩
      have hlt : maxEx (F.erase e) < maxEx F := by
        rcases exists_maxEx_witness (F.erase e) with ⟨t, ht, hval⟩
        have htF : t ⊆ F := ht.trans (Finset.erase_subset e F)
        have hle' : maxEx (F.erase e) ≤ maxEx F := maxEx_mono (Finset.erase_subset e F)
        by_contra hge
        have heq : maxEx (F.erase e) = maxEx F := by omega
        have htex : ex t = (maxEx F : ℤ) := by
          simp only [ex]; omega
        have heT : e ∈ t := hSub t htF htex heS
        exact (Finset.notMem_erase e F) (ht heT)
      rcases ih (F.erase e) (by omega) with ⟨Z', hZ'sub, hZ'card, hZ'hit⟩
      refine ⟨insert e Z', Finset.insert_subset (hSF heS) (hZ'sub.trans (Finset.erase_subset e F)), ?_, ?_⟩
      · have := Finset.card_insert_le e Z'
        omega
      · intro s hsF hdisj
        have hne : e ∉ s := fun he => Finset.disjoint_left.mp hdisj he (Finset.mem_insert_self e Z')
        have hsEr : s ⊆ F.erase e := by
          intro x hx
          exact Finset.mem_erase.mpr ⟨fun h => hne (h ▸ hx), hsF hx⟩
        have hdisj' : Disjoint s Z' :=
          Finset.disjoint_of_subset_right (Finset.subset_insert e Z') hdisj
        exact hZ'hit s hsEr hdisj'

def inc (S : Finset (GEdge G)) (v : Vert m n) : Finset (GEdge G) :=
  S.filter (fun e => endL e = v ∨ endR e = v)

def deg (S : Finset (GEdge G)) (v : Vert m n) : ℕ :=
  (inc S v).card

lemma mem_verts_iff_inc_nonempty (S : Finset (GEdge G)) (v : Vert m n) :
    v ∈ verts S ↔ (inc S v).Nonempty := by
  simp only [verts, inc, Finset.mem_union, Finset.mem_image, Finset.Nonempty, Finset.mem_filter]
  constructor
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact ⟨e, he, Or.inl rfl⟩
    · exact ⟨e, he, Or.inr rfl⟩
  · rintro ⟨e, he, h | h⟩
    · exact Or.inl ⟨e, he, h⟩
    · exact Or.inr ⟨e, he, h⟩

lemma mem_verts_iff_deg_pos (S : Finset (GEdge G)) (v : Vert m n) :
    v ∈ verts S ↔ 0 < deg S v := by
  rw [mem_verts_iff_inc_nonempty, deg, Finset.card_pos]

lemma sum_deg (S : Finset (GEdge G)) :
    ∑ v ∈ verts S, deg S v = 2 * S.card := by
  have h1 : ∑ v ∈ verts S, deg S v =
      ∑ v ∈ verts S, ∑ e ∈ S, if (endL e = v ∨ endR e = v) then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro v _
    rw [deg, inc, Finset.card_filter]
  rw [h1, Finset.sum_comm]
  have h2 : ∀ e ∈ S, (∑ v ∈ verts S, if (endL e = v ∨ endR e = v) then 1 else 0) = 2 := by
    intro e he
    have hL : endL e ∈ verts S := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    have hR : endR e ∈ verts S := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    have hfil : (verts S).filter (fun v => endL e = v ∨ endR e = v) = {endL e, endR e} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_, rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨hL, Or.inl rfl⟩
        · exact ⟨hR, Or.inr rfl⟩
    rw [← Finset.card_filter, hfil, Finset.card_pair (endL_ne_endR e)]
  rw [Finset.sum_congr rfl h2]
  simp [Nat.mul_comm]

lemma min_deg_ge_two_of_min {S : Finset (GEdge G)} (hMin : ∀ A ⊂ S, ex A < ex S) :
    ∀ v ∈ verts S, 2 ≤ deg S v := by
  intro v hv
  have hpos : 0 < deg S v := (mem_verts_iff_deg_pos S v).mp hv
  by_contra hlt
  have h1 : deg S v = 1 := by omega
  rcases Finset.card_eq_one.mp h1 with ⟨e, heq⟩
  have heInc : e ∈ inc S v := by rw [heq]; exact Finset.mem_singleton_self e
  have heS : e ∈ S := (Finset.mem_filter.mp heInc).1
  have hvNot : v ∉ verts (S.erase e) := by
    rw [mem_verts_iff_inc_nonempty]
    rintro ⟨e', he'⟩
    rcases Finset.mem_filter.mp he' with ⟨he'Er, he'v⟩
    rcases Finset.mem_erase.mp he'Er with ⟨hne, he'S⟩
    have he'Inc : e' ∈ inc S v := Finset.mem_filter.mpr ⟨he'S, he'v⟩
    rw [heq, Finset.mem_singleton] at he'Inc
    exact hne he'Inc
  have hvSub : verts (S.erase e) ⊆ (verts S).erase v := by
    intro w hw
    exact Finset.mem_erase.mpr ⟨fun h => hvNot (h ▸ hw), verts_mono (Finset.erase_subset e S) hw⟩
  have hvc : (verts (S.erase e)).card ≤ (verts S).card - 1 := by
    have := Finset.card_le_card hvSub
    rwa [Finset.card_erase_of_mem hv] at this
  have hec : (S.erase e).card = S.card - 1 := Finset.card_erase_of_mem heS
  have hltS : ex (S.erase e) < ex S := hMin (S.erase e) (Finset.erase_ssubset heS)
  have hvPos : 1 ≤ (verts S).card := Finset.card_pos.mpr ⟨v, hv⟩
  have hSPos : 1 ≤ S.card := Finset.card_pos.mpr ⟨e, heS⟩
  simp only [ex] at hltS
  omega

def branchVerts (S : Finset (GEdge G)) : Finset (Vert m n) :=
  (verts S).filter (fun v => 3 ≤ deg S v)

lemma branchVerts_subset (S : Finset (GEdge G)) : branchVerts S ⊆ verts S :=
  Finset.filter_subset _ _

lemma sum_branch_excess {S : Finset (GEdge G)} (hdeg : ∀ v ∈ verts S, 2 ≤ deg S v) :
    ∑ v ∈ branchVerts S, (deg S v - 2) = 2 * (S.card - (verts S).card) := by
  have h1 : ∑ v ∈ branchVerts S, (deg S v - 2) = ∑ v ∈ verts S, (deg S v - 2) := by
    apply Finset.sum_subset (branchVerts_subset S)
    intro v hv hnotB
    have h2 := hdeg v hv
    simp only [branchVerts, Finset.mem_filter, not_and, not_le] at hnotB
    have := hnotB hv
    omega
  rw [h1]
  have h2 : (∑ v ∈ verts S, (deg S v - 2)) + ∑ v ∈ verts S, 2 = ∑ v ∈ verts S, deg S v := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    have := hdeg v hv
    omega
  rw [sum_deg] at h2
  simp only [Finset.sum_const, smul_eq_mul] at h2
  omega

lemma branchVerts_card_bounds {S : Finset (GEdge G)}
    (hdeg : ∀ v ∈ verts S, 2 ≤ deg S v) (hpos : 0 < ex S) :
    1 ≤ (branchVerts S).card ∧ (branchVerts S).card ≤ 2 * (S.card - (verts S).card) := by
  have hsum := sum_branch_excess hdeg
  have hsubPos : 0 < S.card - (verts S).card := by
    simp only [ex] at hpos; omega
  have hle : (branchVerts S).card ≤ ∑ v ∈ branchVerts S, (deg S v - 2) := by
    calc (branchVerts S).card = ∑ _v ∈ branchVerts S, 1 := by simp
      _ ≤ ∑ v ∈ branchVerts S, (deg S v - 2) := by
        apply Finset.sum_le_sum
        intro v hv
        have := (Finset.mem_filter.mp hv).2
        omega
  constructor
  · by_contra h0
    have hEmpty : branchVerts S = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hEmpty, Finset.sum_empty] at hsum
    omega
  · omega

end GraphBasics

section Threads

variable {m n : ℕ} {G : BipGraph m n}

def other (v : Vert m n) (e : GEdge G) : Vert m n :=
  if endL e = v then endR e else endL e

abbrev Dart (m n : ℕ) (G : BipGraph m n) : Type := Vert m n × GEdge G

def GoodDart (S : Finset (GEdge G)) (d : Dart m n G) : Prop :=
  d.2 ∈ inc S d.1

def flip (d : Dart m n G) : Dart m n G :=
  (other d.1 d.2, d.2)

lemma other_endL (e : GEdge G) : other (endL e) e = endR e := by
  simp [other]

lemma other_endR (e : GEdge G) : other (endR e) e = endL e := by
  unfold other
  rw [ite_eq_right_iff.mpr (fun h => (endL_ne_endR e h).elim)]

lemma other_other {S : Finset (GEdge G)} {d : Dart m n G} (hd : GoodDart S d) :
    other (other d.1 d.2) d.2 = d.1 := by
  rcases (Finset.mem_filter.mp hd).2 with h | h
  · rw [← h, other_endL, other_endR]
  · rw [← h, other_endR, other_endL]

lemma other_ne {S : Finset (GEdge G)} {d : Dart m n G} (hd : GoodDart S d) :
    other d.1 d.2 ≠ d.1 := by
  rcases (Finset.mem_filter.mp hd).2 with h | h
  · rw [← h, other_endL]; exact (endL_ne_endR d.2).symm
  · rw [← h, other_endR]; exact endL_ne_endR d.2

lemma flip_good {S : Finset (GEdge G)} {d : Dart m n G} (hd : GoodDart S d) :
    GoodDart S (flip d) := by
  rcases Finset.mem_filter.mp hd with ⟨heS, h | h⟩
  · refine Finset.mem_filter.mpr ⟨heS, Or.inr ?_⟩
    simp [flip, ← h, other_endL]
  · refine Finset.mem_filter.mpr ⟨heS, Or.inl ?_⟩
    simp [flip, ← h, other_endR]

lemma flip_flip {S : Finset (GEdge G)} {d : Dart m n G} (hd : GoodDart S d) :
    flip (flip d) = d := by
  rcases d with ⟨v, e⟩
  simp only [flip]
  exact Prod.ext (other_other hd) rfl

lemma flip_ne {S : Finset (GEdge G)} {d : Dart m n G} (hd : GoodDart S d) :
    flip d ≠ d := by
  intro h
  exact other_ne hd (congrArg Prod.fst h)

lemma goodDart_eq_or_flip {S : Finset (GEdge G)} {a b : Dart m n G}
    (ha : GoodDart S a) (hb : GoodDart S b) (he : a.2 = b.2) :
    a = b ∨ a = flip b := by
  rcases a with ⟨va, ea⟩
  rcases b with ⟨vb, eb⟩
  simp only at he
  subst he
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  dsimp only at ha' hb'
  rcases ha' with haL | haR <;> rcases hb' with hbL | hbR
  · left; exact Prod.ext (haL.symm.trans hbL) rfl
  · right; exact Prod.ext (by rw [flip, ← hbR, other_endR, haL]) rfl
  · right; exact Prod.ext (by rw [flip, ← hbL, other_endL, haR]) rfl
  · left; exact Prod.ext (haR.symm.trans hbR) rfl

noncomputable def nextEdge (S : Finset (GEdge G)) (v : Vert m n) (e : GEdge G) : GEdge G :=
  if h : ((inc S v).erase e).Nonempty then h.choose else e

lemma nextEdge_spec {S : Finset (GEdge G)} {v : Vert m n} {e : GEdge G}
    (he : e ∈ inc S v) (hdeg : deg S v = 2) :
    nextEdge S v e ∈ inc S v ∧ nextEdge S v e ≠ e ∧
    (∀ e' ∈ inc S v, e' ≠ e → e' = nextEdge S v e) := by
  have hcard : ((inc S v).erase e).card = 1 := by
    rw [Finset.card_erase_of_mem he]; unfold deg at hdeg; omega
  have hne : ((inc S v).erase e).Nonempty := Finset.card_pos.mp (by omega)
  have hmem : nextEdge S v e ∈ (inc S v).erase e := by
    unfold nextEdge
    split_ifs
    exact hne.choose_spec
  rcases Finset.mem_erase.mp hmem with ⟨hne_e, hinc⟩
  refine ⟨hinc, hne_e, ?_⟩
  intro e' he' hne'
  have hmem' : e' ∈ (inc S v).erase e := Finset.mem_erase.mpr ⟨hne', he'⟩
  rcases Finset.card_eq_one.mp hcard with ⟨x, hx⟩
  rw [hx, Finset.mem_singleton] at hmem hmem'
  exact hmem'.trans hmem.symm

lemma nextEdge_invol {S : Finset (GEdge G)} {v : Vert m n} {e : GEdge G}
    (he : e ∈ inc S v) (hdeg : deg S v = 2) :
    nextEdge S v (nextEdge S v e) = e := by
  rcases nextEdge_spec he hdeg with ⟨h1, h2, _⟩
  rcases nextEdge_spec h1 hdeg with ⟨_, _, huniq⟩
  exact (huniq e he h2.symm).symm

noncomputable def stepDart (S : Finset (GEdge G)) (d : Dart m n G) : Dart m n G :=
  (other d.1 d.2, nextEdge S (other d.1 d.2) d.2)

lemma stepDart_good {S : Finset (GEdge G)} {d : Dart m n G}
    (hd : GoodDart S d) (hdeg : deg S (other d.1 d.2) = 2) :
    GoodDart S (stepDart S d) :=
  (nextEdge_spec (flip_good hd) hdeg).1

lemma stepDart_snd_ne {S : Finset (GEdge G)} {d : Dart m n G}
    (hd : GoodDart S d) (hdeg : deg S (other d.1 d.2) = 2) :
    (stepDart S d).2 ≠ d.2 :=
  (nextEdge_spec (flip_good hd) hdeg).2.1

lemma stepDart_flip_stepDart {S : Finset (GEdge G)} {d : Dart m n G}
    (hd : GoodDart S d) (hdeg : deg S (other d.1 d.2) = 2) :
    stepDart S (flip (stepDart S d)) = flip d := by
  have hd' : GoodDart S (stepDart S d) := stepDart_good hd hdeg
  have hoth : other (flip (stepDart S d)).1 (flip (stepDart S d)).2 = other d.1 d.2 := by
    simpa [flip, stepDart] using other_other hd'
  have hne := nextEdge_invol (flip_good hd) hdeg
  unfold stepDart flip
  dsimp only
  rw [show other (other (other d.1 d.2) (nextEdge S (other d.1 d.2) d.2))
        (nextEdge S (other d.1 d.2) d.2) = other d.1 d.2 from hoth]
  exact Prod.ext rfl hne

noncomputable def trace (S : Finset (GEdge G)) (B : Finset (Vert m n)) :
    ℕ → Dart m n G → List (Dart m n G)
  | 0, d => [d]
  | k + 1, d => if other d.1 d.2 ∈ B then [d] else d :: trace S B k (stepDart S d)

lemma trace_ne_nil (S : Finset (GEdge G)) (B : Finset (Vert m n)) (k : ℕ) (d : Dart m n G) :
    trace S B k d ≠ [] := by
  cases k with
  | zero => simp [trace]
  | succ k => unfold trace; split_ifs <;> simp

lemma trace_length_le (S : Finset (GEdge G)) (B : Finset (Vert m n)) (k : ℕ) (d : Dart m n G) :
    (trace S B k d).length ≤ k + 1 := by
  induction k generalizing d with
  | zero => simp [trace]
  | succ k ih =>
    unfold trace
    split_ifs
    · simp
    · simp only [List.length_cons]
      have := ih (stepDart S d)
      omega

lemma trace_head (S : Finset (GEdge G)) (B : Finset (Vert m n)) (k : ℕ) (d : Dart m n G) :
    (trace S B k d)[0]'(List.length_pos_of_ne_nil (trace_ne_nil S B k d)) = d := by
  cases k with
  | zero => simp [trace]
  | succ k => unfold trace; split_ifs <;> rfl

lemma trace_step_props (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v) :
    let B := branchVerts S
    ∀ (k : ℕ) (d : Dart m n G), GoodDart S d →
      (∀ x ∈ trace S B k d, GoodDart S x) ∧
      (∀ (i : ℕ) (hi : i + 1 < (trace S B k d).length),
        other (trace S B k d)[i].1 (trace S B k d)[i].2 ∉ B ∧
        (trace S B k d)[i + 1] = stepDart S (trace S B k d)[i] ∧
        (trace S B k d)[i + 1].1 ∉ B) ∧
      ((trace S B k d).length ≤ k →
        other ((trace S B k d).getLast (trace_ne_nil S B k d)).1
              ((trace S B k d).getLast (trace_ne_nil S B k d)).2 ∈ B) := by
  intro B k
  induction k with
  | zero =>
    intro d hd
    refine ⟨by simp [trace, hd], ?_, ?_⟩
    · intro i hi; simp [trace] at hi
    · intro hle; simp [trace] at hle
  | succ k ih =>
    intro d hd
    unfold trace
    split_ifs with hB
    · refine ⟨by simp [hd], ?_, ?_⟩
      · intro i hi; simp at hi
      · intro _; simpa using hB
    · have hothV : other d.1 d.2 ∈ verts S :=
        (mem_verts_iff_inc_nonempty S _).mpr ⟨d.2, flip_good hd⟩
      have hdegEq : deg S (other d.1 d.2) = 2 := by
        have hge := hdeg2 _ hothV
        simp only [B, branchVerts, Finset.mem_filter, not_and, not_le] at hB
        have hlt := hB hothV
        omega
      have hstepGood : GoodDart S (stepDart S d) := stepDart_good hd hdegEq
      rcases ih (stepDart S d) hstepGood with ⟨ihGood, ihStep, ihLast⟩
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hxt
        · exact hd
        · exact ihGood x hxt
      · intro i hi
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero, List.getElem_cons_succ, trace_head]
          exact ⟨hB, trivial, hB⟩
        | succ i' =>
          simp only [List.getElem_cons_succ]
          exact ihStep i' (by simpa using hi)
      · intro hle
        have hle' : (trace S B k (stepDart S d)).length ≤ k := by
          simp only [List.length_cons] at hle; omega
        have hlastEq : (d :: trace S B k (stepDart S d)).getLast (by simp) =
            (trace S B k (stepDart S d)).getLast (trace_ne_nil S B k (stepDart S d)) :=
          List.getLast_cons (trace_ne_nil S B k (stepDart S d))
        rw [hlastEq]
        exact ihLast hle'

lemma deg_eq_two_of_not_branch {S : Finset (GEdge G)} (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    {v : Vert m n} (hv : v ∈ verts S) (hnB : v ∉ branchVerts S) :
    deg S v = 2 := by
  have hge := hdeg2 v hv
  simp only [branchVerts, Finset.mem_filter, not_and, not_le] at hnB
  have hlt := hnB hv
  omega

lemma trace_edges_nodup (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (k : ℕ) (d : Dart m n G) (hd : GoodDart S d) (hdB : d.1 ∈ branchVerts S) :
    ((trace S (branchVerts S) k d).map Prod.snd).Nodup := by
  classical
  set B := branchVerts S
  set L := trace S B k d
  rcases trace_step_props S hdeg2 k d hd with ⟨hGood, hStep, _⟩
  change ∀ x ∈ L, GoodDart S x at hGood
  change ∀ (i : ℕ) (hi : i + 1 < L.length),
    other L[i].1 L[i].2 ∉ B ∧ L[i + 1] = stepDart S L[i] ∧ L[i + 1].1 ∉ B at hStep
  rw [List.nodup_iff_injective_getElem]
  by_contra hnot
  have hex : ∃ i : ℕ, ∃ (hi : i < L.length), ∃ (j : ℕ) (hj : j < i),
      (L[j]'(lt_trans hj hi)).2 = L[i].2 := by
    by_contra hno
    apply hnot
    intro a b hab
    simp only [List.getElem_map] at hab
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · exact hno ⟨b.1, by simpa using b.2, a.1, hlt, hab⟩
    · exact hno ⟨a.1, by simpa using a.2, b.1, hgt, hab.symm⟩
  let i := Nat.find hex
  have hi_spec := Nat.find_spec hex
  have hi_min : ∀ i' < i, ¬ ∃ (hi' : i' < L.length), ∃ (j : ℕ) (hj : j < i'),
      (L[j]'(lt_trans hj hi')).2 = L[i'].2 :=
    fun i' hlt => Nat.find_min hex hlt
  rcases hi_spec with ⟨hi_lt, j, hji, hEqE⟩
  have hGi : GoodDart S L[i] := hGood _ (List.getElem_mem hi_lt)
  have hGj : GoodDart S (L[j]'(lt_trans hji hi_lt)) := hGood _ (List.getElem_mem (lt_trans hji hi_lt))
  have hi_pos : 0 < i := Nat.zero_lt_of_lt hji
  let i' := i - 1
  have hi'_eq : i' + 1 = i := Nat.sub_add_cancel hi_pos
  have hSi := hStep i' (by omega)
  have hL_i : L[i] = stepDart S (L[i']'(by omega)) := by
    have h1 := hSi.2.1
    have h2 : L[i' + 1]'(by omega) = L[i] := by congr 1
    exact h2.symm.trans h1
  have hLi_notB : L[i].1 ∉ B := by
    have h1 := hSi.2.2
    have h2 : L[i' + 1]'(by omega) = L[i] := by congr 1
    rwa [h2] at h1
  have hGi' : GoodDart S (L[i']'(by omega)) := hGood _ (List.getElem_mem (by omega))
  have hLi_deg : deg S (other (L[i']'(by omega)).1 (L[i']'(by omega)).2) = 2 := by
    apply deg_eq_two_of_not_branch hdeg2
    · exact (mem_verts_iff_inc_nonempty S _).mpr ⟨(L[i']'(by omega)).2, flip_good hGi'⟩
    · exact hSi.1
  have hInv_i : stepDart S (flip L[i]) = flip (L[i']'(by omega)) := by
    rw [hL_i]
    exact stepDart_flip_stepDart hGi' hLi_deg
  rcases goodDart_eq_or_flip hGj hGi hEqE with hSame | hFlip
  · cases j with
    | zero =>
      have h0 : L[0]'(List.length_pos_of_ne_nil (trace_ne_nil S B k d)) = d := trace_head S B k d
      have hL0B : (L[0]'(by omega)).1 ∈ B := by rw [h0]; exact hdB
      rw [hSame] at hL0B
      exact hLi_notB hL0B
    | succ j' =>
      have hSj := hStep j' (by omega)
      have hGj' : GoodDart S (L[j']'(by omega)) := hGood _ (List.getElem_mem (by omega))
      have hLj_deg : deg S (other (L[j']'(by omega)).1 (L[j']'(by omega)).2) = 2 := by
        apply deg_eq_two_of_not_branch hdeg2
        · exact (mem_verts_iff_inc_nonempty S _).mpr ⟨(L[j']'(by omega)).2, flip_good hGj'⟩
        · exact hSj.1
      have hInv_j : stepDart S (flip (L[j' + 1]'(by omega))) = flip (L[j']'(by omega)) := by
        rw [hSj.2.1]
        exact stepDart_flip_stepDart hGj' hLj_deg
      have hFlipEq : flip (L[j']'(by omega)) = flip (L[i']'(by omega)) := by
        rw [← hInv_j, ← hInv_i, hSame]
      have hPrevEq : (L[j']'(by omega)) = (L[i']'(by omega)) := by
        have := congrArg flip hFlipEq
        rwa [flip_flip hGj', flip_flip hGi'] at this
      exact hi_min i' (by omega) ⟨by omega, j', by omega, congrArg Prod.snd hPrevEq⟩
  · by_cases hAdj : j + 1 = i
    · have hSj := hStep j (by omega)
      have hLj_deg : deg S (other (L[j]'(by omega)).1 (L[j]'(by omega)).2) = 2 := by
        apply deg_eq_two_of_not_branch hdeg2
        · exact (mem_verts_iff_inc_nonempty S _).mpr ⟨(L[j]'(by omega)).2, flip_good hGj⟩
        · exact hSj.1
      have hne : (stepDart S (L[j]'(by omega))).2 ≠ (L[j]'(by omega)).2 := stepDart_snd_ne hGj hLj_deg
      have hEq1 : L[j + 1]'(by omega) = L[i] := by congr 1
      rw [← hSj.2.1, hEq1] at hne
      exact hne hEqE.symm
    · have hSj := hStep j (by omega)
      have hNextEq : L[j + 1]'(by omega) = flip (L[i']'(by omega)) := by
        rw [hSj.2.1, hFlip, hInv_i]
      by_cases hMid : j + 1 = i'
      · have hEqMid : L[j + 1]'(by omega) = L[i']'(by omega) := by congr 1
        rw [hEqMid] at hNextEq
        exact flip_ne hGi' hNextEq.symm
      · exact hi_min i' (by omega) ⟨by omega, j + 1, by omega,
          by rw [hNextEq]; rfl⟩

lemma trace_length_le_card (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (k : ℕ) (d : Dart m n G) (hd : GoodDart S d) (hdB : d.1 ∈ branchVerts S) :
    (trace S (branchVerts S) k d).length ≤ S.card := by
  have hnd := trace_edges_nodup S hdeg2 k d hd hdB
  have hGood := (trace_step_props S hdeg2 k d hd).1
  have hsub : ((trace S (branchVerts S) k d).map Prod.snd).toFinset ⊆ S := by
    intro e he
    rw [List.mem_toFinset, List.mem_map] at he
    rcases he with ⟨x, hx, rfl⟩
    exact (Finset.mem_filter.mp (hGood x hx)).1
  calc (trace S (branchVerts S) k d).length
      = ((trace S (branchVerts S) k d).map Prod.snd).length := (List.length_map _).symm
    _ = ((trace S (branchVerts S) k d).map Prod.snd).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ S.card := Finset.card_le_card hsub

lemma trace_ends_in_branch (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (d : Dart m n G) (hd : GoodDart S d) (hdB : d.1 ∈ branchVerts S) :
    other ((trace S (branchVerts S) S.card d).getLast (trace_ne_nil S (branchVerts S) S.card d)).1
          ((trace S (branchVerts S) S.card d).getLast (trace_ne_nil S (branchVerts S) S.card d)).2
      ∈ branchVerts S :=
  (trace_step_props S hdeg2 S.card d hd).2.2 (trace_length_le_card S hdeg2 S.card d hd hdB)

lemma trace_eq_of_chain (S : Finset (GEdge G)) (B : Finset (Vert m n)) :
    ∀ (L : List (Dart m n G)) (hL : L ≠ []) (k : ℕ),
      L.length ≤ k + 1 →
      (∀ (i : ℕ) (hi : i + 1 < L.length),
        other L[i].1 L[i].2 ∉ B ∧ L[i + 1] = stepDart S L[i]) →
      other (L.getLast hL).1 (L.getLast hL).2 ∈ B →
      trace S B k (L[0]'(List.length_pos_of_ne_nil hL)) = L := by
  intro L
  induction L with
  | nil => intro hL; exact (hL rfl).elim
  | cons a t ih =>
    intro hL k hlen hstep hlast
    cases t with
    | nil =>
      cases k with
      | zero => simp [trace]
      | succ k' =>
        simp only [List.getLast_singleton] at hlast
        simp [trace, hlast]
    | cons b t' =>
      cases k with
      | zero => simp at hlen
      | succ k' =>
        have h0 := hstep 0 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 ⊢
        unfold trace
        rw [ite_eq_right_iff.mpr (fun h => (h0.1 h).elim)]
        congr 1
        have hih := ih (by simp) k' (by simp only [List.length_cons] at hlen ⊢; omega)
          (fun i hi => by
            have h1 := hstep (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
            simpa only [List.getElem_cons_succ] using h1)
          (by simpa [List.getLast_cons (show b :: t' ≠ [] by simp)] using hlast)
        simpa [h0.2] using hih

noncomputable def revDart (S : Finset (GEdge G)) (d : Dart m n G) : Dart m n G :=
  flip ((trace S (branchVerts S) S.card d).getLast (trace_ne_nil S (branchVerts S) S.card d))

lemma trace_revDart (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (d : Dart m n G) (hd : GoodDart S d) (hdB : d.1 ∈ branchVerts S) :
    trace S (branchVerts S) S.card (revDart S d) =
      (trace S (branchVerts S) S.card d).reverse.map flip := by
  set B := branchVerts S
  set L := trace S B S.card d
  have hLeq : trace S (branchVerts S) S.card d = L := rfl
  have hne : L ≠ [] := trace_ne_nil S B S.card d
  set R := L.reverse.map flip
  have hRne : R ≠ [] := by simp [R, hne]
  rcases trace_step_props S hdeg2 S.card d hd with ⟨hGood, hStep, _⟩
  change ∀ x ∈ L, GoodDart S x at hGood
  change ∀ (i : ℕ) (hi : i + 1 < L.length),
    other L[i].1 L[i].2 ∉ B ∧ L[i + 1] = stepDart S L[i] ∧ L[i + 1].1 ∉ B at hStep
  have hLenLe : L.length ≤ S.card := trace_length_le_card S hdeg2 S.card d hd hdB
  have hRlen : R.length = L.length := by simp [R]
  have hR0 : R[0]'(List.length_pos_of_ne_nil hRne) = revDart S d := by
    simp only [R, revDart, List.getElem_map, List.getElem_reverse]
    congr 1
    rw [List.getLast_eq_getElem]
    simp [hLeq]
  have hRget : ∀ (i : ℕ) (hi : i < R.length),
      R[i] = flip (L[L.length - 1 - i]'(by omega)) := by
    intro i hi
    simp only [R, List.getElem_map, List.getElem_reverse]
  have hRstep : ∀ (i : ℕ) (hi : i + 1 < R.length),
      other R[i].1 R[i].2 ∉ B ∧ R[i + 1] = stepDart S R[i] := by
    intro i hi
    have hj_lt : L.length - 1 - (i + 1) + 1 < L.length := by omega
    set j := L.length - 1 - (i + 1)
    have hj1 : L.length - 1 - i = j + 1 := by omega
    have hRi : R[i] = flip (L[j + 1]'(by omega)) := by
      rw [hRget i (by omega)]
      exact congrArg flip (by congr 1)
    have hRi1 : R[i + 1] = flip (L[j]'(by omega)) := hRget (i + 1) hi
    have hSj := hStep j hj_lt
    have hGj : GoodDart S (L[j]'(by omega)) := hGood _ (List.getElem_mem (by omega))
    have hGj1 : GoodDart S (L[j + 1]'(hj_lt)) := hGood _ (List.getElem_mem hj_lt)
    have hdegJ : deg S (other (L[j]'(by omega)).1 (L[j]'(by omega)).2) = 2 := by
      apply deg_eq_two_of_not_branch hdeg2
      · exact (mem_verts_iff_inc_nonempty S _).mpr ⟨(L[j]'(by omega)).2, flip_good hGj⟩
      · exact hSj.1
    have hOthRi : other R[i].1 R[i].2 = (L[j + 1]'(hj_lt)).1 := by
      rw [hRi]
      exact other_other hGj1
    constructor
    · rw [hOthRi]; exact hSj.2.2
    · rw [hRi, hRi1, hSj.2.1]
      exact (stepDart_flip_stepDart hGj hdegJ).symm
  have hLpos : 0 < L.length := List.length_pos_of_ne_nil hne
  have hRlast : other (R.getLast hRne).1 (R.getLast hRne).2 ∈ B := by
    rw [List.getLast_eq_getElem, hRget (R.length - 1) (by omega)]
    have h0 : L.length - 1 - (R.length - 1) = 0 := by omega
    have hL0 : L[L.length - 1 - (R.length - 1)]'(by omega) = d := by
      simpa [h0] using trace_head S B S.card d
    rw [hL0]
    have : other (flip d).1 (flip d).2 = d.1 := other_other hd
    rwa [this]
  have hRle : R.length ≤ S.card + 1 := by omega
  have hEq := trace_eq_of_chain S B R hRne S.card hRle hRstep hRlast
  simpa [hR0] using hEq

lemma revDart_good (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (d : Dart m n G) (hd : GoodDart S d) (hdB : d.1 ∈ branchVerts S) :
    GoodDart S (revDart S d) ∧ (revDart S d).1 ∈ branchVerts S := by
  have hGood := (trace_step_props S hdeg2 S.card d hd).1
  have hLastGood : GoodDart S ((trace S (branchVerts S) S.card d).getLast (trace_ne_nil S (branchVerts S) S.card d)) :=
    hGood _ (List.getLast_mem (trace_ne_nil S (branchVerts S) S.card d))
  exact ⟨flip_good hLastGood, trace_ends_in_branch S hdeg2 d hd hdB⟩

lemma revDart_invol (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (d : Dart m n G) (hd : GoodDart S d) (hdB : d.1 ∈ branchVerts S) :
    revDart S (revDart S d) = d := by
  have htr := trace_revDart S hdeg2 d hd hdB
  set L := trace S (branchVerts S) S.card d
  have hne : L ≠ [] := trace_ne_nil S (branchVerts S) S.card d
  have hlast : (trace S (branchVerts S) S.card (revDart S d)).getLast
      (trace_ne_nil S (branchVerts S) S.card (revDart S d)) = flip d := by
    have h1 : (L.reverse.map flip).getLast (by simp [hne]) = flip d := by
      rw [List.getLast_map, List.getLast_reverse]
      rw [List.head_eq_getElem_zero]
      exact congrArg flip (trace_head S (branchVerts S) S.card d)
    simpa [htr] using h1
  change flip ((trace S (branchVerts S) S.card (revDart S d)).getLast
    (trace_ne_nil S (branchVerts S) S.card (revDart S d))) = d
  rw [hlast]
  exact flip_flip hd

lemma revDart_ne (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (d : Dart m n G) (hd : GoodDart S d) (hdB : d.1 ∈ branchVerts S) :
    revDart S d ≠ d := by
  set L := trace S (branchVerts S) S.card d
  have hne : L ≠ [] := trace_ne_nil S (branchVerts S) S.card d
  have hnd := trace_edges_nodup S hdeg2 S.card d hd hdB
  by_cases hlen : L.length = 1
  · have hEqLast : L.getLast hne = d := by
      rw [List.getLast_eq_getElem]
      have h0 : L.length - 1 = 0 := by omega
      simpa [h0] using trace_head S (branchVerts S) S.card d
    change flip (L.getLast hne) ≠ d
    rw [hEqLast]
    exact flip_ne hd
  · have hpos : 1 < L.length := by
      have := List.length_pos_of_ne_nil hne; omega
    have hneE : (L.getLast hne).2 ≠ d.2 := by
      rw [List.getLast_eq_getElem]
      rw [List.nodup_iff_injective_getElem] at hnd
      intro hEq
      have hFin : (⟨L.length - 1, by simp; omega⟩ : Fin (L.map Prod.snd).length) =
                  ⟨0, by simp; omega⟩ := by
        apply hnd
        simp only [List.getElem_map]
        rw [hEq, trace_head]
      have hVal := congrArg Fin.val hFin
      simp at hVal
      omega
    intro hEq
    have hSnd : (revDart S d).2 = (L.getLast hne).2 := rfl
    exact hneE (hSnd.symm.trans (congrArg Prod.snd hEq))

noncomputable def threadEdges (S : Finset (GEdge G)) (d : Dart m n G) : Finset (GEdge G) :=
  ((trace S (branchVerts S) S.card d).map Prod.snd).toFinset

lemma threadEdges_subset (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (d : Dart m n G) (hd : GoodDart S d) :
    threadEdges S d ⊆ S := by
  intro e he
  rw [threadEdges, List.mem_toFinset, List.mem_map] at he
  rcases he with ⟨x, hx, rfl⟩
  exact (Finset.mem_filter.mp ((trace_step_props S hdeg2 S.card d hd).1 x hx)).1

lemma threadEdges_revDart (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (d : Dart m n G) (hd : GoodDart S d) (hdB : d.1 ∈ branchVerts S) :
    threadEdges S (revDart S d) = threadEdges S d := by
  ext e
  simp only [threadEdges, trace_revDart S hdeg2 d hd hdB, List.mem_toFinset, List.mem_map,
    List.mem_reverse]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨flip x, ⟨x, hx, rfl⟩, rfl⟩

lemma mem_threadEdges_self (S : Finset (GEdge G)) (d : Dart m n G) :
    d.2 ∈ threadEdges S d := by
  rw [threadEdges, List.mem_toFinset, List.mem_map]
  have hpos := List.length_pos_of_ne_nil (trace_ne_nil S (branchVerts S) S.card d)
  have hmem : (trace S (branchVerts S) S.card d)[0]'hpos ∈ trace S (branchVerts S) S.card d :=
    List.getElem_mem hpos
  rw [trace_head] at hmem
  exact ⟨d, hmem, rfl⟩

lemma endpoint_mem_verts_threadEdges (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (d : Dart m n G) (hd : GoodDart S d) (hdB : d.1 ∈ branchVerts S) :
    d.1 ∈ verts (threadEdges S d) ∧ (revDart S d).1 ∈ verts (threadEdges S d) := by
  constructor
  · have hmem : d.2 ∈ threadEdges S d := mem_threadEdges_self S d
    rcases (Finset.mem_filter.mp hd).2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d.2, hmem, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d.2, hmem, h⟩)
  · have hrg := revDart_good S hdeg2 d hd hdB
    have hmem : (revDart S d).2 ∈ threadEdges S d := by
      rw [← threadEdges_revDart S hdeg2 d hd hdB]
      exact mem_threadEdges_self S (revDart S d)
    rcases (Finset.mem_filter.mp hrg.1).2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hmem, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hmem, h⟩)

lemma verts_threadEdges_inter_branch (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (d : Dart m n G) (hd : GoodDart S d) (hdB : d.1 ∈ branchVerts S) :
    verts (threadEdges S d) ∩ branchVerts S = {d.1, (revDart S d).1} := by
  set B := branchVerts S
  set L := trace S B S.card d
  have hLeq : trace S (branchVerts S) S.card d = L := rfl
  have hne : L ≠ [] := trace_ne_nil S B S.card d
  rcases trace_step_props S hdeg2 S.card d hd with ⟨hGood, hStep, _⟩
  change ∀ x ∈ L, GoodDart S x at hGood
  change ∀ (i : ℕ) (hi : i + 1 < L.length),
    other L[i].1 L[i].2 ∉ B ∧ L[i + 1] = stepDart S L[i] ∧ L[i + 1].1 ∉ B at hStep
  have hEnds := endpoint_mem_verts_threadEdges S hdeg2 d hd hdB
  have hrg := revDart_good S hdeg2 d hd hdB
  ext v
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hvT, hvB⟩
    have hvInc : ∃ e ∈ threadEdges S d, endL e = v ∨ endR e = v := by
      simp only [verts, Finset.mem_union, Finset.mem_image] at hvT
      rcases hvT with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
      · exact ⟨e, he, Or.inl rfl⟩
      · exact ⟨e, he, Or.inr rfl⟩
    rcases hvInc with ⟨e, heT, hev⟩
    rw [threadEdges, hLeq, List.mem_toFinset, List.mem_map] at heT
    rcases heT with ⟨x, hxL, rfl⟩
    rcases List.getElem_of_mem hxL with ⟨i, hi, rfl⟩
    have hGx : GoodDart S L[i] := hGood _ hxL
    have hvOr : v = L[i].1 ∨ v = other L[i].1 L[i].2 := by
      rcases (Finset.mem_filter.mp hGx).2 with h1 | h1 <;> rcases hev with h2 | h2
      · left; exact h2.symm.trans h1
      · right; rw [← h2, ← h1, other_endL]
      · right; rw [← h2, ← h1, other_endR]
      · left; exact h2.symm.trans h1
    rcases hvOr with rfl | rfl
    · cases i with
      | zero => left; exact congrArg Prod.fst (trace_head S B S.card d)
      | succ i' => exact ((hStep i' (by omega)).2.2 hvB).elim
    · by_cases hLast : i + 1 < L.length
      · exact ((hStep i hLast).1 hvB).elim
      · right
        have hiEq : i = L.length - 1 := by omega
        change other L[i].1 L[i].2 = other (L.getLast hne).1 (L.getLast hne).2
        rw [List.getLast_eq_getElem]
        simp [hiEq]
  · rintro (rfl | rfl)
    · exact ⟨hEnds.1, hdB⟩
    · exact ⟨hEnds.2, hrg.2⟩

lemma trace_suffix_last_eq (S : Finset (GEdge G)) (B : Finset (Vert m n))
    {L₁ L₂ : List (Dart m n G)} (h1 : L₁ ≠ []) (h2 : L₂ ≠ [])
    (hs1 : ∀ (i : ℕ) (hi : i + 1 < L₁.length), other L₁[i].1 L₁[i].2 ∉ B ∧ L₁[i + 1] = stepDart S L₁[i])
    (hs2 : ∀ (i : ℕ) (hi : i + 1 < L₂.length), other L₂[i].1 L₂[i].2 ∉ B ∧ L₂[i + 1] = stepDart S L₂[i])
    (hl1 : other (L₁.getLast h1).1 (L₁.getLast h1).2 ∈ B)
    (hl2 : other (L₂.getLast h2).1 (L₂.getLast h2).2 ∈ B) :
    ∀ (k : ℕ) (i₁ i₂ : ℕ) (hi₁ : i₁ < L₁.length) (hi₂ : i₂ < L₂.length),
      L₁.length - i₁ ≤ k → L₁[i₁] = L₂[i₂] →
      L₁.getLast h1 = L₂.getLast h2 := by
  intro k
  induction k with
  | zero => intro i₁ _ hi₁ _ hk; omega
  | succ k ih =>
    intro i₁ i₂ hi₁ hi₂ hk hEq
    by_cases hEnd1 : i₁ + 1 < L₁.length
    · have hnotB : other L₁[i₁].1 L₁[i₁].2 ∉ B := (hs1 i₁ hEnd1).1
      have hEnd2 : i₂ + 1 < L₂.length := by
        by_contra hno
        have hi2Last : i₂ = L₂.length - 1 := by omega
        have hMemB : other L₂[i₂].1 L₂[i₂].2 ∈ B := by
          rw [List.getLast_eq_getElem] at hl2
          simpa [hi2Last] using hl2
        rw [← hEq] at hMemB
        exact hnotB hMemB
      have hNext : L₁[i₁ + 1] = L₂[i₂ + 1] := by
        rw [(hs1 i₁ hEnd1).2, (hs2 i₂ hEnd2).2, hEq]
      exact ih (i₁ + 1) (i₂ + 1) hEnd1 hEnd2 (by omega) hNext
    · have hi1Last : i₁ = L₁.length - 1 := by omega
      have hMemB : other L₁[i₁].1 L₁[i₁].2 ∈ B := by
        rw [List.getLast_eq_getElem] at hl1
        simpa [hi1Last] using hl1
      have hEnd2 : ¬ (i₂ + 1 < L₂.length) := by
        intro hlt
        have hnotB := (hs2 i₂ hlt).1
        rw [← hEq] at hnotB
        exact hnotB hMemB
      have hi2Last : i₂ = L₂.length - 1 := by omega
      rw [List.getLast_eq_getElem, List.getLast_eq_getElem]
      simpa [hi1Last, hi2Last] using hEq

lemma threadEdges_inter_eq_or_rev (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    {d₁ d₂ : Dart m n G}
    (hd₁ : GoodDart S d₁) (hd₁B : d₁.1 ∈ branchVerts S)
    (hd₂ : GoodDart S d₂) (hd₂B : d₂.1 ∈ branchVerts S)
    {e : GEdge G} (he₁ : e ∈ threadEdges S d₁) (he₂ : e ∈ threadEdges S d₂) :
    d₁ = d₂ ∨ d₁ = revDart S d₂ := by
  set B := branchVerts S
  set L₁ := trace S B S.card d₁
  set L₂ := trace S B S.card d₂
  have hL1eq : trace S (branchVerts S) S.card d₁ = L₁ := rfl
  have hL2eq : trace S (branchVerts S) S.card d₂ = L₂ := rfl
  rw [threadEdges, hL1eq, List.mem_toFinset, List.mem_map] at he₁
  rw [threadEdges, hL2eq, List.mem_toFinset, List.mem_map] at he₂
  rcases he₁ with ⟨a₁, ha₁, rfl⟩
  rcases he₂ with ⟨a₂, ha₂, haE⟩
  rcases List.getElem_of_mem ha₁ with ⟨i₁, hi₁, rfl⟩
  rcases List.getElem_of_mem ha₂ with ⟨i₂, hi₂, rfl⟩
  rcases trace_step_props S hdeg2 S.card d₁ hd₁ with ⟨hG1, hS1, _⟩
  rcases trace_step_props S hdeg2 S.card d₂ hd₂ with ⟨hG2, hS2, _⟩
  change ∀ x ∈ L₁, GoodDart S x at hG1
  change ∀ (i : ℕ) (hi : i + 1 < L₁.length),
    other L₁[i].1 L₁[i].2 ∉ B ∧ L₁[i + 1] = stepDart S L₁[i] ∧ L₁[i + 1].1 ∉ B at hS1
  change ∀ x ∈ L₂, GoodDart S x at hG2
  change ∀ (i : ℕ) (hi : i + 1 < L₂.length),
    other L₂[i].1 L₂[i].2 ∉ B ∧ L₂[i + 1] = stepDart S L₂[i] ∧ L₂[i + 1].1 ∉ B at hS2
  have h1 := hG1 _ ha₁
  have h2 := hG2 _ ha₂
  rcases goodDart_eq_or_flip h1 h2 haE.symm with hSame | hFlip
  · left
    have hLastEq := trace_suffix_last_eq S B (trace_ne_nil S B S.card d₁) (trace_ne_nil S B S.card d₂)
      (fun i hi => ⟨(hS1 i hi).1, (hS1 i hi).2.1⟩)
      (fun i hi => ⟨(hS2 i hi).1, (hS2 i hi).2.1⟩)
      (trace_ends_in_branch S hdeg2 d₁ hd₁ hd₁B)
      (trace_ends_in_branch S hdeg2 d₂ hd₂ hd₂B)
      L₁.length i₁ i₂ hi₁ hi₂ (Nat.sub_le L₁.length i₁) hSame
    have hRevEq : revDart S d₁ = revDart S d₂ := congrArg flip hLastEq
    have := congrArg (revDart S) hRevEq
    rwa [revDart_invol S hdeg2 d₁ hd₁ hd₁B, revDart_invol S hdeg2 d₂ hd₂ hd₂B] at this
  · right
    have hrg2 := revDart_good S hdeg2 d₂ hd₂ hd₂B
    set L₂' := trace S B S.card (revDart S d₂)
    have hmem2' : L₁[i₁] ∈ L₂' := by
      rw [show L₂' = L₂.reverse.map flip from trace_revDart S hdeg2 d₂ hd₂ hd₂B]
      rw [List.mem_map]
      exact ⟨L₂[i₂], List.mem_reverse.mpr ha₂, hFlip.symm⟩
    rcases List.getElem_of_mem hmem2' with ⟨i₂', hi₂', hEq2'⟩
    rcases trace_step_props S hdeg2 S.card (revDart S d₂) hrg2.1 with ⟨_, hS2', _⟩
    change ∀ (i : ℕ) (hi : i + 1 < L₂'.length),
      other L₂'[i].1 L₂'[i].2 ∉ B ∧ L₂'[i + 1] = stepDart S L₂'[i] ∧ L₂'[i + 1].1 ∉ B at hS2'
    have hLastEq := trace_suffix_last_eq S B (trace_ne_nil S B S.card d₁) (trace_ne_nil S B S.card (revDart S d₂))
      (fun i hi => ⟨(hS1 i hi).1, (hS1 i hi).2.1⟩)
      (fun i hi => ⟨(hS2' i hi).1, (hS2' i hi).2.1⟩)
      (trace_ends_in_branch S hdeg2 d₁ hd₁ hd₁B)
      (trace_ends_in_branch S hdeg2 (revDart S d₂) hrg2.1 hrg2.2)
      L₁.length i₁ i₂' hi₁ hi₂' (Nat.sub_le L₁.length i₁) hEq2'.symm
    have hRevEq : revDart S d₁ = revDart S (revDart S d₂) := congrArg flip hLastEq
    have := congrArg (revDart S) hRevEq
    rwa [revDart_invol S hdeg2 d₁ hd₁ hd₁B, revDart_invol S hdeg2 (revDart S d₂) hrg2.1 hrg2.2] at this

lemma getElem_succ_mem_tail {α : Type} {l : List α} {i : ℕ} (hi : i + 1 < l.length) :
    l[i + 1] ∈ l.tail := by
  cases l with
  | nil => simp at hi
  | cons x t =>
    simp only [List.tail_cons, List.getElem_cons_succ]
    exact List.getElem_mem (by simp at hi; omega)

lemma mem_tail_iff_exists_succ {α : Type} {l : List α} {x : α} :
    x ∈ l.tail ↔ ∃ (i : ℕ) (hi : i + 1 < l.length), l[i + 1] = x := by
  cases l with
  | nil => simp
  | cons a t =>
    simp only [List.tail_cons, List.length_cons, List.getElem_cons_succ]
    constructor
    · intro hx
      rcases List.getElem_of_mem hx with ⟨i, hi, rfl⟩
      exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact List.getElem_mem (by omega)

lemma getElem_tail_eq {α : Type} {l : List α} {i : ℕ} (hi : i < l.tail.length) :
    l.tail[i] = l[i + 1]'(by cases l <;> simp at hi ⊢; omega) := by
  cases l with
  | nil => simp at hi
  | cons a t => rfl

lemma thread_internal_props (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (d : Dart m n G) (hd : GoodDart S d) (hdB : d.1 ∈ branchVerts S) :
    (verts (threadEdges S d) \ branchVerts S).card + 1 = (threadEdges S d).card ∧
    ∀ v ∈ verts (threadEdges S d) \ branchVerts S, inc S v ⊆ threadEdges S d := by
  set B := branchVerts S
  set L := trace S B S.card d
  have hLeq : trace S (branchVerts S) S.card d = L := rfl
  have hne : L ≠ [] := trace_ne_nil S B S.card d
  have hnd : (L.map Prod.snd).Nodup := trace_edges_nodup S hdeg2 S.card d hd hdB
  rcases trace_step_props S hdeg2 S.card d hd with ⟨hGood, hStep, _⟩
  change ∀ x ∈ L, GoodDart S x at hGood
  change ∀ (i : ℕ) (hi : i + 1 < L.length),
    other L[i].1 L[i].2 ∉ B ∧ L[i + 1] = stepDart S L[i] ∧ L[i + 1].1 ∉ B at hStep
  have hCardE : (threadEdges S d).card = L.length := by
    rw [threadEdges, hLeq, List.toFinset_card_of_nodup hnd, List.length_map]
  have hIntEq : verts (threadEdges S d) \ B = (L.tail.map Prod.fst).toFinset := by
    ext v
    simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨hvT, hvNotB⟩
      have hvInc : ∃ e ∈ threadEdges S d, endL e = v ∨ endR e = v := by
        simp only [verts, Finset.mem_union, Finset.mem_image] at hvT
        rcases hvT with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
        · exact ⟨e, he, Or.inl rfl⟩
        · exact ⟨e, he, Or.inr rfl⟩
      rcases hvInc with ⟨e, heT, hev⟩
      rw [threadEdges, hLeq, List.mem_toFinset, List.mem_map] at heT
      rcases heT with ⟨x, hxL, rfl⟩
      rcases List.getElem_of_mem hxL with ⟨i, hi, rfl⟩
      have hGx : GoodDart S L[i] := hGood _ hxL
      have hvOr : v = L[i].1 ∨ v = other L[i].1 L[i].2 := by
        rcases (Finset.mem_filter.mp hGx).2 with h1 | h1 <;> rcases hev with h2 | h2
        · left; exact h2.symm.trans h1
        · right; rw [← h2, ← h1, other_endL]
        · right; rw [← h2, ← h1, other_endR]
        · left; exact h2.symm.trans h1
      rcases hvOr with rfl | rfl
      · cases i with
        | zero =>
          have h0 := trace_head S B S.card d
          rw [h0] at hvNotB
          exact (hvNotB hdB).elim
        | succ i' =>
          exact ⟨L[i' + 1], getElem_succ_mem_tail hi, rfl⟩
      · by_cases hlt : i + 1 < L.length
        · have hSi := hStep i hlt
          have hEqV : L[i + 1].1 = other L[i].1 L[i].2 := by rw [hSi.2.1]; rfl
          exact ⟨L[i + 1], getElem_succ_mem_tail hlt, hEqV⟩
        · have hiEq : i = L.length - 1 := by omega
          have hEndB : other (L.getLast hne).1 (L.getLast hne).2 ∈ B :=
            trace_ends_in_branch S hdeg2 d hd hdB
          rw [List.getLast_eq_getElem] at hEndB
          have : other L[i].1 L[i].2 ∈ B := by simpa [hiEq] using hEndB
          exact (hvNotB this).elim
    · rintro ⟨x, hxTail, rfl⟩
      rcases mem_tail_iff_exists_succ.mp hxTail with ⟨i', hi, rfl⟩
      have hGx : GoodDart S L[i' + 1] := hGood _ (List.getElem_mem hi)
      have hmemE : L[i' + 1].2 ∈ threadEdges S d := by
        rw [threadEdges, hLeq, List.mem_toFinset, List.mem_map]
        exact ⟨L[i' + 1], List.getElem_mem hi, rfl⟩
      have hvT : L[i' + 1].1 ∈ verts (threadEdges S d) := by
        rcases (Finset.mem_filter.mp hGx).2 with h | h
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hmemE, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hmemE, h⟩)
      exact ⟨hvT, (hStep i' hi).2.2⟩
  have hIncSub : ∀ (i : ℕ) (hi : i + 1 < L.length), inc S L[i + 1].1 ⊆ threadEdges S d := by
    intro i hi
    have hSi := hStep i hi
    have hGi : GoodDart S (L[i]'(by omega)) := hGood _ (List.getElem_mem (by omega))
    have hGi1 : GoodDart S L[i + 1] := hGood _ (List.getElem_mem hi)
    have hV : L[i + 1].1 ∈ verts S :=
      (mem_verts_iff_inc_nonempty S _).mpr ⟨L[i + 1].2, hGi1⟩
    have hdegEq : deg S L[i + 1].1 = 2 := deg_eq_two_of_not_branch hdeg2 hV hSi.2.2
    have he1 : (L[i]'(by omega)).2 ∈ inc S L[i + 1].1 := by
      have hEq1 : L[i + 1].1 = other (L[i]'(by omega)).1 (L[i]'(by omega)).2 := by rw [hSi.2.1]; rfl
      rw [hEq1]
      exact flip_good hGi
    have he2 : L[i + 1].2 ∈ inc S L[i + 1].1 := hGi1
    have hneE : L[i + 1].2 ≠ (L[i]'(by omega)).2 := by
      rw [hSi.2.1]
      apply stepDart_snd_ne hGi
      have hEq1 : L[i + 1].1 = other (L[i]'(by omega)).1 (L[i]'(by omega)).2 := by rw [hSi.2.1]; rfl
      rwa [← hEq1]
    have hPairSub : ({(L[i]'(by omega)).2, L[i + 1].2} : Finset (GEdge G)) ⊆ inc S L[i + 1].1 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact he1
      · rw [Finset.mem_singleton.mp hx']; exact he2
    have hPairEq : inc S L[i + 1].1 = {(L[i]'(by omega)).2, L[i + 1].2} := by
      symm
      apply Finset.eq_of_subset_of_card_le hPairSub
      rw [Finset.card_pair hneE.symm]
      exact hdegEq.le
    rw [hPairEq]
    intro x hx
    rw [threadEdges, hLeq, List.mem_toFinset, List.mem_map]
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact ⟨L[i]'(by omega), List.getElem_mem (by omega), rfl⟩
    · rw [Finset.mem_singleton.mp hx']
      exact ⟨L[i + 1], List.getElem_mem hi, rfl⟩
  have hTailNodup : (L.tail.map Prod.fst).Nodup := by
    have hltCase : ∀ (a b : Fin (L.tail.map Prod.fst).length),
        (L.tail.map Prod.fst)[a.1] = (L.tail.map Prod.fst)[b.1] → a.1 < b.1 → False := by
      intro a b hab hlt
      have ha : a.1 < L.tail.length := by simpa using a.2
      have hb : b.1 < L.tail.length := by simpa using b.2
      have ha1 : a.1 + 1 < L.length := by rw [List.length_tail] at ha; omega
      have hb1 : b.1 + 1 < L.length := by rw [List.length_tail] at hb; omega
      have hEqV : (L[a.1 + 1]'ha1).1 = (L[b.1 + 1]'hb1).1 := by
        simpa [List.getElem_map, getElem_tail_eq ha, getElem_tail_eq hb] using hab
      have hGb : GoodDart S (L[b.1 + 1]'hb1) := hGood _ (List.getElem_mem hb1)
      have hSa := hStep a.1 ha1
      have hGa : GoodDart S (L[a.1]'(by omega)) := hGood _ (List.getElem_mem (by omega))
      have hGa1 : GoodDart S (L[a.1 + 1]'ha1) := hGood _ (List.getElem_mem ha1)
      have hV : (L[a.1 + 1]'ha1).1 ∈ verts S :=
        (mem_verts_iff_inc_nonempty S _).mpr ⟨(L[a.1 + 1]'ha1).2, hGa1⟩
      have hdegEq : deg S (L[a.1 + 1]'ha1).1 = 2 := deg_eq_two_of_not_branch hdeg2 hV hSa.2.2
      have he1 : (L[a.1]'(by omega)).2 ∈ inc S (L[a.1 + 1]'ha1).1 := by
        have hEq1 : (L[a.1 + 1]'ha1).1 = other (L[a.1]'(by omega)).1 (L[a.1]'(by omega)).2 := by rw [hSa.2.1]; rfl
        rw [hEq1]; exact flip_good hGa
      have hneE : (L[a.1 + 1]'ha1).2 ≠ (L[a.1]'(by omega)).2 := by
        rw [hSa.2.1]
        apply stepDart_snd_ne hGa
        have hEq1 : (L[a.1 + 1]'ha1).1 = other (L[a.1]'(by omega)).1 (L[a.1]'(by omega)).2 := by rw [hSa.2.1]; rfl
        rwa [← hEq1]
      have hPairEq : inc S (L[a.1 + 1]'ha1).1 = {(L[a.1]'(by omega)).2, (L[a.1 + 1]'ha1).2} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact he1
          · rw [Finset.mem_singleton.mp hz']; exact hGa1
        · rw [Finset.card_pair hneE.symm]; exact hdegEq.le
      have hbIn : (L[b.1 + 1]'hb1).2 ∈ inc S (L[a.1 + 1]'ha1).1 := by
        rw [hEqV]; exact hGb
      rw [hPairEq, Finset.mem_insert, Finset.mem_singleton] at hbIn
      rw [List.nodup_iff_injective_getElem] at hnd
      rcases hbIn with hEq1 | hEq2
      · have hFin : (⟨b.1 + 1, by simp; omega⟩ : Fin (L.map Prod.snd).length) =
                    ⟨a.1, by simp; omega⟩ := hnd (by simpa using hEq1)
        have := congrArg Fin.val hFin; simp at this; omega
      · have hFin : (⟨b.1 + 1, by simp; omega⟩ : Fin (L.map Prod.snd).length) =
                    ⟨a.1 + 1, by simp; omega⟩ := hnd (by simpa using hEq2)
        have := congrArg Fin.val hFin; simp at this; omega
    rw [List.nodup_iff_injective_getElem]
    intro a b hab
    by_contra hneAB
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hneAB) with hlt | hgt
    · exact hltCase a b hab hlt
    · exact hltCase b a hab.symm hgt
  constructor
  · rw [hIntEq, List.toFinset_card_of_nodup hTailNodup, List.length_map, List.length_tail, hCardE]
    have hpos : 0 < L.length := List.length_pos_of_ne_nil hne
    omega
  · intro v hv
    rw [hIntEq, List.mem_toFinset, List.mem_map] at hv
    rcases hv with ⟨x, hxTail, rfl⟩
    rcases mem_tail_iff_exists_succ.mp hxTail with ⟨i', hi, rfl⟩
    exact hIncSub i' hi

end Threads

section KernelBFS

variable {m n : ℕ} {G : BipGraph m n}

def branchDarts (S : Finset (GEdge G)) : Finset (Dart m n G) :=
  ((branchVerts S) ×ˢ S).filter (fun d => endL d.2 = d.1 ∨ endR d.2 = d.1)

lemma mem_branchDarts_iff (S : Finset (GEdge G)) (d : Dart m n G) :
    d ∈ branchDarts S ↔ GoodDart S d ∧ d.1 ∈ branchVerts S := by
  simp only [branchDarts, GoodDart, inc, Finset.mem_filter, Finset.mem_product]
  tauto

noncomputable def threads (S : Finset (GEdge G)) : Finset (Finset (GEdge G)) :=
  (branchDarts S).image (threadEdges S)

lemma threads_pairwise_disjoint (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v) :
    (threads S : Set (Finset (GEdge G))).PairwiseDisjoint id := by
  intro t₁ ht₁ t₂ ht₂ hne
  rcases Finset.mem_image.mp ht₁ with ⟨d₁, hd₁, rfl⟩
  rcases Finset.mem_image.mp ht₂ with ⟨d₂, hd₂, rfl⟩
  rcases (mem_branchDarts_iff S d₁).mp hd₁ with ⟨hG1, hB1⟩
  rcases (mem_branchDarts_iff S d₂).mp hd₂ with ⟨hG2, hB2⟩
  change Disjoint _ _
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  rcases threadEdges_inter_eq_or_rev S hdeg2 hG1 hB1 hG2 hB2 he₁ he₂ with rfl | rfl
  · exact hne rfl
  · exact hne (threadEdges_revDart S hdeg2 d₂ hG2 hB2)

lemma threads_internals_pairwise_disjoint (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v) :
    (threads S : Set (Finset (GEdge G))).PairwiseDisjoint (fun t => verts t \ branchVerts S) := by
  intro t₁ ht₁ t₂ ht₂ hne
  rcases Finset.mem_image.mp ht₁ with ⟨d₁, hd₁, rfl⟩
  rcases Finset.mem_image.mp ht₂ with ⟨d₂, hd₂, rfl⟩
  rcases (mem_branchDarts_iff S d₁).mp hd₁ with ⟨hG1, hB1⟩
  rcases (mem_branchDarts_iff S d₂).mp hd₂ with ⟨hG2, hB2⟩
  change Disjoint _ _
  rw [Finset.disjoint_left]
  intro v hv₁ hv₂
  have hsub1 := (thread_internal_props S hdeg2 d₁ hG1 hB1).2 v hv₁
  have hv2T : v ∈ verts (threadEdges S d₂) := (Finset.mem_sdiff.mp hv₂).1
  rcases (mem_verts_iff_inc_nonempty _ v).mp hv2T with ⟨e, he⟩
  rcases Finset.mem_filter.mp he with ⟨he2, hev⟩
  have heS : e ∈ S := threadEdges_subset S hdeg2 d₂ hG2 he2
  have he1 : e ∈ threadEdges S d₁ := hsub1 (Finset.mem_filter.mpr ⟨heS, hev⟩)
  exact Finset.disjoint_left.mp (threads_pairwise_disjoint S hdeg2 ht₁ ht₂ hne) he1 he2

lemma lift_ex_eq (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (T' : Finset (Finset (GEdge G))) (hT' : T' ⊆ threads S) :
    let D := T'.biUnion id
    D ⊆ S ∧
    ex D = (T'.card : ℤ) - ((verts D ∩ branchVerts S).card : ℤ) ∧
    ex S - (T'.card : ℤ) ≤ ex (S \ D) := by
  intro D
  have hDsub : D ⊆ S := by
    intro e he
    rcases Finset.mem_biUnion.mp he with ⟨t, htT', het⟩
    rcases Finset.mem_image.mp (hT' htT') with ⟨d, hd, rfl⟩
    exact threadEdges_subset S hdeg2 d ((mem_branchDarts_iff S d).mp hd).1 het
  have hDisjE : (T' : Set (Finset (GEdge G))).PairwiseDisjoint id :=
    (threads_pairwise_disjoint S hdeg2).subset (by exact_mod_cast hT')
  have hDisjI : (T' : Set (Finset (GEdge G))).PairwiseDisjoint (fun t => verts t \ branchVerts S) :=
    (threads_internals_pairwise_disjoint S hdeg2).subset (by exact_mod_cast hT')
  have hCardD : D.card = ∑ t ∈ T', t.card := Finset.card_biUnion hDisjE
  have hIntEq : verts D \ branchVerts S = T'.biUnion (fun t => verts t \ branchVerts S) := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, D]
    constructor
    · rintro ⟨hvD, hvNotB⟩
      rcases (mem_verts_iff_inc_nonempty _ v).mp hvD with ⟨e, he⟩
      rcases Finset.mem_filter.mp he with ⟨heD, hev⟩
      rcases Finset.mem_biUnion.mp heD with ⟨t, htT', het⟩
      refine ⟨t, htT', ?_, hvNotB⟩
      exact (mem_verts_iff_inc_nonempty _ v).mpr ⟨e, Finset.mem_filter.mpr ⟨het, hev⟩⟩
    · rintro ⟨t, htT', hvt, hvNotB⟩
      exact ⟨verts_mono (Finset.subset_biUnion_of_mem id htT') hvt, hvNotB⟩
  have hCardInt : (verts D \ branchVerts S).card = ∑ t ∈ T', (verts t \ branchVerts S).card := by
    rw [hIntEq]
    exact Finset.card_biUnion hDisjI
  have hSumDiff : (verts D \ branchVerts S).card + T'.card = D.card := by
    rw [hCardInt, hCardD, show T'.card = ∑ _t ∈ T', 1 by simp, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t htT'
    rcases Finset.mem_image.mp (hT' htT') with ⟨d, hd, rfl⟩
    rcases (mem_branchDarts_iff S d).mp hd with ⟨hGd, hBd⟩
    exact (thread_internal_props S hdeg2 d hGd hBd).1
  have hSplitV : (verts D).card = (verts D ∩ branchVerts S).card + (verts D \ branchVerts S).card := by
    rw [Finset.card_inter_add_card_sdiff]
  have hDisjSD : Disjoint (verts (S \ D)) (verts D \ branchVerts S) := by
    rw [Finset.disjoint_left]
    intro v hvSD hvInt
    rw [hIntEq, Finset.mem_biUnion] at hvInt
    rcases hvInt with ⟨t, htT', hvt⟩
    rcases Finset.mem_image.mp (hT' htT') with ⟨d, hd, rfl⟩
    rcases (mem_branchDarts_iff S d).mp hd with ⟨hGd, hBd⟩
    have hIncSub := (thread_internal_props S hdeg2 d hGd hBd).2 v hvt
    rcases (mem_verts_iff_inc_nonempty _ v).mp hvSD with ⟨e, he⟩
    rcases Finset.mem_filter.mp he with ⟨heSD, hev⟩
    rcases Finset.mem_sdiff.mp heSD with ⟨heS, heNotD⟩
    have heT : e ∈ threadEdges S d := hIncSub (Finset.mem_filter.mpr ⟨heS, hev⟩)
    exact heNotD (Finset.mem_biUnion.mpr ⟨threadEdges S d, htT', heT⟩)
  have hSubVS : verts (S \ D) ∪ (verts D \ branchVerts S) ⊆ verts S :=
    Finset.union_subset (verts_mono Finset.sdiff_subset)
      (Finset.sdiff_subset.trans (verts_mono hDsub))
  have hCardVSD : (verts (S \ D)).card + (verts D \ branchVerts S).card ≤ (verts S).card := by
    rw [← Finset.card_union_of_disjoint hDisjSD]
    exact Finset.card_le_card hSubVS
  have hCardSD : (S \ D).card = S.card - D.card := Finset.card_sdiff_of_subset hDsub
  have hDleS : D.card ≤ S.card := Finset.card_le_card hDsub
  refine ⟨hDsub, ?_, ?_⟩
  · simp only [ex]; omega
  · simp only [ex]; omega

noncomputable def bfsV (S : Finset (GEdge G)) (r : Vert m n) : ℕ → Finset (Vert m n)
  | 0 => {r}
  | k + 1 =>
    bfsV S r k ∪
      (branchVerts S).filter (fun w => w ∉ bfsV S r k ∧
        ∃ d ∈ branchDarts S, d.1 ∈ bfsV S r k ∧ (revDart S d).1 = w)

lemma bfsV_mono (S : Finset (GEdge G)) (r : Vert m n) :
    ∀ {a b : ℕ}, a ≤ b → bfsV S r a ⊆ bfsV S r b := by
  intro a b hab
  induction hab with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans Finset.subset_union_left

lemma bfsV_subset_branch (S : Finset (GEdge G)) {r : Vert m n} (hr : r ∈ branchVerts S) :
    ∀ k, bfsV S r k ⊆ branchVerts S := by
  intro k
  induction k with
  | zero => exact Finset.singleton_subset_iff.mpr hr
  | succ k ih => exact Finset.union_subset ih (Finset.filter_subset _ _)

lemma mem_bfsV_zero (S : Finset (GEdge G)) (r : Vert m n) :
    ∀ k, r ∈ bfsV S r k :=
  fun k => bfsV_mono S r (Nat.zero_le k) (Finset.mem_singleton_self r)

noncomputable def birth (S : Finset (GEdge G)) (r w : Vert m n) : ℕ :=
  letI := Classical.propDecidable
  if h : ∃ j, w ∈ bfsV S r (j + 1) then Nat.find h else 0

lemma birth_spec (S : Finset (GEdge G)) (r : Vert m n) {k : ℕ} {w : Vert m n}
    (hw : w ∈ bfsV S r k) (hne : w ≠ r) :
    birth S r w < k ∧
    w ∈ bfsV S r (birth S r w + 1) ∧
    w ∉ bfsV S r (birth S r w) := by
  classical
  have hex : ∃ j, w ∈ bfsV S r (j + 1) := by
    cases k with
    | zero => exact (hne (Finset.mem_singleton.mp hw)).elim
    | succ k' => exact ⟨k', hw⟩
  have hdef : birth S r w = Nat.find hex := by
    unfold birth
    split_ifs
    convert rfl
  rw [hdef]
  have hIn : w ∈ bfsV S r (Nat.find hex + 1) := Nat.find_spec hex
  have hlt : Nat.find hex < k := by
    cases k with
    | zero => exact (hne (Finset.mem_singleton.mp hw)).elim
    | succ k' =>
      have hle : Nat.find hex ≤ k' := Nat.find_min' hex hw
      omega
  have hOut : w ∉ bfsV S r (Nat.find hex) := by
    cases h0 : Nat.find hex with
    | zero => simpa [bfsV] using hne
    | succ j' =>
      have hmin := Nat.find_min hex (show j' < Nat.find hex by omega)
      exact hmin
  exact ⟨hlt, hIn, hOut⟩

lemma exists_parentDart (S : Finset (GEdge G)) (r : Vert m n) {k : ℕ} {w : Vert m n}
    (hw : w ∈ bfsV S r k) (hne : w ≠ r) :
    ∃ d ∈ branchDarts S, d.1 ∈ bfsV S r (birth S r w) ∧ (revDart S d).1 = w := by
  rcases birth_spec S r hw hne with ⟨_, hIn, hOut⟩
  unfold bfsV at hIn
  rcases Finset.mem_union.mp hIn with hOld | hNew
  · exact (hOut hOld).elim
  · exact (Finset.mem_filter.mp hNew).2.2

noncomputable def parentThread (S : Finset (GEdge G)) (r w : Vert m n) : Finset (GEdge G) :=
  letI := Classical.propDecidable
  if h : ∃ d ∈ branchDarts S, d.1 ∈ bfsV S r (birth S r w) ∧ (revDart S d).1 = w then
    threadEdges S h.choose
  else ∅

noncomputable def parentVert (S : Finset (GEdge G)) (r w : Vert m n) : Vert m n :=
  letI := Classical.propDecidable
  if h : ∃ d ∈ branchDarts S, d.1 ∈ bfsV S r (birth S r w) ∧ (revDart S d).1 = w then
    h.choose.1
  else r

lemma parent_spec (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (r : Vert m n) {k : ℕ} {w : Vert m n} (hw : w ∈ bfsV S r k) (hne : w ≠ r) :
    parentThread S r w ∈ threads S ∧
    parentVert S r w ∈ bfsV S r (birth S r w) ∧
    verts (parentThread S r w) ∩ branchVerts S = {parentVert S r w, w} := by
  have hex := exists_parentDart S r hw hne
  have hPT : parentThread S r w = threadEdges S hex.choose := by
    unfold parentThread
    split_ifs
    rfl
  have hPV : parentVert S r w = hex.choose.1 := by
    unfold parentVert
    split_ifs
    rfl
  rcases hex.choose_spec with ⟨hdBD, hdIn, hdRev⟩
  rcases (mem_branchDarts_iff S hex.choose).mp hdBD with ⟨hGd, hBd⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hPT]; exact Finset.mem_image.mpr ⟨hex.choose, hdBD, rfl⟩
  · rw [hPV]; exact hdIn
  · rw [hPT, hPV, verts_threadEdges_inter_branch S hdeg2 hex.choose hGd hBd, hdRev]

lemma parentThread_injOn (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (r : Vert m n) (k : ℕ) :
    Set.InjOn (parentThread S r) (((bfsV S r k).erase r : Finset (Vert m n)) : Set (Vert m n)) := by
  intro w₁ hw₁ w₂ hw₂ hEq
  rcases Finset.mem_erase.mp hw₁ with ⟨hne₁, hV₁⟩
  rcases Finset.mem_erase.mp hw₂ with ⟨hne₂, hV₂⟩
  rcases birth_spec S r hV₁ hne₁ with ⟨_, hIn₁, hOut₁⟩
  rcases birth_spec S r hV₂ hne₂ with ⟨_, hIn₂, hOut₂⟩
  rcases parent_spec S hdeg2 r hV₁ hne₁ with ⟨_, hPV₁, hEnds₁⟩
  rcases parent_spec S hdeg2 r hV₂ hne₂ with ⟨_, hPV₂, hEnds₂⟩
  have hSetEq : ({parentVert S r w₁, w₁} : Finset (Vert m n)) = {parentVert S r w₂, w₂} := by
    rw [← hEnds₁, ← hEnds₂, hEq]
  have hMem1 : w₁ ∈ ({parentVert S r w₂, w₂} : Finset (Vert m n)) := by
    rw [← hSetEq]; simp
  have hMem2 : w₂ ∈ ({parentVert S r w₁, w₁} : Finset (Vert m n)) := by
    rw [hSetEq]; simp
  rcases lt_trichotomy (birth S r w₁) (birth S r w₂) with hlt | heqB | hgt
  · have hIn1' : w₁ ∈ bfsV S r (birth S r w₂) := bfsV_mono S r (by omega) hIn₁
    have hPV1' : parentVert S r w₁ ∈ bfsV S r (birth S r w₂) := bfsV_mono S r (by omega) hPV₁
    rcases Finset.mem_insert.mp hMem2 with h | h
    · exact (hOut₂ (h ▸ hPV1')).elim
    · exact (hOut₂ (Finset.mem_singleton.mp h ▸ hIn1')).elim
  · rcases Finset.mem_insert.mp hMem1 with h | h
    · rw [heqB] at hOut₁
      exact (hOut₁ (h ▸ hPV₂)).elim
    · exact Finset.mem_singleton.mp h
  · have hIn2' : w₂ ∈ bfsV S r (birth S r w₁) := bfsV_mono S r (by omega) hIn₂
    have hPV2' : parentVert S r w₂ ∈ bfsV S r (birth S r w₁) := bfsV_mono S r (by omega) hPV₂
    rcases Finset.mem_insert.mp hMem1 with h | h
    · exact (hOut₁ (h ▸ hPV2')).elim
    · exact (hOut₁ (Finset.mem_singleton.mp h ▸ hIn2')).elim

noncomputable def bfsE (S : Finset (GEdge G)) (r : Vert m n) (k : ℕ) : Finset (Finset (GEdge G)) :=
  ((bfsV S r k).erase r).image (parentThread S r)

lemma bfsE_card (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (r : Vert m n) (k : ℕ) :
    (bfsE S r k).card + 1 = (bfsV S r k).card := by
  rw [bfsE, Finset.card_image_of_injOn (parentThread_injOn S hdeg2 r k),
      Finset.card_erase_add_one (mem_bfsV_zero S r k)]

noncomputable def bfsPath (S : Finset (GEdge G)) (r : Vert m n) :
    ℕ → Vert m n → Finset (Finset (GEdge G))
  | 0, _ => ∅
  | k + 1, w =>
    if w = r then ∅
    else if w ∈ bfsV S r (k + 1) then
      insert (parentThread S r w) (bfsPath S r k (parentVert S r w))
    else ∅

lemma bfsPath_props (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (r : Vert m n) :
    ∀ k w, w ∈ bfsV S r k →
      bfsPath S r k w ⊆ bfsE S r k ∧
      (bfsPath S r k w).card ≤ k ∧
      ∀ v ∈ (verts ((bfsPath S r k w).biUnion id) ∩ branchVerts S ∪ {w}).erase r,
        parentThread S r v ∈ bfsPath S r k w := by
  intro k
  induction k with
  | zero =>
    intro w hw
    have hwr : w = r := Finset.mem_singleton.mp hw
    subst hwr
    refine ⟨Finset.empty_subset _, by simp [bfsPath], ?_⟩
    intro v hv
    simp [bfsPath, verts_empty] at hv
  | succ k ih =>
    intro w hw
    by_cases hwr : w = r
    · subst hwr
      refine ⟨by simp [bfsPath], by simp [bfsPath], ?_⟩
      intro v hv
      simp [bfsPath, verts_empty] at hv
    · have hPath : bfsPath S r (k + 1) w =
          insert (parentThread S r w) (bfsPath S r k (parentVert S r w)) := by
        simp [bfsPath, hwr, hw]
      rcases birth_spec S r hw hwr with ⟨hbLt, _, _⟩
      rcases parent_spec S hdeg2 r hw hwr with ⟨_, hPVin, hEnds⟩
      have hPVk : parentVert S r w ∈ bfsV S r k := bfsV_mono S r (by omega) hPVin
      rcases ih (parentVert S r w) hPVk with ⟨ihSub, ihCard, ihCov⟩
      have hEmono : bfsE S r k ⊆ bfsE S r (k + 1) :=
        Finset.image_subset_image (Finset.erase_subset_erase r (bfsV_mono S r (Nat.le_succ k)))
      have hPTmem : parentThread S r w ∈ bfsE S r (k + 1) :=
        Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hwr, hw⟩, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [hPath]
        exact Finset.insert_subset hPTmem (ihSub.trans hEmono)
      · rw [hPath]
        have := Finset.card_insert_le (parentThread S r w) (bfsPath S r k (parentVert S r w))
        omega
      · intro v hv
        rw [hPath]
        rcases Finset.mem_erase.mp hv with ⟨hvr, hvU⟩
        rw [hPath, Finset.biUnion_insert, id_eq, verts_union, Finset.union_inter_distrib_right,
            hEnds] at hvU
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hvU
        rcases hvU with ((rfl | rfl) | hvOld) | rfl
        · exact Finset.mem_insert_of_mem (ihCov (parentVert S r w)
            (Finset.mem_erase.mpr ⟨hvr, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩))
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (ihCov v
            (Finset.mem_erase.mpr ⟨hvr, Finset.mem_union_left _ hvOld⟩))
        · exact Finset.mem_insert_self _ _

noncomputable def ballThreads (S : Finset (GEdge G)) (r : Vert m n) (k : ℕ) :
    Finset (Finset (GEdge G)) :=
  (threads S).filter (fun t => verts t ∩ branchVerts S ⊆ bfsV S r k)

lemma bfsE_subset_ballThreads (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (r : Vert m n) (k : ℕ) :
    bfsE S r k ⊆ ballThreads S r k := by
  intro t ht
  rcases Finset.mem_image.mp ht with ⟨w, hw, rfl⟩
  rcases Finset.mem_erase.mp hw with ⟨hwr, hwV⟩
  rcases birth_spec S r hwV hwr with ⟨hbLt, _, _⟩
  rcases parent_spec S hdeg2 r hwV hwr with ⟨hMemT, hPVin, hEnds⟩
  refine Finset.mem_filter.mpr ⟨hMemT, ?_⟩
  rw [hEnds]
  exact Finset.insert_subset (bfsV_mono S r (by omega) hPVin) (Finset.singleton_subset_iff.mpr hwV)

lemma ballThreads_mono (S : Finset (GEdge G)) (r : Vert m n) (k : ℕ) :
    ballThreads S r k ⊆ ballThreads S r (k + 1) := by
  intro t ht
  rcases Finset.mem_filter.mp ht with ⟨htT, hsub⟩
  exact Finset.mem_filter.mpr ⟨htT, hsub.trans (bfsV_mono S r (Nat.le_succ k))⟩

lemma surplus_mono (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    (r : Vert m n) (k : ℕ) :
    ballThreads S r k \ bfsE S r k ⊆ ballThreads S r (k + 1) \ bfsE S r (k + 1) := by
  intro t ht
  rcases Finset.mem_sdiff.mp ht with ⟨htB, htNotE⟩
  refine Finset.mem_sdiff.mpr ⟨ballThreads_mono S r k htB, ?_⟩
  intro htE1
  rcases Finset.mem_image.mp htE1 with ⟨w, hw, rfl⟩
  rcases Finset.mem_erase.mp hw with ⟨hwr, hwV1⟩
  by_cases hwVk : w ∈ bfsV S r k
  · exact htNotE (Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hwr, hwVk⟩, rfl⟩)
  · rcases parent_spec S hdeg2 r hwV1 hwr with ⟨_, _, hEnds⟩
    have hsub := (Finset.mem_filter.mp htB).2
    rw [hEnds] at hsub
    exact hwVk (hsub (by simp))

lemma bfs_doubling (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    {r : Vert m n} (hr : r ∈ branchVerts S) (k : ℕ)
    (hSur : (ballThreads S r (k + 1) \ bfsE S r (k + 1)).card ≤ 1) :
    2 * (bfsV S r k).card ≤ (bfsV S r (k + 1)).card := by
  let Dk := (branchDarts S).filter (fun d => d.1 ∈ bfsV S r k)
  let Din := Dk.filter (fun d => (revDart S d).1 ∈ bfsV S r k)
  let Dcut := Dk.filter (fun d => (revDart S d).1 ∉ bfsV S r k)
  have hDkCard : 3 * (bfsV S r k).card ≤ Dk.card := by
    have hFib : Dk.card = ∑ v ∈ bfsV S r k, (Dk.filter (fun d => d.1 = v)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext d
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        constructor
        · intro hd; exact ⟨d.1, (Finset.mem_filter.mp hd).2, hd, rfl⟩
        · rintro ⟨_, _, hd, _⟩; exact hd
      · intro a _ b _ hab
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro d h1 h2
        exact hab ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    rw [hFib]
    calc 3 * (bfsV S r k).card = ∑ _v ∈ bfsV S r k, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ bfsV S r k, (Dk.filter (fun d => d.1 = v)).card := by
        apply Finset.sum_le_sum
        intro v hv
        have hvB : v ∈ branchVerts S := bfsV_subset_branch S hr k hv
        have hdeg3 : 3 ≤ deg S v := (Finset.mem_filter.mp hvB).2
        have hEqCard : (Dk.filter (fun d => d.1 = v)).card = deg S v := by
          unfold deg
          have hImg : (Dk.filter (fun d => d.1 = v)).image Prod.snd = inc S v := by
            ext e
            simp only [Finset.mem_image, Finset.mem_filter, Dk, mem_branchDarts_iff, GoodDart]
            constructor
            · rintro ⟨d, ⟨⟨⟨heInc, _⟩, _⟩, rfl⟩, rfl⟩; exact heInc
            · intro heInc
              exact ⟨(v, e), ⟨⟨⟨heInc, hvB⟩, hv⟩, rfl⟩, rfl⟩
          rw [← hImg, Finset.card_image_of_injOn]
          intro a ha b hb hab
          exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) hab
        omega
  have hSplitD : Dk.card = Din.card + Dcut.card := by
    have hU : Din ∪ Dcut = Dk := by
      ext d; simp only [Din, Dcut, Finset.mem_union, Finset.mem_filter]; tauto
    have hDisj : Disjoint Din Dcut := by
      rw [Finset.disjoint_left]
      intro d h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    rw [← hU, Finset.card_union_of_disjoint hDisj]
  have hDinCard : Din.card = 2 * (ballThreads S r k).card := by
    have hPart : Din.card =
        ∑ t ∈ ballThreads S r k, (Din.filter (fun d => threadEdges S d = t)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext d
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        constructor
        · intro hd
          rcases Finset.mem_filter.mp hd with ⟨hdDk, hrevIn⟩
          rcases Finset.mem_filter.mp hdDk with ⟨hdBD, hdIn⟩
          rcases (mem_branchDarts_iff S d).mp hdBD with ⟨hGd, hBd⟩
          refine ⟨threadEdges S d, ?_, hd, rfl⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨d, hdBD, rfl⟩, ?_⟩
          rw [verts_threadEdges_inter_branch S hdeg2 d hGd hBd]
          exact Finset.insert_subset hdIn (Finset.singleton_subset_iff.mpr hrevIn)
        · rintro ⟨_, _, hd, _⟩; exact hd
      · intro t₁ _ t₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro d h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    rw [hPart]
    have hFib2 : ∀ t ∈ ballThreads S r k, (Din.filter (fun d => threadEdges S d = t)).card = 2 := by
      intro t ht
      rcases Finset.mem_filter.mp ht with ⟨htT, htSub⟩
      rcases Finset.mem_image.mp htT with ⟨d, hdBD, rfl⟩
      rcases (mem_branchDarts_iff S d).mp hdBD with ⟨hGd, hBd⟩
      have hEnds := verts_threadEdges_inter_branch S hdeg2 d hGd hBd
      rw [hEnds] at htSub
      have hdIn : d.1 ∈ bfsV S r k := htSub (by simp)
      have hrIn : (revDart S d).1 ∈ bfsV S r k := htSub (by simp)
      have hrg := revDart_good S hdeg2 d hGd hBd
      have hrevBD : revDart S d ∈ branchDarts S := (mem_branchDarts_iff S _).mpr hrg
      have hSetEq : Din.filter (fun x => threadEdges S x = threadEdges S d) = {d, revDart S d} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hxDin, hxEq⟩
          have hxBD : x ∈ branchDarts S := (Finset.mem_filter.mp (Finset.mem_filter.mp hxDin).1).1
          rcases (mem_branchDarts_iff S x).mp hxBD with ⟨hGx, hBx⟩
          have hmem : x.2 ∈ threadEdges S d := by rw [← hxEq]; exact mem_threadEdges_self S x
          exact threadEdges_inter_eq_or_rev S hdeg2 hGx hBx hGd hBd (mem_threadEdges_self S x) hmem
        · rintro (rfl | rfl)
          · exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hdBD, hdIn⟩, hrIn⟩, rfl⟩
          · refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hrevBD, hrIn⟩, ?_⟩,
              threadEdges_revDart S hdeg2 d hGd hBd⟩
            rw [revDart_invol S hdeg2 d hGd hBd]
            exact hdIn
      rw [hSetEq, Finset.card_pair (revDart_ne S hdeg2 d hGd hBd).symm]
    rw [Finset.sum_congr rfl hFib2]
    simp [Nat.mul_comm]
  have hDcutLe : Dcut.card ≤ (ballThreads S r (k + 1) \ ballThreads S r k).card := by
    have hImgSub : Dcut.image (threadEdges S) ⊆ ballThreads S r (k + 1) \ ballThreads S r k := by
      intro t ht
      rcases Finset.mem_image.mp ht with ⟨d, hd, rfl⟩
      rcases Finset.mem_filter.mp hd with ⟨hdDk, hrevOut⟩
      rcases Finset.mem_filter.mp hdDk with ⟨hdBD, hdIn⟩
      rcases (mem_branchDarts_iff S d).mp hdBD with ⟨hGd, hBd⟩
      have hrg := revDart_good S hdeg2 d hGd hBd
      have hEnds := verts_threadEdges_inter_branch S hdeg2 d hGd hBd
      have hrevIn1 : (revDart S d).1 ∈ bfsV S r (k + 1) := by
        unfold bfsV
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hrg.2, hrevOut, d, hdBD, hdIn, rfl⟩)
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨d, hdBD, rfl⟩, ?_⟩
        rw [hEnds]
        exact Finset.insert_subset (bfsV_mono S r (Nat.le_succ k) hdIn)
          (Finset.singleton_subset_iff.mpr hrevIn1)
      · intro hInOld
        have hsub := (Finset.mem_filter.mp hInOld).2
        rw [hEnds] at hsub
        exact hrevOut (hsub (by simp))
    have hInj : Set.InjOn (threadEdges S) (Dcut : Set (Dart m n G)) := by
      intro a ha b hb hEq
      rcases Finset.mem_filter.mp ha with ⟨haDk, haRevOut⟩
      rcases Finset.mem_filter.mp haDk with ⟨haBD, haIn⟩
      rcases Finset.mem_filter.mp hb with ⟨hbDk, _⟩
      rcases Finset.mem_filter.mp hbDk with ⟨hbBD, hbIn⟩
      rcases (mem_branchDarts_iff S a).mp haBD with ⟨hGa, hBa⟩
      rcases (mem_branchDarts_iff S b).mp hbBD with ⟨hGb, hBb⟩
      have hmem : a.2 ∈ threadEdges S b := by rw [← hEq]; exact mem_threadEdges_self S a
      rcases threadEdges_inter_eq_or_rev S hdeg2 hGa hBa hGb hBb (mem_threadEdges_self S a) hmem
        with h1 | h2
      · exact h1
      · have hRevA : revDart S a = b := by
          rw [h2, revDart_invol S hdeg2 b hGb hBb]
        rw [hRevA] at haRevOut
        exact (haRevOut hbIn).elim
    calc Dcut.card = (Dcut.image (threadEdges S)).card := (Finset.card_image_of_injOn hInj).symm
      _ ≤ (ballThreads S r (k + 1) \ ballThreads S r k).card := Finset.card_le_card hImgSub
  have hBTk : (ballThreads S r k).card = (bfsE S r k).card + (ballThreads S r k \ bfsE S r k).card := by
    rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_right,
        Finset.union_sdiff_of_subset (bfsE_subset_ballThreads S hdeg2 r k)]
  have hBTk1 : (ballThreads S r (k + 1)).card =
      (bfsE S r (k + 1)).card + (ballThreads S r (k + 1) \ bfsE S r (k + 1)).card := by
    rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_right,
        Finset.union_sdiff_of_subset (bfsE_subset_ballThreads S hdeg2 r (k + 1))]
  have hDiff : (ballThreads S r (k + 1) \ ballThreads S r k).card =
      (ballThreads S r (k + 1)).card - (ballThreads S r k).card :=
    Finset.card_sdiff_of_subset (ballThreads_mono S r k)
  have hBTle : (ballThreads S r k).card ≤ (ballThreads S r (k + 1)).card :=
    Finset.card_le_card (ballThreads_mono S r k)
  have hSurK : (ballThreads S r k \ bfsE S r k).card ≤ 1 :=
    (Finset.card_le_card (surplus_mono S hdeg2 r k)).trans hSur
  have hEk := bfsE_card S hdeg2 r k
  have hEk1 := bfsE_card S hdeg2 r (k + 1)
  omega

lemma bfs_pow_le_card (S : Finset (GEdge G)) (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v)
    {r : Vert m n} (hr : r ∈ branchVerts S) :
    ∀ k, (ballThreads S r k \ bfsE S r k).card ≤ 1 → 2 ^ k ≤ (bfsV S r k).card := by
  intro k
  induction k with
  | zero => intro _; simp [bfsV]
  | succ k ih =>
    intro hSur
    have hSurK : (ballThreads S r k \ bfsE S r k).card ≤ 1 :=
      (Finset.card_le_card (surplus_mono S hdeg2 r k)).trans hSur
    have h1 := ih hSurK
    have h2 := bfs_doubling S hdeg2 hr k hSur
    rw [Nat.pow_succ, Nat.mul_comm]
    omega

lemma exists_small_dense_lift (S : Finset (GEdge G))
    (hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v) (hpos : 0 < ex S) :
    ∃ D ⊆ S,
      dense D ∧
      ex S - ((4 * Nat.clog 2 (2 * (S.card - (verts S).card) + 1) + 2 : ℕ) : ℤ) ≤ ex (S \ D) := by
  rcases branchVerts_card_bounds hdeg2 hpos with ⟨hBpos, hBle⟩
  rcases Finset.card_pos.mp hBpos with ⟨r, hr⟩
  set k := Nat.clog 2 ((branchVerts S).card + 1)
  have h2k : (branchVerts S).card + 1 ≤ 2 ^ k := Nat.le_pow_clog (by omega) _
  have hSur2 : 2 ≤ (ballThreads S r k \ bfsE S r k).card := by
    by_contra hlt
    have hle1 : (ballThreads S r k \ bfsE S r k).card ≤ 1 := by omega
    have hpow := bfs_pow_le_card S hdeg2 hr k hle1
    have hVle : (bfsV S r k).card ≤ (branchVerts S).card :=
      Finset.card_le_card (bfsV_subset_branch S hr k)
    omega
  rcases Finset.one_lt_card.mp (by omega : 1 < (ballThreads S r k \ bfsE S r k).card)
    with ⟨t₁, ht₁, t₂, ht₂, ht12⟩
  rcases Finset.mem_sdiff.mp ht₁ with ⟨ht₁B, ht₁NotE⟩
  rcases Finset.mem_sdiff.mp ht₂ with ⟨ht₂B, ht₂NotE⟩
  rcases Finset.mem_filter.mp ht₁B with ⟨ht₁T, ht₁Sub⟩
  rcases Finset.mem_filter.mp ht₂B with ⟨ht₂T, ht₂Sub⟩
  rcases Finset.mem_image.mp ht₁T with ⟨d₁, hd₁BD, rfl⟩
  rcases Finset.mem_image.mp ht₂T with ⟨d₂, hd₂BD, rfl⟩
  rcases (mem_branchDarts_iff S d₁).mp hd₁BD with ⟨hGd₁, hBd₁⟩
  rcases (mem_branchDarts_iff S d₂).mp hd₂BD with ⟨hGd₂, hBd₂⟩
  have hE1 := verts_threadEdges_inter_branch S hdeg2 d₁ hGd₁ hBd₁
  have hE2 := verts_threadEdges_inter_branch S hdeg2 d₂ hGd₂ hBd₂
  rw [hE1] at ht₁Sub
  rw [hE2] at ht₂Sub
  let a₁ := d₁.1
  let b₁ := (revDart S d₁).1
  let a₂ := d₂.1
  let b₂ := (revDart S d₂).1
  have ha₁V : a₁ ∈ bfsV S r k := ht₁Sub (by simp [a₁])
  have hb₁V : b₁ ∈ bfsV S r k := ht₁Sub (by simp [b₁])
  have ha₂V : a₂ ∈ bfsV S r k := ht₂Sub (by simp [a₂])
  have hb₂V : b₂ ∈ bfsV S r k := ht₂Sub (by simp [b₂])
  let Ttree := bfsPath S r k a₁ ∪ bfsPath S r k b₁ ∪ bfsPath S r k a₂ ∪ bfsPath S r k b₂
  let T' := insert (threadEdges S d₁) (insert (threadEdges S d₂) Ttree)
  rcases bfsPath_props S hdeg2 r k a₁ ha₁V with ⟨hSubA1, hCardA1, hCovA1⟩
  rcases bfsPath_props S hdeg2 r k b₁ hb₁V with ⟨hSubB1, hCardB1, hCovB1⟩
  rcases bfsPath_props S hdeg2 r k a₂ ha₂V with ⟨hSubA2, hCardA2, hCovA2⟩
  rcases bfsPath_props S hdeg2 r k b₂ hb₂V with ⟨hSubB2, hCardB2, hCovB2⟩
  have hTreeSubE : Ttree ⊆ bfsE S r k :=
    Finset.union_subset (Finset.union_subset (Finset.union_subset hSubA1 hSubB1) hSubA2) hSubB2
  have hT'sub : T' ⊆ threads S := by
    refine Finset.insert_subset ht₁T (Finset.insert_subset ht₂T ?_)
    exact hTreeSubE.trans ((bfsE_subset_ballThreads S hdeg2 r k).trans (Finset.filter_subset _ _))
  have ht₁NotTree : threadEdges S d₁ ∉ Ttree := fun h => ht₁NotE (hTreeSubE h)
  have ht₂NotTree : threadEdges S d₂ ∉ Ttree := fun h => ht₂NotE (hTreeSubE h)
  have hT'card : T'.card = Ttree.card + 2 := by
    rw [Finset.card_insert_of_notMem (by simp [ht12, ht₁NotTree]),
        Finset.card_insert_of_notMem ht₂NotTree]
  have hTreeCardLe : Ttree.card ≤ 4 * k := by
    dsimp only [Ttree]
    have h1 := Finset.card_union_le (bfsPath S r k a₁ ∪ bfsPath S r k b₁ ∪ bfsPath S r k a₂) (bfsPath S r k b₂)
    have h2 := Finset.card_union_le (bfsPath S r k a₁ ∪ bfsPath S r k b₁) (bfsPath S r k a₂)
    have h3 := Finset.card_union_le (bfsPath S r k a₁) (bfsPath S r k b₁)
    omega
  let D := T'.biUnion id
  rcases lift_ex_eq S hdeg2 T' hT'sub with ⟨hDsub, hDex, hSDex⟩
  have hVsubV : (verts D ∩ branchVerts S) ⊆ bfsV S r k := by
    intro v hv
    rcases Finset.mem_inter.mp hv with ⟨hvD, hvB⟩
    rcases (mem_verts_iff_inc_nonempty _ v).mp hvD with ⟨e, he⟩
    rcases Finset.mem_filter.mp he with ⟨heD, hev⟩
    rcases Finset.mem_biUnion.mp heD with ⟨t, htT', het⟩
    have hvt : v ∈ verts t ∩ branchVerts S :=
      Finset.mem_inter.mpr ⟨(mem_verts_iff_inc_nonempty _ v).mpr ⟨e, Finset.mem_filter.mpr ⟨het, hev⟩⟩, hvB⟩
    rcases Finset.mem_insert.mp htT' with rfl | ht2
    · rw [hE1] at hvt; exact ht₁Sub hvt
    · rcases Finset.mem_insert.mp ht2 with rfl | htTree
      · rw [hE2] at hvt; exact ht₂Sub hvt
      · have htBT := bfsE_subset_ballThreads S hdeg2 r k (hTreeSubE htTree)
        exact (Finset.mem_filter.mp htBT).2 hvt
  have hPTimg : ((verts D ∩ branchVerts S).erase r).image (parentThread S r) ⊆ Ttree := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨v, hv, rfl⟩
    rcases Finset.mem_erase.mp hv with ⟨hvr, hvDB⟩
    rcases Finset.mem_inter.mp hvDB with ⟨hvD, hvB⟩
    rcases (mem_verts_iff_inc_nonempty _ v).mp hvD with ⟨e, he⟩
    rcases Finset.mem_filter.mp he with ⟨heD, hev⟩
    rcases Finset.mem_biUnion.mp heD with ⟨t₀, ht₀T', het₀⟩
    have hvVertT0 : v ∈ verts t₀ :=
      (mem_verts_iff_inc_nonempty _ v).mpr ⟨e, Finset.mem_filter.mpr ⟨het₀, hev⟩⟩
    have hvt₀ : v ∈ verts t₀ ∩ branchVerts S := Finset.mem_inter.mpr ⟨hvVertT0, hvB⟩
    rcases Finset.mem_insert.mp ht₀T' with rfl | ht2
    · rw [hE1] at hvt₀
      rcases Finset.mem_insert.mp hvt₀ with rfl | hmem
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (hCovA1 a₁ (Finset.mem_erase.mpr ⟨hvr, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩))))
      · have hvEq : v = b₁ := Finset.mem_singleton.mp hmem
        subst hvEq
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
          (hCovB1 b₁ (Finset.mem_erase.mpr ⟨hvr, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩))))
    · rcases Finset.mem_insert.mp ht2 with rfl | htTree
      · rw [hE2] at hvt₀
        rcases Finset.mem_insert.mp hvt₀ with rfl | hmem
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (hCovA2 a₂ (Finset.mem_erase.mpr ⟨hvr, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩)))
        · have hvEq : v = b₂ := Finset.mem_singleton.mp hmem
          subst hvEq
          exact Finset.mem_union_right _
            (hCovB2 b₂ (Finset.mem_erase.mpr ⟨hvr, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩))
      · rcases Finset.mem_union.mp htTree with h123 | hB2
        · rcases Finset.mem_union.mp h123 with h12 | hA2
          · rcases Finset.mem_union.mp h12 with hA1 | hB1
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                (hCovA1 v (Finset.mem_erase.mpr ⟨hvr, Finset.mem_union_left _
                  (Finset.mem_inter.mpr ⟨verts_mono (Finset.subset_biUnion_of_mem id hA1) hvVertT0, hvB⟩)⟩))))
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
                (hCovB1 v (Finset.mem_erase.mpr ⟨hvr, Finset.mem_union_left _
                  (Finset.mem_inter.mpr ⟨verts_mono (Finset.subset_biUnion_of_mem id hB1) hvVertT0, hvB⟩)⟩))))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (hCovA2 v (Finset.mem_erase.mpr ⟨hvr, Finset.mem_union_left _
                (Finset.mem_inter.mpr ⟨verts_mono (Finset.subset_biUnion_of_mem id hA2) hvVertT0, hvB⟩)⟩)))
        · exact Finset.mem_union_right _
            (hCovB2 v (Finset.mem_erase.mpr ⟨hvr, Finset.mem_union_left _
              (Finset.mem_inter.mpr ⟨verts_mono (Finset.subset_biUnion_of_mem id hB2) hvVertT0, hvB⟩)⟩))
  have hInjOn : Set.InjOn (parentThread S r) (((verts D ∩ branchVerts S).erase r : Finset (Vert m n)) : Set (Vert m n)) :=
    (parentThread_injOn S hdeg2 r k).mono (by exact_mod_cast Finset.erase_subset_erase r hVsubV)
  have hVcardLe : ((verts D ∩ branchVerts S).erase r).card ≤ Ttree.card := by
    calc ((verts D ∩ branchVerts S).erase r).card
        = (((verts D ∩ branchVerts S).erase r).image (parentThread S r)).card :=
          (Finset.card_image_of_injOn hInjOn).symm
      _ ≤ Ttree.card := Finset.card_le_card hPTimg
  have hDBcardLe : (verts D ∩ branchVerts S).card ≤ Ttree.card + 1 := by
    by_cases hrIn : r ∈ verts D ∩ branchVerts S
    · rw [← Finset.card_erase_add_one hrIn]; omega
    · rw [Finset.erase_eq_of_notMem hrIn] at hVcardLe; omega
  have hDense : dense D := by
    unfold dense
    dsimp only [D] at hDBcardLe ⊢
    simp only [ex] at hDex
    omega
  have hkLe : k ≤ Nat.clog 2 (2 * (S.card - (verts S).card) + 1) :=
    Nat.clog_mono_right 2 (by omega)
  refine ⟨D, hDsub, hDense, ?_⟩
  dsimp only [D]
  omega

end KernelBFS

section PackingAndInversion

variable {m n : ℕ} {G : BipGraph m n}

lemma pack_dense_step (F : Finset (GEdge G)) (d0 : ℕ) (hle : maxEx F ≤ d0) (hpos : 0 < maxEx F) :
    ∃ D ⊆ F,
      dense D ∧
      maxEx (F \ D) < maxEx F ∧
      maxEx F ≤ maxEx (F \ D) + (4 * Nat.clog 2 (2 * d0 + 1) + 2) := by
  rcases exists_min_maximizer F hpos with ⟨S, hSF, hSex, hSub, hMin⟩
  have hdeg2 : ∀ v ∈ verts S, 2 ≤ deg S v := min_deg_ge_two_of_min hMin
  have hSpos : 0 < ex S := by omega
  rcases exists_small_dense_lift S hdeg2 hSpos with ⟨D, hDS, hDense, hSDex⟩
  have hDF : D ⊆ F := hDS.trans hSF
  have hDne : D.Nonempty := by
    by_contra hE
    rw [Finset.not_nonempty_iff_eq_empty] at hE
    subst hE
    simp [dense, verts_empty] at hDense
  have hDrop : maxEx (F \ D) < maxEx F := by
    rcases exists_maxEx_witness (F \ D) with ⟨t, ht, hval⟩
    have htF : t ⊆ F := ht.trans Finset.sdiff_subset
    have hle' : maxEx (F \ D) ≤ maxEx F := maxEx_mono Finset.sdiff_subset
    by_contra hge
    have heq : maxEx (F \ D) = maxEx F := by omega
    have htex : ex t = (maxEx F : ℤ) := by simp only [ex]; omega
    rcases hDne with ⟨e, heD⟩
    have heT : e ∈ t := hSub t htF htex (hDS heD)
    exact (Finset.mem_sdiff.mp (ht heT)).2 heD
  have hSdiff : S.card - (verts S).card = maxEx F := by
    simp only [ex] at hSex; omega
  have hClogMono : Nat.clog 2 (2 * (S.card - (verts S).card) + 1) ≤ Nat.clog 2 (2 * d0 + 1) :=
    Nat.clog_mono_right 2 (by omega)
  have hMaxSD : ex (S \ D) ≤ (maxEx (F \ D) : ℤ) :=
    ex_le_maxEx (Finset.sdiff_subset_sdiff hSF (Finset.Subset.refl D))
  refine ⟨D, hDF, hDense, hDrop, ?_⟩
  omega

lemma pack_dense_loop : ∀ (cur : ℕ) (d0 : ℕ) (F : Finset (GEdge G)),
    maxEx F = cur → maxEx F ≤ d0 →
    ∃ family : Finset (Finset (GEdge G)),
      (∀ s ∈ family, s ⊆ F ∧ dense s) ∧
      (∀ a ∈ family, ∀ b ∈ family, a ≠ b → Disjoint a b) ∧
      maxEx F ≤ family.card * (4 * Nat.clog 2 (2 * d0 + 1) + 2) := by
  intro cur
  induction cur using Nat.strong_induction_on with
  | ind cur ih =>
    intro d0 F hcur hle
    by_cases h0 : cur = 0
    · refine ⟨∅, by simp, by simp, ?_⟩
      omega
    · rcases pack_dense_step F d0 hle (by omega) with ⟨D, hDF, hDense, hDrop, hBound⟩
      rcases ih (maxEx (F \ D)) (by omega) d0 (F \ D) rfl (by omega) with ⟨fam, hFamS, hFamD, hFamB⟩
      have hDnot : D ∉ fam := by
        intro hmem
        have hsub : D ⊆ F \ D := (hFamS D hmem).1
        have hne : D.Nonempty := by
          by_contra hE
          rw [Finset.not_nonempty_iff_eq_empty] at hE
          subst hE; simp [dense, verts_empty] at hDense
        rcases hne with ⟨e, heD⟩
        exact (Finset.mem_sdiff.mp (hsub heD)).2 heD
      refine ⟨insert D fam, ?_, ?_, ?_⟩
      · intro s hs
        rcases Finset.mem_insert.mp hs with rfl | hsf
        · exact ⟨hDF, hDense⟩
        · exact ⟨(hFamS s hsf).1.trans Finset.sdiff_subset, (hFamS s hsf).2⟩
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with rfl | haf <;>
        rcases Finset.mem_insert.mp hb with rfl | hbf
        · exact (hab rfl).elim
        · exact Finset.disjoint_of_subset_right (hFamS b hbf).1 disjoint_sdiff_self_right
        · exact Finset.disjoint_of_subset_left (hFamS a haf).1 disjoint_sdiff_self_left
        · exact hFamD a haf b hbf hab
      · rw [Finset.card_insert_of_notMem hDnot, Nat.add_mul, Nat.one_mul]
        omega

lemma two_mul_le_two_pow : ∀ k : ℕ, 4 ≤ k → 2 * k ≤ 2 ^ k := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk4 : k < 4
    · have hk3 : k = 3 := by omega
      subst hk3; decide
    · have h := ih (by omega)
      have hpos : 2 ≤ 2 ^ k := by
        have := Nat.one_le_pow k 2 (by omega)
        omega
      rw [Nat.pow_succ, Nat.mul_comm]
      omega

lemma invert_clog_bound (d p : ℕ)
    (h : d ≤ p * (4 * Nat.clog 2 (2 * d + 1) + 2)) :
    d ≤ 56 * p * Nat.clog 2 (p + 2) := by
  by_cases hp0 : p = 0
  · subst hp0; simp at h; omega
  · by_cases hd0 : d = 0
    · subst hd0; simp
    · set L := Nat.clog 2 (p + 2)
      have hL2 : 2 ≤ L := by
        have h1 : 1 < L := (Nat.lt_clog_iff_pow_lt (hb := by omega)).mpr (by omega)
        omega
      have hpPow : p + 2 ≤ 2 ^ L := Nat.le_pow_clog (by omega) _
      set c := Nat.clog 2 (d + 2)
      have hc2 : 2 ≤ c := by
        have h1 : 1 < c := (Nat.lt_clog_iff_pow_lt (hb := by omega)).mpr (by omega)
        omega
      have h2d : Nat.clog 2 (2 * d + 1) ≤ c + 1 := by
        have h1 : 2 * d + 1 ≤ 2 ^ (c + 1) := by
          have hdPow : d + 2 ≤ 2 ^ c := Nat.le_pow_clog (by omega) _
          rw [Nat.pow_succ]
          omega
        exact Nat.clog_le_of_le_pow h1
      have hdStep : d ≤ 7 * p * c := by
        have hA : 4 * Nat.clog 2 (2 * d + 1) + 2 ≤ 7 * c := by omega
        calc d ≤ p * (4 * Nat.clog 2 (2 * d + 1) + 2) := h
          _ ≤ p * (7 * c) := Nat.mul_le_mul_left p hA
          _ = 7 * p * c := by ring
      have hcLe : c ≤ 8 * L := by
        by_contra hgt
        have hcGe : 2 * L + 10 ≤ c := by omega
        set t := c - L - 4
        have ht4 : 4 ≤ t := by omega
        have h2t : 2 * t ≤ 2 ^ t := two_mul_le_two_pow t ht4
        have hcLt2t : c < 2 ^ t := by omega
        have hPowSplit : 2 ^ (L + 3) * 2 ^ t = 2 ^ (c - 1) := by
          rw [← Nat.pow_add]
          congr 1
          omega
        have hPredLt : 2 ^ (c - 1) < d + 2 := by
          have := Nat.pow_pred_clog_lt_self (b := 2) (x := d + 2) (by omega)
          simpa [Nat.pred_eq_sub_one, c] using this
        have hUpper : d + 2 ≤ 2 ^ (L + 3) * c := by
          have h8 : 2 ^ (L + 3) = 8 * 2 ^ L := by
            rw [Nat.pow_add]; norm_num; ring
          have h2le : 2 ≤ p * c := by
            have : 1 * 2 ≤ p * c := Nat.mul_le_mul (by omega) hc2
            omega
          calc d + 2 ≤ 7 * p * c + p * c := by omega
            _ = 8 * p * c := by ring
            _ ≤ 8 * 2 ^ L * c := by
              have : p ≤ 2 ^ L := by omega
              exact Nat.mul_le_mul_right c (Nat.mul_le_mul_left 8 this)
            _ = 2 ^ (L + 3) * c := by rw [h8]
        have hMulLt : 2 ^ (L + 3) * c < 2 ^ (L + 3) * 2 ^ t :=
          Nat.mul_lt_mul_of_pos_left hcLt2t (Nat.pow_pos (by omega))
        rw [hPowSplit] at hMulLt
        omega
      calc d ≤ 7 * p * c := hdStep
        _ ≤ 7 * p * (8 * L) := Nat.mul_le_mul_left (7 * p) hcLe
        _ = 56 * p * L := by ring

theorem dense_hitting_bound (m n p : ℕ) (G : BipGraph m n)
    (hpack : ∀ family : Finset (Finset (GEdge G)),
      (∀ s ∈ family, (s.image (fun e => e.1.1)).card + (s.image (fun e => e.1.2)).card < s.card) →
      (∀ a ∈ family, ∀ b ∈ family, a ≠ b → Disjoint a b) → family.card ≤ p) :
    ∃ Z : Finset (GEdge G),
      Z.card ≤ 56 * p * Nat.clog 2 (p + 2) ∧
      ∀ s : Finset (GEdge G), Disjoint s Z →
        ¬ ((s.image (fun e => e.1.1)).card + (s.image (fun e => e.1.2)).card < s.card) := by
  let U : Finset (GEdge G) := Finset.univ
  rcases pack_dense_loop (maxEx U) (maxEx U) U rfl (le_refl _) with ⟨fam, hFamS, hFamD, hFamB⟩
  have hFamCard : fam.card ≤ p := hpack fam (fun s hs => (dense_iff s).mp (hFamS s hs).2) hFamD
  have hIn : maxEx U ≤ p * (4 * Nat.clog 2 (2 * maxEx U + 1) + 2) :=
    hFamB.trans (Nat.mul_le_mul_right _ hFamCard)
  have hBound : maxEx U ≤ 56 * p * Nat.clog 2 (p + 2) := invert_clog_bound (maxEx U) p hIn
  rcases hitting_le_maxEx (56 * p * Nat.clog 2 (p + 2)) U hBound with ⟨Z, _, hZcard, hZhit⟩
  refine ⟨Z, hZcard, ?_⟩
  intro s hdisj
  rw [← dense_iff]
  exact hZhit s (Finset.subset_univ s) hdisj

end PackingAndInversion

end Half1

section Half2

open PEqualNP.ProofComplexity PEqualNP.Expanders

lemma isDerivation_mono {V : Type} [DecidableEq V] {F₁ F₂ : Set (Clause V)}
    (hsub : F₁ ⊆ F₂) {π : List (Clause V)} (hπ : IsDerivation F₁ π) :
    IsDerivation F₂ π := by
  induction hπ with
  | nil => exact .nil
  | ax _ hC ih => exact .ax ih (hsub hC)
  | res _ hC hD hR ih => exact .res ih hC hD hR

lemma isDerivation_append {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π₁ π₂ : List (Clause V)} (h₁ : IsDerivation F π₁) (h₂ : IsDerivation F π₂) :
    IsDerivation F (π₁ ++ π₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | ax _ hC ih => exact .ax ih hC
  | res _ hC hD hR ih =>
    exact .res ih (List.mem_append_left _ hC) (List.mem_append_left _ hD) hR

lemma isRefutation_mono {V : Type} [DecidableEq V] {F₁ F₂ : Set (Clause V)}
    (hsub : F₁ ⊆ F₂) {π : List (Clause V)} (hπ : IsRefutation F₁ π) :
    IsRefutation F₂ π :=
  ⟨isDerivation_mono hsub hπ.1, hπ.2⟩

def mapLit {E₁ E₂ : Type} (φ : E₁ → E₂) (l : Literal E₁) : Literal E₂ :=
  (φ l.1, l.2)

def mapClause {E₁ E₂ : Type} [DecidableEq E₂] (φ : E₁ → E₂) (C : Clause E₁) : Clause E₂ :=
  C.image (mapLit φ)

lemma mapLit_injective {E₁ E₂ : Type} {φ : E₁ → E₂} (hφ : Function.Injective φ) :
    Function.Injective (mapLit φ) := by
  intro a b h
  cases a; cases b
  simp only [mapLit, Prod.mk.injEq] at h
  exact Prod.ext (hφ h.1) h.2

lemma mapClause_empty {E₁ E₂ : Type} [DecidableEq E₂] (φ : E₁ → E₂) :
    mapClause φ (∅ : Clause E₁) = ∅ := by
  simp [mapClause]

lemma mapClause_erase {E₁ E₂ : Type} [DecidableEq E₁] [DecidableEq E₂]
    {φ : E₁ → E₂} (hφ : Function.Injective φ) (C : Clause E₁) (l : Literal E₁) :
    (mapClause φ C).erase (mapLit φ l) = mapClause φ (C.erase l) := by
  ext y
  simp only [mapClause, Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hne, a, ha, rfl⟩
    refine ⟨a, ⟨?_, ha⟩, rfl⟩
    intro h; exact hne (congrArg (mapLit φ) h)
  · rintro ⟨a, ⟨hne, ha⟩, rfl⟩
    refine ⟨?_, a, ha, rfl⟩
    intro h; exact hne (mapLit_injective hφ h)

lemma mapClause_union {E₁ E₂ : Type} [DecidableEq E₁] [DecidableEq E₂]
    (φ : E₁ → E₂) (C D : Clause E₁) :
    mapClause φ (C ∪ D) = mapClause φ C ∪ mapClause φ D := by
  simp only [mapClause, Finset.image_union]

lemma not_mem_mapClause_of_ne {E₁ E₂ : Type} [DecidableEq E₂]
    {φ : E₁ → E₂} {x : Literal E₂} (hx : ∀ e, φ e ≠ x.1) (C : Clause E₁) :
    x ∉ mapClause φ C := by
  simp only [mapClause, Finset.mem_image, not_exists, not_and]
  intro l _ hl
  exact hx l.1 (congrArg Prod.fst hl)

lemma isResolvent_lift_opt {E₁ E₂ : Type} [DecidableEq E₁] [DecidableEq E₂]
    {φ : E₁ → E₂} (hφ : Function.Injective φ)
    {x : Literal E₂} (hx : ∀ e, φ e ≠ x.1)
    {C D R : Clause E₁} (hR : IsResolvent C D R)
    {C' D' : Clause E₂}
    (hC' : C' = mapClause φ C ∨ C' = insert x (mapClause φ C))
    (hD' : D' = mapClause φ D ∨ D' = insert x (mapClause φ D)) :
    ∃ R' : Clause E₂, IsResolvent C' D' R' ∧
      (R' = mapClause φ R ∨ R' = insert x (mapClause φ R)) := by
  rcases hR with ⟨v, hvC, hvD, rfl⟩
  have hneT : x ≠ (φ v, true) := fun h => hx v (congrArg Prod.fst h).symm
  have hneF : x ≠ (φ v, false) := fun h => hx v (congrArg Prod.fst h).symm
  have hvC' : (φ v, true) ∈ mapClause φ C :=
    Finset.mem_image.mpr ⟨(v, true), hvC, rfl⟩
  have hvD' : (φ v, false) ∈ mapClause φ D :=
    Finset.mem_image.mpr ⟨(v, false), hvD, rfl⟩
  have hErC : (mapClause φ C).erase (φ v, true) = mapClause φ (C.erase (v, true)) :=
    mapClause_erase hφ C (v, true)
  have hErD : (mapClause φ D).erase (φ v, false) = mapClause φ (D.erase (v, false)) :=
    mapClause_erase hφ D (v, false)
  rcases hC' with rfl | rfl <;> rcases hD' with rfl | rfl
  · refine ⟨mapClause φ (C.erase (v, true) ∪ D.erase (v, false)), ?_, Or.inl rfl⟩
    exact ⟨φ v, hvC', hvD', by rw [hErC, hErD, mapClause_union]⟩
  · refine ⟨insert x (mapClause φ (C.erase (v, true) ∪ D.erase (v, false))), ?_, Or.inr rfl⟩
    refine ⟨φ v, hvC', Finset.mem_insert_of_mem hvD', ?_⟩
    rw [Finset.erase_insert_of_ne hneF, hErC, hErD, mapClause_union, Finset.union_insert]
  · refine ⟨insert x (mapClause φ (C.erase (v, true) ∪ D.erase (v, false))), ?_, Or.inr rfl⟩
    refine ⟨φ v, Finset.mem_insert_of_mem hvC', hvD', ?_⟩
    rw [Finset.erase_insert_of_ne hneT, hErC, hErD, mapClause_union, Finset.insert_union]
  · refine ⟨insert x (mapClause φ (C.erase (v, true) ∪ D.erase (v, false))), ?_, Or.inr rfl⟩
    refine ⟨φ v, Finset.mem_insert_of_mem hvC', Finset.mem_insert_of_mem hvD', ?_⟩
    rw [Finset.erase_insert_of_ne hneT, Finset.erase_insert_of_ne hneF,
        hErC, hErD, mapClause_union, Finset.insert_union, Finset.union_insert, Finset.insert_idem]

lemma countP_not_mem_add_card_le {α : Type} [DecidableEq α]
    (l : List α) (H : Finset α) (hH : ∀ a ∈ H, a ∈ l) :
    l.countP (fun a => decide (a ∉ H)) + H.card ≤ l.length := by
  induction l generalizing H with
  | nil =>
    have hEmpty : H = ∅ := by
      ext a
      simp only [Finset.notMem_empty, iff_false]
      intro ha
      exact List.not_mem_nil (hH a ha)
    subst hEmpty
    simp
  | cons x xs ih =>
    by_cases hx : x ∈ H
    · have hsub : ∀ a ∈ H.erase x, a ∈ xs := by
        intro a ha
        rcases Finset.mem_erase.mp ha with ⟨hne, haH⟩
        rcases List.mem_cons.mp (hH a haH) with rfl | hxs
        · exact (hne rfl).elim
        · exact hxs
      have h1 := ih (H.erase x) hsub
      have hle : xs.countP (fun a => decide (a ∉ H)) ≤
          xs.countP (fun a => decide (a ∉ H.erase x)) := by
        apply List.countP_mono_left
        intro a _ ha
        simp only [decide_eq_true_eq] at ha ⊢
        intro h
        exact ha (Finset.mem_of_mem_erase h)
      have hcard : (H.erase x).card + 1 = H.card := Finset.card_erase_add_one hx
      simp only [List.countP_cons, List.length_cons, decide_eq_true_eq, hx, not_true_eq_false,
        ↓reduceIte, Nat.add_zero]
      omega
    · have hsub : ∀ a ∈ H, a ∈ xs := by
        intro a ha
        rcases List.mem_cons.mp (hH a ha) with rfl | hxs
        · exact (hx ha).elim
        · exact hxs
      have h1 := ih H hsub
      simp only [List.countP_cons, List.length_cons, decide_eq_true_eq, hx, not_false_eq_true,
        ↓reduceIte]
      omega

lemma lift_derivation_opt {E₁ E₂ : Type} [DecidableEq E₁] [DecidableEq E₂]
    {φ : E₁ → E₂} (hφ : Function.Injective φ)
    {x : Literal E₂} (hx : ∀ e, φ e ≠ x.1)
    {F₁ : Set (Clause E₁)} {F₂ : Set (Clause E₂)}
    {base : List (Clause E₂)} (hbase : IsDerivation F₂ base)
    (handled : Finset (Clause E₁))
    (hHandled : ∀ C ∈ handled, mapClause φ C ∈ base ∨ insert x (mapClause φ C) ∈ base)
    {π₁ : List (Clause E₁)} (hπ₁ : IsDerivation F₁ π₁)
    (hAx : ∀ C ∈ F₁, C ∈ π₁ → C ∉ handled → mapClause φ C ∈ F₂ ∨ insert x (mapClause φ C) ∈ F₂) :
    ∃ π₂ : List (Clause E₂),
      IsDerivation F₂ π₂ ∧
      (∀ D ∈ base, D ∈ π₂) ∧
      (∀ C ∈ π₁, mapClause φ C ∈ π₂ ∨ insert x (mapClause φ C) ∈ π₂) ∧
      π₂.length ≤ base.length + π₁.countP (fun C => decide (C ∉ handled)) := by
  induction hπ₁ with
  | nil =>
    exact ⟨base, hbase, fun _ h => h, fun _ h => (List.not_mem_nil h).elim, by simp⟩
  | ax =>
    rename_i π C hπ hCF ih
    have hAx' : ∀ D ∈ F₁, D ∈ π → D ∉ handled →
        mapClause φ D ∈ F₂ ∨ insert x (mapClause φ D) ∈ F₂ :=
      fun D hDF hDπ hDn => hAx D hDF (List.mem_cons_of_mem C hDπ) hDn
    rcases ih hAx' with ⟨π₂, hder, hsub_base, hcov, hlen⟩
    by_cases hCh : C ∈ handled
    · refine ⟨π₂, hder, hsub_base, ?_, ?_⟩
      · intro D hD
        rcases List.mem_cons.mp hD with rfl | hDπ
        · rcases hHandled D hCh with hb | hb
          · exact Or.inl (hsub_base _ hb)
          · exact Or.inr (hsub_base _ hb)
        · exact hcov D hDπ
      · simp only [List.countP_cons, decide_eq_true_eq, hCh, not_true_eq_false,
          ↓reduceIte, Nat.add_zero]
        exact hlen
    · rcases hAx C hCF List.mem_cons_self hCh with hF | hF
      · refine ⟨mapClause φ C :: π₂, .ax hder hF, fun D hD => List.mem_cons_of_mem _ (hsub_base D hD), ?_, ?_⟩
        · intro D hD
          rcases List.mem_cons.mp hD with rfl | hDπ
          · exact Or.inl List.mem_cons_self
          · exact (hcov D hDπ).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)
        · simp only [List.length_cons, List.countP_cons, decide_eq_true_eq, hCh, not_false_eq_true,
            ↓reduceIte]
          omega
      · refine ⟨insert x (mapClause φ C) :: π₂, .ax hder hF,
          fun D hD => List.mem_cons_of_mem _ (hsub_base D hD), ?_, ?_⟩
        · intro D hD
          rcases List.mem_cons.mp hD with rfl | hDπ
          · exact Or.inr List.mem_cons_self
          · exact (hcov D hDπ).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)
        · simp only [List.length_cons, List.countP_cons, decide_eq_true_eq, hCh, not_false_eq_true,
            ↓reduceIte]
          omega
  | res =>
    rename_i π C D R hπ hC hD hR ih
    have hAx' : ∀ A ∈ F₁, A ∈ π → A ∉ handled →
        mapClause φ A ∈ F₂ ∨ insert x (mapClause φ A) ∈ F₂ :=
      fun A hAF hAπ hAn => hAx A hAF (List.mem_cons_of_mem R hAπ) hAn
    rcases ih hAx' with ⟨π₂, hder, hsub_base, hcov, hlen⟩
    by_cases hRh : R ∈ handled
    · refine ⟨π₂, hder, hsub_base, ?_, ?_⟩
      · intro A hA
        rcases List.mem_cons.mp hA with rfl | hAπ
        · rcases hHandled A hRh with hb | hb
          · exact Or.inl (hsub_base _ hb)
          · exact Or.inr (hsub_base _ hb)
        · exact hcov A hAπ
      · simp only [List.countP_cons, decide_eq_true_eq, hRh, not_true_eq_false,
          ↓reduceIte, Nat.add_zero]
        exact hlen
    · have hC' : ∃ C' ∈ π₂, C' = mapClause φ C ∨ C' = insert x (mapClause φ C) := by
        rcases hcov C hC with h | h
        · exact ⟨_, h, Or.inl rfl⟩
        · exact ⟨_, h, Or.inr rfl⟩
      have hD' : ∃ D' ∈ π₂, D' = mapClause φ D ∨ D' = insert x (mapClause φ D) := by
        rcases hcov D hD with h | h
        · exact ⟨_, h, Or.inl rfl⟩
        · exact ⟨_, h, Or.inr rfl⟩
      rcases hC' with ⟨C', hC'mem, hC'eq⟩
      rcases hD' with ⟨D', hD'mem, hD'eq⟩
      rcases isResolvent_lift_opt hφ hx hR hC'eq hD'eq with ⟨R', hRes', hR'eq⟩
      refine ⟨R' :: π₂, .res hder hC'mem hD'mem hRes',
        fun A hA => List.mem_cons_of_mem _ (hsub_base A hA), ?_, ?_⟩
      · intro A hA
        rcases List.mem_cons.mp hA with rfl | hAπ
        · rcases hR'eq with rfl | rfl
          · exact Or.inl List.mem_cons_self
          · exact Or.inr List.mem_cons_self
        · exact (hcov A hAπ).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)
      · simp only [List.length_cons, List.countP_cons, decide_eq_true_eq, hRh, not_false_eq_true,
          ↓reduceIte]
        omega

def pigeonClause {m n : ℕ} (G : BipGraph m n) (i : Fin m) : Clause (GEdge G) :=
  Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true)

lemma pigeonClause_mem_graphPHP {m n : ℕ} (G : BipGraph m n) (i : Fin m) :
    pigeonClause G i ∈ graphPHP G :=
  Or.inl ⟨i, rfl⟩

lemma holeClause_mem_graphPHP {m n : ℕ} (G : BipGraph m n) (e e' : GEdge G)
    (hj : e.1.2 = e'.1.2) (hi : e.1.1 ≠ e'.1.1) :
    ({(e, false), (e', false)} : Clause (GEdge G)) ∈ graphPHP G :=
  Or.inr ⟨e, e', hj, hi, rfl⟩

def delEdgeGraph {m n : ℕ} (G : BipGraph m n) (e : GEdge G) : BipGraph m n :=
  fun i => if i = e.1.1 then (G i).erase e.1.2 else G i

def delEdgeEmb {m n : ℕ} (G : BipGraph m n) (e : GEdge G) :
    GEdge (delEdgeGraph G e) → GEdge G :=
  fun x => ⟨x.1, by
    have hx := x.2
    unfold delEdgeGraph at hx
    split_ifs at hx with h
    · exact Finset.mem_of_mem_erase hx
    · exact hx⟩

lemma delEdgeEmb_injective {m n : ℕ} (G : BipGraph m n) (e : GEdge G) :
    Function.Injective (delEdgeEmb G e) := by
  intro a b h
  exact Subtype.ext (by simpa [delEdgeEmb] using congrArg Subtype.val h)

lemma delEdgeEmb_ne {m n : ℕ} (G : BipGraph m n) (e : GEdge G)
    (x : GEdge (delEdgeGraph G e)) : delEdgeEmb G e x ≠ e := by
  intro h
  have h1 : x.1.1 = e.1.1 := congrArg (fun z => z.1.1) h
  have h2 : x.1.2 = e.1.2 := congrArg (fun z => z.1.2) h
  have hx := x.2
  unfold delEdgeGraph at hx
  rw [ite_eq_left_iff.mpr (fun hn => (hn h1).elim), h2] at hx
  exact (Finset.notMem_erase _ _) hx

lemma card_delEdgeGraph {m n : ℕ} (G : BipGraph m n) (e : GEdge G) :
    Fintype.card (GEdge (delEdgeGraph G e)) + 1 ≤ Fintype.card (GEdge G) := by
  have hsub : Finset.univ.image (delEdgeEmb G e) ⊆ Finset.univ.erase e := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, _, rfl⟩
    exact Finset.mem_erase.mpr ⟨delEdgeEmb_ne G e x, Finset.mem_univ _⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (delEdgeEmb_injective G e), Finset.card_univ,
      Finset.card_erase_of_mem (Finset.mem_univ e), Finset.card_univ] at hcard
  have hpos : 0 < Fintype.card (GEdge G) := Fintype.card_pos_iff.mpr ⟨e⟩
  omega

lemma delEdge_pigeonClause {m n : ℕ} (G : BipGraph m n) (e : GEdge G) (i : Fin m) :
    mapClause (delEdgeEmb G e) (pigeonClause (delEdgeGraph G e) i) =
      if i = e.1.1 then (pigeonClause G i).erase (e, true) else pigeonClause G i := by
  split_ifs with hi
  · ext ⟨y, b⟩
    simp only [mapClause, mapLit, pigeonClause, Finset.mem_image, Finset.mem_erase,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨x, bx⟩, ⟨hx1, rfl⟩, hpair⟩
      simp only [Prod.mk.injEq] at hpair
      rcases hpair with ⟨rfl, rfl⟩
      refine ⟨?_, hx1, rfl⟩
      intro heq
      exact delEdgeEmb_ne G e x (congrArg Prod.fst heq)
    · rintro ⟨hne, hy1, rfl⟩
      have hy_ne : y ≠ e := fun heq => hne (by rw [heq])
      have hy2 : y.1.2 ≠ e.1.2 := by
        intro h2
        apply hy_ne
        exact Subtype.ext (Prod.ext (hy1.trans hi) h2)
      have hmem : y.1.2 ∈ delEdgeGraph G e y.1.1 := by
        unfold delEdgeGraph
        rw [ite_eq_left_iff.mpr (fun hn => (hn (hy1.trans hi)).elim)]
        exact Finset.mem_erase.mpr ⟨hy2, y.2⟩
      exact ⟨(⟨y.1, hmem⟩, true), ⟨hy1, rfl⟩, rfl⟩
  · ext ⟨y, b⟩
    simp only [mapClause, mapLit, pigeonClause, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨x, bx⟩, ⟨hx1, rfl⟩, hpair⟩
      simp only [Prod.mk.injEq] at hpair
      rcases hpair with ⟨rfl, rfl⟩
      exact ⟨hx1, rfl⟩
    · rintro ⟨hy1, rfl⟩
      have hmem : y.1.2 ∈ delEdgeGraph G e y.1.1 := by
        unfold delEdgeGraph
        rw [ite_eq_right_iff.mpr (fun h => (hi (hy1.symm.trans h)).elim)]
        exact y.2
      exact ⟨(⟨y.1, hmem⟩, true), ⟨hy1, rfl⟩, rfl⟩

def delVertexGraph {m' n' : ℕ} (G : BipGraph (m' + 1) (n' + 1))
    (i : Fin (m' + 1)) (j : Fin (n' + 1)) : BipGraph m' n' :=
  fun a => Finset.univ.filter (fun b => j.succAbove b ∈ G (i.succAbove a))

def delVertexEmb {m' n' : ℕ} (G : BipGraph (m' + 1) (n' + 1))
    (i : Fin (m' + 1)) (j : Fin (n' + 1)) :
    GEdge (delVertexGraph G i j) → GEdge G :=
  fun x => ⟨(i.succAbove x.1.1, j.succAbove x.1.2), (Finset.mem_filter.mp x.2).2⟩

lemma delVertexEmb_injective {m' n' : ℕ} (G : BipGraph (m' + 1) (n' + 1))
    (i : Fin (m' + 1)) (j : Fin (n' + 1)) :
    Function.Injective (delVertexEmb G i j) := by
  intro a b h
  have h1 := congrArg (fun z => z.1.1) h
  have h2 := congrArg (fun z => z.1.2) h
  apply Subtype.ext
  exact Prod.ext (Fin.succAbove_right_injective h1) (Fin.succAbove_right_injective h2)

lemma delVertexEmb_fst_ne {m' n' : ℕ} (G : BipGraph (m' + 1) (n' + 1))
    (i : Fin (m' + 1)) (j : Fin (n' + 1)) (x : GEdge (delVertexGraph G i j)) :
    (delVertexEmb G i j x).1.1 ≠ i :=
  Fin.succAbove_ne i x.1.1

lemma delVertexEmb_snd_ne {m' n' : ℕ} (G : BipGraph (m' + 1) (n' + 1))
    (i : Fin (m' + 1)) (j : Fin (n' + 1)) (x : GEdge (delVertexGraph G i j)) :
    (delVertexEmb G i j x).1.2 ≠ j :=
  Fin.succAbove_ne j x.1.2

lemma card_delVertexGraph {m' n' : ℕ} (G : BipGraph (m' + 1) (n' + 1))
    (e : GEdge G) :
    Fintype.card (GEdge (delVertexGraph G e.1.1 e.1.2)) + 1 +
      ((rightNbrs G e.1.2).erase e.1.1).card ≤ Fintype.card (GEdge G) := by
  let S1 : Finset (GEdge G) := Finset.univ.image (delVertexEmb G e.1.1 e.1.2)
  let S2 : Finset (GEdge G) :=
    ((rightNbrs G e.1.2).erase e.1.1).attach.image
      (fun a => ⟨(a.1, e.1.2), (Finset.mem_filter.mp (show a.1 ∈ rightNbrs G e.1.2 from Finset.mem_of_mem_erase a.2)).2⟩)
  have hdisj12 : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    rcases Finset.mem_image.mp hy1 with ⟨x, _, rfl⟩
    rcases Finset.mem_image.mp hy2 with ⟨a, _, ha⟩
    exact delVertexEmb_snd_ne G e.1.1 e.1.2 x (congrArg (fun z => z.1.2) ha).symm
  have he1 : e ∉ S1 := by
    intro h
    rcases Finset.mem_image.mp h with ⟨x, _, hx⟩
    exact delVertexEmb_fst_ne G e.1.1 e.1.2 x (congrArg (fun z => z.1.1) hx)
  have he2 : e ∉ S2 := by
    intro h
    rcases Finset.mem_image.mp h with ⟨a, _, ha⟩
    exact (Finset.mem_erase.mp a.2).1 (congrArg (fun z => z.1.1) ha)
  have hS1 : S1.card = Fintype.card (GEdge (delVertexGraph G e.1.1 e.1.2)) := by
    rw [Finset.card_image_of_injective _ (delVertexEmb_injective G e.1.1 e.1.2), Finset.card_univ]
  have hS2 : S2.card = ((rightNbrs G e.1.2).erase e.1.1).card := by
    rw [Finset.card_image_of_injective, Finset.card_attach]
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z => z.1.1) hab
  have htot : (insert e (S1 ∪ S2)).card ≤ (Finset.univ : Finset (GEdge G)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_insert_of_notMem (by simp [he1, he2]),
      Finset.card_union_of_disjoint hdisj12, hS1, hS2, Finset.card_univ] at htot
  omega

lemma delVertex_pigeonClause {m' n' : ℕ} (G : BipGraph (m' + 1) (n' + 1))
    (i : Fin (m' + 1)) (j : Fin (n' + 1)) (a : Fin m') :
    mapClause (delVertexEmb G i j) (pigeonClause (delVertexGraph G i j) a) =
      if h : j ∈ G (i.succAbove a) then
        (pigeonClause G (i.succAbove a)).erase (⟨(i.succAbove a, j), h⟩, true)
      else
        pigeonClause G (i.succAbove a) := by
  split_ifs with hj
  · ext ⟨y, b⟩
    simp only [mapClause, mapLit, pigeonClause, Finset.mem_image, Finset.mem_erase,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨x, bx⟩, ⟨hx1, rfl⟩, hpair⟩
      simp only [Prod.mk.injEq] at hpair
      rcases hpair with ⟨rfl, rfl⟩
      refine ⟨?_, ?_, rfl⟩
      · intro heq
        have h2 := congrArg (fun z => z.1.1.2) heq
        exact Fin.succAbove_ne j x.1.2 h2
      · change i.succAbove x.1.1 = i.succAbove a
        exact congrArg i.succAbove hx1
    · rintro ⟨hne, hy1, rfl⟩
      have hy2 : y.1.2 ≠ j := by
        intro h2
        apply hne
        exact Prod.ext (Subtype.ext (Prod.ext hy1 h2)) rfl
      rcases Fin.exists_succAbove_eq hy2 with ⟨b', hb'⟩
      have hmem : b' ∈ delVertexGraph G i j a := by
        simp only [delVertexGraph, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hb', ← hy1]
        exact y.2
      refine ⟨(⟨(a, b'), hmem⟩, true), ⟨rfl, rfl⟩, ?_⟩
      exact Prod.ext (Subtype.ext (Prod.ext hy1.symm hb')) rfl
  · ext ⟨y, b⟩
    simp only [mapClause, mapLit, pigeonClause, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨x, bx⟩, ⟨hx1, rfl⟩, hpair⟩
      simp only [Prod.mk.injEq] at hpair
      rcases hpair with ⟨rfl, rfl⟩
      exact ⟨congrArg i.succAbove hx1, rfl⟩
    · rintro ⟨hy1, rfl⟩
      have hy2 : y.1.2 ≠ j := by
        intro h2
        apply hj
        rw [← hy1, ← h2]
        exact y.2
      rcases Fin.exists_succAbove_eq hy2 with ⟨b', hb'⟩
      have hmem : b' ∈ delVertexGraph G i j a := by
        simp only [delVertexGraph, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hb', ← hy1]
        exact y.2
      refine ⟨(⟨(a, b'), hmem⟩, true), ⟨rfl, rfl⟩, ?_⟩
      exact Prod.ext (Subtype.ext (Prod.ext hy1.symm hb')) rfl

lemma card_gedge_eq_sum {m n : ℕ} (G : BipGraph m n) :
    Fintype.card (GEdge G) = ∑ i : Fin m, (G i).card := by
  let e : GEdge G ≃ Σ i : Fin m, {j : Fin n // j ∈ G i} :=
    { toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
      invFun := fun y => ⟨(y.1, y.2.1), y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact Fintype.card_coe (G i)

lemma card_gedge_le_of_not_dense {m n : ℕ} (G : BipGraph m n)
    (h : ¬ ((Finset.univ.image (fun e : GEdge G => e.1.1)).card +
            (Finset.univ.image (fun e : GEdge G => e.1.2)).card <
            (Finset.univ : Finset (GEdge G)).card)) :
    Fintype.card (GEdge G) ≤ m + n := by
  have h1 : (Finset.univ : Finset (GEdge G)).card ≤
      (Finset.univ.image (fun e : GEdge G => e.1.1)).card +
      (Finset.univ.image (fun e : GEdge G => e.1.2)).card := Nat.le_of_not_lt h
  have hm : (Finset.univ.image (fun e : GEdge G => e.1.1)).card ≤ m := by
    calc (Finset.univ.image (fun e : GEdge G => e.1.1)).card
        ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = m := by simp
  have hn : (Finset.univ.image (fun e : GEdge G => e.1.2)).card ≤ n := by
    calc (Finset.univ.image (fun e : GEdge G => e.1.2)).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  rw [Finset.card_univ] at h1
  omega

lemma exists_pigeon_deg_le_one {m n : ℕ} (G : BipGraph m n)
    (hnm : n < m)
    (hnd : ¬ ((Finset.univ.image (fun e : GEdge G => e.1.1)).card +
              (Finset.univ.image (fun e : GEdge G => e.1.2)).card <
              (Finset.univ : Finset (GEdge G)).card)) :
    ∃ i : Fin m, (G i).card ≤ 1 := by
  by_contra hall
  push Not at hall
  have hsum : 2 * m ≤ ∑ i : Fin m, (G i).card := by
    calc 2 * m = ∑ _i : Fin m, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum (fun i _ => hall i)
  have hcard := card_gedge_le_of_not_dense G hnd
  rw [card_gedge_eq_sum] at hcard
  omega

lemma not_dense_delEdge {m n : ℕ} (G : BipGraph m n) (e : GEdge G)
    (Z : Finset (GEdge G)) (he : e ∈ Z)
    (hZ : ∀ s : Finset (GEdge G), Disjoint s Z →
      ¬ ((s.image (fun x => x.1.1)).card + (s.image (fun x => x.1.2)).card < s.card)) :
    let Z₀ : Finset (GEdge (delEdgeGraph G e)) :=
      Finset.univ.filter (fun x => delEdgeEmb G e x ∈ Z.erase e)
    Z₀.card ≤ Z.card - 1 ∧
    ∀ s : Finset (GEdge (delEdgeGraph G e)), Disjoint s Z₀ →
      ¬ ((s.image (fun x => x.1.1)).card + (s.image (fun x => x.1.2)).card < s.card) := by
  intro Z₀
  constructor
  · have hsub : Z₀.image (delEdgeEmb G e) ⊆ Z.erase e := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      exact (Finset.mem_filter.mp hx).2
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (delEdgeEmb_injective G e),
        Finset.card_erase_of_mem he] at hcard
    exact hcard
  · intro s hs
    let s' : Finset (GEdge G) := s.image (delEdgeEmb G e)
    have hdisj : Disjoint s' Z := by
      rw [Finset.disjoint_left]
      intro y hy hyZ
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      have hne : delEdgeEmb G e x ≠ e := delEdgeEmb_ne G e x
      have hxZ₀ : x ∈ Z₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_erase.mpr ⟨hne, hyZ⟩⟩
      exact Finset.disjoint_left.mp hs hx hxZ₀
    have hnd := hZ s' hdisj
    have h1 : s'.image (fun x => x.1.1) = s.image (fun x => x.1.1) := by
      dsimp only [s']; rw [Finset.image_image]; rfl
    have h2 : s'.image (fun x => x.1.2) = s.image (fun x => x.1.2) := by
      dsimp only [s']; rw [Finset.image_image]; rfl
    have hc : s'.card = s.card := Finset.card_image_of_injective s (delEdgeEmb_injective G e)
    simpa [h1, h2, hc] using hnd

lemma not_dense_delVertex {m' n' : ℕ} (G : BipGraph (m' + 1) (n' + 1))
    (e : GEdge G) (Z : Finset (GEdge G))
    (hZ : ∀ s : Finset (GEdge G), Disjoint s Z →
      ¬ ((s.image (fun x => x.1.1)).card + (s.image (fun x => x.1.2)).card < s.card)) :
    let Z₁ : Finset (GEdge (delVertexGraph G e.1.1 e.1.2)) :=
      Finset.univ.filter (fun x => delVertexEmb G e.1.1 e.1.2 x ∈ Z.erase e)
    (e ∈ Z → Z₁.card ≤ Z.card - 1) ∧
    (Z = ∅ → Z₁ = ∅) ∧
    ∀ s : Finset (GEdge (delVertexGraph G e.1.1 e.1.2)), Disjoint s Z₁ →
      ¬ ((s.image (fun x => x.1.1)).card + (s.image (fun x => x.1.2)).card < s.card) := by
  intro Z₁
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have hsub : Z₁.image (delVertexEmb G e.1.1 e.1.2) ⊆ Z.erase e := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      exact (Finset.mem_filter.mp hx).2
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (delVertexEmb_injective G e.1.1 e.1.2),
        Finset.card_erase_of_mem he] at hcard
    exact hcard
  · intro hEmpty
    ext x
    simp [Z₁, hEmpty]
  · intro s hs
    let s' : Finset (GEdge G) := s.image (delVertexEmb G e.1.1 e.1.2)
    have hdisj : Disjoint s' Z := by
      rw [Finset.disjoint_left]
      intro y hy hyZ
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      have hne : delVertexEmb G e.1.1 e.1.2 x ≠ e := fun h =>
        delVertexEmb_fst_ne G e.1.1 e.1.2 x (congrArg (fun z => z.1.1) h)
      have hxZ₁ : x ∈ Z₁ :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_erase.mpr ⟨hne, hyZ⟩⟩
      exact Finset.disjoint_left.mp hs hx hxZ₁
    have hnd := hZ s' hdisj
    have h1 : (s'.image (fun x => x.1.1)).card = (s.image (fun x => x.1.1)).card := by
      have heq : s'.image (fun x => x.1.1) = (s.image (fun x => x.1.1)).image e.1.1.succAbove := by
        dsimp only [s']; rw [Finset.image_image, Finset.image_image]; rfl
      rw [heq, Finset.card_image_of_injective _ Fin.succAbove_right_injective]
    have h2 : (s'.image (fun x => x.1.2)).card = (s.image (fun x => x.1.2)).card := by
      have heq : s'.image (fun x => x.1.2) = (s.image (fun x => x.1.2)).image e.1.2.succAbove := by
        dsimp only [s']; rw [Finset.image_image, Finset.image_image]; rfl
      rw [heq, Finset.card_image_of_injective _ Fin.succAbove_right_injective]
    have hc : s'.card = s.card := Finset.card_image_of_injective s (delVertexEmb_injective G e.1.1 e.1.2)
    simpa [h1, h2, hc] using hnd

lemma build_delVertex_base {m' n' : ℕ} (G : BipGraph (m' + 1) (n' + 1)) (e : GEdge G)
    (S : Finset (Fin m'))
    (hS : ∀ a ∈ S, e.1.2 ∈ G (e.1.1.succAbove a)) :
    ∃ base : List (Clause (GEdge G)),
      IsDerivation (graphPHP G) base ∧
      base.length = 3 * S.card ∧
      ∀ a ∈ S,
        insert (e, false) (mapClause (delVertexEmb G e.1.1 e.1.2)
          (pigeonClause (delVertexGraph G e.1.1 e.1.2) a)) ∈ base := by
  classical
  induction S using Finset.induction with
  | empty =>
    exact ⟨[], .nil, by simp, fun _ h => (Finset.notMem_empty _ h).elim⟩
  | @insert a S ha ih =>
    have hS' : ∀ b ∈ S, e.1.2 ∈ G (e.1.1.succAbove b) :=
      fun b hb => hS b (Finset.mem_insert_of_mem hb)
    rcases ih hS' with ⟨base, hder, hlen, hcov⟩
    have hj : e.1.2 ∈ G (e.1.1.succAbove a) := hS a (Finset.mem_insert_self a S)
    let e' : GEdge G := ⟨(e.1.1.succAbove a, e.1.2), hj⟩
    let Cpig : Clause (GEdge G) := pigeonClause G (e.1.1.succAbove a)
    let Chole : Clause (GEdge G) := {(e, false), (e', false)}
    let Cres : Clause (GEdge G) :=
      insert (e, false) (mapClause (delVertexEmb G e.1.1 e.1.2)
        (pigeonClause (delVertexGraph G e.1.1 e.1.2) a))
    have hne : e' ≠ e := fun h =>
      Fin.succAbove_ne e.1.1 a (congrArg (fun z => z.1.1) h)
    have hmem_pig : (e', true) ∈ Cpig := by
      simp [Cpig, pigeonClause, e']
    have hmem_hole : (e', false) ∈ Chole := by simp [Chole]
    have hRes : IsResolvent Cpig Chole Cres := by
      refine ⟨e', hmem_pig, hmem_hole, ?_⟩
      have h1 := delVertex_pigeonClause G e.1.1 e.1.2 a
      split_ifs at h1
      have hChole_er : Chole.erase (e', false) = {(e, false)} := by
        ext z
        simp only [Chole, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hz, rfl | rfl⟩
          · rfl
          · exact (hz rfl).elim
        · rintro rfl
          exact ⟨fun h => hne (congrArg Prod.fst h).symm, Or.inl rfl⟩
      rw [hChole_er]
      change Cres = Cpig.erase (e', true) ∪ {(e, false)}
      rw [Finset.union_comm]
      simp [Cres, Cpig, e', h1]
    have hder1 : IsDerivation (graphPHP G) (Cpig :: base) :=
      .ax hder (pigeonClause_mem_graphPHP G (e.1.1.succAbove a))
    have hder2 : IsDerivation (graphPHP G) (Chole :: Cpig :: base) :=
      .ax hder1 (holeClause_mem_graphPHP G e e' rfl (Fin.succAbove_ne e.1.1 a).symm)
    have hder3 : IsDerivation (graphPHP G) (Cres :: Chole :: Cpig :: base) :=
      .res hder2 (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self hRes
    refine ⟨Cres :: Chole :: Cpig :: base, hder3, ?_, ?_⟩
    · simp [hlen, Finset.card_insert_of_notMem ha]
      omega
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hbS
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hcov b hbS)))

lemma lift_delVertex_refutation {m' n' : ℕ} (G : BipGraph (m' + 1) (n' + 1)) (e : GEdge G)
    (π₁ : List (Clause (GEdge (delVertexGraph G e.1.1 e.1.2))))
    (hπ₁ : IsRefutation (graphPHP (delVertexGraph G e.1.1 e.1.2)) π₁) :
    ∃ π₂ : List (Clause (GEdge G)),
      IsDerivation (graphPHP G) π₂ ∧
      ((∅ : Clause (GEdge G)) ∈ π₂ ∨ ({(e, false)} : Clause (GEdge G)) ∈ π₂) ∧
      π₂.length ≤ π₁.length + 2 * ((rightNbrs G e.1.2).erase e.1.1).card := by
  classical
  let G₁ := delVertexGraph G e.1.1 e.1.2
  let φ := delVertexEmb G e.1.1 e.1.2
  by_cases hDeg1 : ∃ a : Fin m', e.1.2 ∈ G (e.1.1.succAbove a) ∧ G₁ a = ∅
  · rcases hDeg1 with ⟨a, hj, haEmpty⟩
    let e' : GEdge G := ⟨(e.1.1.succAbove a, e.1.2), hj⟩
    have hne : e' ≠ e := fun h => Fin.succAbove_ne e.1.1 a (congrArg (fun z => z.1.1) h)
    have hBpos : 1 ≤ ((rightNbrs G e.1.2).erase e.1.1).card := by
      apply Finset.card_pos.mpr
      refine ⟨e.1.1.succAbove a, Finset.mem_erase.mpr ⟨Fin.succAbove_ne e.1.1 a, ?_⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    have hLen1pos : 1 ≤ π₁.length := List.length_pos_of_mem hπ₁.2
    have hpig : pigeonClause G (e.1.1.succAbove a) = {(e', true)} := by
      ext ⟨y, b⟩
      simp only [pigeonClause, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hy1, rfl⟩
        have hy2 : y.1.2 = e.1.2 := by
          by_contra hne2
          rcases Fin.exists_succAbove_eq hne2 with ⟨b', hb'⟩
          have hb'mem : b' ∈ G₁ a := by
            simp only [G₁, delVertexGraph, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hb', ← hy1]; exact y.2
          rw [haEmpty] at hb'mem
          exact Finset.notMem_empty _ hb'mem
        exact Prod.ext (Subtype.ext (Prod.ext hy1 hy2)) rfl
      · rintro h
        cases h
        exact ⟨rfl, rfl⟩
    let Chole : Clause (GEdge G) := {(e, false), (e', false)}
    have hRes : IsResolvent {(e', true)} Chole {(e, false)} := by
      refine ⟨e', by simp, by simp [Chole], ?_⟩
      ext z
      simp only [Chole, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro rfl
        exact Or.inr ⟨fun h => hne (congrArg Prod.fst h).symm, Or.inl rfl⟩
      · rintro (⟨h1, rfl⟩ | ⟨h2, rfl | rfl⟩)
        · exact (h1 rfl).elim
        · rfl
        · exact (h2 rfl).elim
    have h1 : IsDerivation (graphPHP G) [{(e', true)}] :=
      .ax .nil (by rw [← hpig]; exact pigeonClause_mem_graphPHP G _)
    have h2 : IsDerivation (graphPHP G) (Chole :: [{(e', true)}]) :=
      .ax h1 (holeClause_mem_graphPHP G e e' rfl (Fin.succAbove_ne e.1.1 a).symm)
    have h3 : IsDerivation (graphPHP G) ({(e, false)} :: Chole :: [{(e', true)}]) :=
      .res h2 (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self hRes
    exact ⟨_, h3, Or.inr List.mem_cons_self, by simp; omega⟩
  · push Not at hDeg1
    let S_all : Finset (Fin m') := Finset.univ.filter (fun a => e.1.2 ∈ G (e.1.1.succAbove a))
    let S_used : Finset (Fin m') := S_all.filter (fun a => pigeonClause G₁ a ∈ π₁)
    let handled : Finset (Clause (GEdge G₁)) := S_used.image (pigeonClause G₁)
    have hInj : Set.InjOn (pigeonClause G₁) (S_used : Set (Fin m')) := by
      intro a ha b hb hab
      have haAll : a ∈ S_all := (Finset.mem_filter.mp ha).1
      have haNe : (G₁ a).Nonempty := hDeg1 a (Finset.mem_filter.mp haAll).2
      rcases haNe with ⟨b', hb'⟩
      let ea : GEdge G₁ := ⟨(a, b'), hb'⟩
      have hmemA : (ea, true) ∈ pigeonClause G₁ a := by simp [pigeonClause, ea]
      rw [hab] at hmemA
      exact (Finset.mem_filter.mp hmemA).2.1
    have hHandledCard : handled.card = S_used.card :=
      Finset.card_image_of_injOn hInj
    have hSusedLe : S_used.card ≤ ((rightNbrs G e.1.2).erase e.1.1).card := by
      have hsub : S_used.image e.1.1.succAbove ⊆ (rightNbrs G e.1.2).erase e.1.1 := by
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨a, ha, rfl⟩
        have haAll := (Finset.mem_filter.mp ha).1
        refine Finset.mem_erase.mpr ⟨Fin.succAbove_ne e.1.1 a, ?_⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp haAll).2⟩
      have hc := Finset.card_le_card hsub
      rwa [Finset.card_image_of_injective _ Fin.succAbove_right_injective] at hc
    rcases build_delVertex_base G e S_used (fun a ha => (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2)
      with ⟨base, hbase_der, hbase_len, hbase_cov⟩
    have hHandled_cov : ∀ C ∈ handled, mapClause φ C ∈ base ∨ insert (e, false) (mapClause φ C) ∈ base := by
      intro C hC
      rcases Finset.mem_image.mp hC with ⟨a, ha, rfl⟩
      exact Or.inr (hbase_cov a ha)
    have hAx : ∀ C ∈ graphPHP G₁, C ∈ π₁ → C ∉ handled →
        mapClause φ C ∈ graphPHP G ∨ insert (e, false) (mapClause φ C) ∈ graphPHP G := by
      intro C hCF hCπ hCn
      rcases hCF with ⟨a, rfl⟩ | ⟨x, y, hxy2, hxy1, rfl⟩
      · left
        have hnotj : e.1.2 ∉ G (e.1.1.succAbove a) := by
          intro hj
          have haUsed : a ∈ S_used :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hCπ⟩
          exact hCn (Finset.mem_image.mpr ⟨a, haUsed, rfl⟩)
        have hEq := delVertex_pigeonClause G e.1.1 e.1.2 a
        rw [dite_eq_right_iff.mpr (fun h => (hnotj h).elim)] at hEq
        rw [show mapClause φ (Finset.univ.filter fun l : Literal (GEdge G₁) => l.1.1.1 = a ∧ l.2 = true) =
              mapClause φ (pigeonClause G₁ a) from rfl, hEq]
        exact pigeonClause_mem_graphPHP G (e.1.1.succAbove a)
      · left
        have hEq : mapClause φ ({(x, false), (y, false)} : Clause (GEdge G₁)) =
            {(φ x, false), (φ y, false)} := by
          simp [mapClause, mapLit]
        rw [hEq]
        exact holeClause_mem_graphPHP G (φ x) (φ y)
          (by simp [φ, delVertexEmb, hxy2])
          (by simp [φ, delVertexEmb, hxy1])
    have hneE : ∀ x : GEdge G₁, φ x ≠ e := fun x h =>
      delVertexEmb_fst_ne G e.1.1 e.1.2 x (congrArg (fun z => z.1.1) h)
    rcases lift_derivation_opt (delVertexEmb_injective G e.1.1 e.1.2) hneE
        hbase_der handled hHandled_cov hπ₁.1 hAx with ⟨π₂, hder₂, _, hcov₂, hlen₂⟩
    have hcount := countP_not_mem_add_card_le π₁ handled (by
      intro C hC
      rcases Finset.mem_image.mp hC with ⟨a, ha, rfl⟩
      exact (Finset.mem_filter.mp ha).2)
    have hEmpty := hcov₂ ∅ hπ₁.2
    rw [mapClause_empty] at hEmpty
    refine ⟨π₂, hder₂, ?_, ?_⟩
    · simpa using hEmpty
    · omega

lemma res_refutation_bound_aux : ∀ (k eCard : ℕ) {m n : ℕ} (G : BipGraph m n)
    (Z : Finset (GEdge G)),
    Z.card = k →
    Fintype.card (GEdge G) = eCard →
    (∀ s : Finset (GEdge G), Disjoint s Z →
      ¬ ((s.image (fun e => e.1.1)).card + (s.image (fun e => e.1.2)).card < s.card)) →
    n < m →
    ∃ π : List (Clause (GEdge G)),
      IsRefutation (graphPHP G) π ∧
      π.length ≤ (2 * eCard + 1) * 2 ^ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ihk =>
    intro eCard
    induction eCard using Nat.strong_induction_on with
    | ind eCard ihe =>
      intro m n G Z hk heCard hZ hnm
      by_cases hk0 : k = 0
      · subst hk0
        have hZempty : Z = ∅ := Finset.card_eq_zero.mp hk
        subst hZempty
        have hndUniv := hZ Finset.univ (Finset.disjoint_empty_right _)
        rcases exists_pigeon_deg_le_one G hnm hndUniv with ⟨i, hi⟩
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with hi0 | hi1
        · have hGempty : G i = ∅ := Finset.card_eq_zero.mp hi0
          have hpigEmpty : pigeonClause G i = ∅ := by
            ext ⟨y, b⟩
            simp only [pigeonClause, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.notMem_empty, iff_false, not_and]
            intro hy1 _
            have hy2 := y.2
            rw [hy1, hGempty] at hy2
            exact Finset.notMem_empty _ hy2
          refine ⟨[∅], ⟨.ax .nil (by rw [← hpigEmpty]; exact pigeonClause_mem_graphPHP G i),
            List.mem_cons_self⟩, ?_⟩
          simp
        · rcases Finset.card_eq_one.mp hi1 with ⟨j, hGj⟩
          have hjmem : j ∈ G i := by rw [hGj]; exact Finset.mem_singleton_self j
          cases m with
          | zero => omega
          | succ m' =>
            cases n with
            | zero => exact (Fin.elim0 j)
            | succ n' =>
              let e : GEdge G := ⟨(i, j), hjmem⟩
              set G₁ := delVertexGraph G e.1.1 e.1.2
              have hcard1 : Fintype.card (GEdge G₁) + 1 + ((rightNbrs G e.1.2).erase e.1.1).card ≤ eCard := by
                rw [← heCard]
                exact card_delVertexGraph G e
              have hlt1 : Fintype.card (GEdge G₁) < eCard := by omega
              have hnd1 := (not_dense_delVertex G e ∅ hZ).2
              have hZ1empty : Finset.univ.filter (fun x : GEdge G₁ => delVertexEmb G e.1.1 e.1.2 x ∈ (∅ : Finset (GEdge G)).erase e) = ∅ :=
                hnd1.1 rfl
              have hnd1' : ∀ s : Finset (GEdge G₁), Disjoint s ∅ →
                  ¬ ((s.image (fun x => x.1.1)).card + (s.image (fun x => x.1.2)).card < s.card) := by
                simpa [hZ1empty] using hnd1.2
              rcases ihe (Fintype.card (GEdge G₁)) hlt1 G₁ ∅ rfl rfl hnd1' (by omega) with ⟨π₁, hπ₁, hlen₁⟩
              rcases lift_delVertex_refutation G e π₁ hπ₁ with ⟨π₂, hder₂, hmem₂, hlen₂⟩
              rcases hmem₂ with hEmpty | hUnit
              · refine ⟨π₂, ⟨hder₂, hEmpty⟩, ?_⟩
                simp only [Nat.pow_zero, Nat.mul_one] at hlen₁ ⊢
                omega
              · have hpig : pigeonClause G i = {(e, true)} := by
                  ext ⟨y, b⟩
                  simp only [pigeonClause, Finset.mem_filter, Finset.mem_univ, true_and,
                    Finset.mem_singleton]
                  constructor
                  · rintro ⟨hy1, rfl⟩
                    have hy2 : y.1.2 = j := by
                      have := y.2
                      rw [hy1, hGj] at this
                      exact Finset.mem_singleton.mp this
                    exact Prod.ext (Subtype.ext (Prod.ext hy1 hy2)) rfl
                  · rintro h
                    cases h
                    exact ⟨rfl, rfl⟩
                have hRes : IsResolvent {(e, true)} {(e, false)} (∅ : Clause (GEdge G)) :=
                  ⟨e, by simp, by simp, by simp⟩
                have hder3 : IsDerivation (graphPHP G) ({(e, true)} :: π₂) :=
                  .ax hder₂ (by rw [← hpig]; exact pigeonClause_mem_graphPHP G i)
                have hder4 : IsDerivation (graphPHP G) (∅ :: {(e, true)} :: π₂) :=
                  .res hder3 List.mem_cons_self (List.mem_cons_of_mem _ hUnit) hRes
                refine ⟨∅ :: {(e, true)} :: π₂, ⟨hder4, List.mem_cons_self⟩, ?_⟩
                simp only [List.length_cons, Nat.pow_zero, Nat.mul_one] at hlen₁ ⊢
                omega
      · have hZne : Z.Nonempty := Finset.card_pos.mp (by omega)
        rcases hZne with ⟨e, heZ⟩
        set G₀ := delEdgeGraph G e
        set Z₀ := Finset.univ.filter (fun x : GEdge G₀ => delEdgeEmb G e x ∈ Z.erase e)
        have h0 := not_dense_delEdge G e Z heZ hZ
        have hZ0le : Z₀.card ≤ k - 1 := by
          have := h0.1
          change Z₀.card ≤ Z.card - 1 at this
          omega
        have hcard0 : Fintype.card (GEdge G₀) + 1 ≤ eCard := by
          rw [← heCard]
          exact card_delEdgeGraph G e
        rcases ihk Z₀.card (by omega) (Fintype.card (GEdge G₀)) G₀ Z₀ rfl rfl h0.2 hnm
          with ⟨π₀, hπ₀, hlen₀⟩
        have hAx₀ : ∀ C ∈ graphPHP G₀, C ∈ π₀ → C ∉ (∅ : Finset (Clause (GEdge G₀))) →
            mapClause (delEdgeEmb G e) C ∈ graphPHP G ∨
            insert (e, true) (mapClause (delEdgeEmb G e) C) ∈ graphPHP G := by
          intro C hCF _ _
          rcases hCF with ⟨i, rfl⟩ | ⟨x, y, hxy2, hxy1, rfl⟩
          · have hEq := delEdge_pigeonClause G e i
            change mapClause (delEdgeEmb G e) (pigeonClause G₀ i) ∈ graphPHP G ∨
              insert (e, true) (mapClause (delEdgeEmb G e) (pigeonClause G₀ i)) ∈ graphPHP G
            rw [hEq]
            split_ifs with hi
            · right
              have hmem : (e, true) ∈ pigeonClause G i := by simp [pigeonClause, hi]
              rw [Finset.insert_erase hmem]
              exact pigeonClause_mem_graphPHP G i
            · left
              exact pigeonClause_mem_graphPHP G i
          · left
            have hEq : mapClause (delEdgeEmb G e) ({(x, false), (y, false)} : Clause (GEdge G₀)) =
                {(delEdgeEmb G e x, false), (delEdgeEmb G e y, false)} := by
              simp [mapClause, mapLit]
            rw [hEq]
            exact holeClause_mem_graphPHP G _ _ hxy2 hxy1
        rcases lift_derivation_opt (delEdgeEmb_injective G e) (delEdgeEmb_ne G e)
            (.nil : IsDerivation (graphPHP G) []) ∅ (by simp) hπ₀.1 hAx₀
          with ⟨π₀', hder₀', _, hcov₀', hlen₀'⟩
        have hEmpty₀ := hcov₀' ∅ hπ₀.2
        rw [mapClause_empty] at hEmpty₀
        simp only [List.length_nil, Nat.zero_add, Finset.notMem_empty, not_false_eq_true,
          decide_true, List.countP_true] at hlen₀'
        cases m with
        | zero => omega
        | succ m' =>
          cases n with
          | zero => exact (Fin.elim0 e.1.2)
          | succ n' =>
            set G₁ := delVertexGraph G e.1.1 e.1.2
            set Z₁ := Finset.univ.filter (fun x : GEdge G₁ => delVertexEmb G e.1.1 e.1.2 x ∈ Z.erase e)
            have h1 := not_dense_delVertex G e Z hZ
            have hZ1le : Z₁.card ≤ k - 1 := by
              have := h1.1 heZ
              change Z₁.card ≤ Z.card - 1 at this
              omega
            have hcard1 : Fintype.card (GEdge G₁) + 1 + ((rightNbrs G e.1.2).erase e.1.1).card ≤ eCard := by
              rw [← heCard]
              exact card_delVertexGraph G e
            rcases ihk Z₁.card (by omega) (Fintype.card (GEdge G₁)) G₁ Z₁ rfl rfl h1.2.2 (by omega)
              with ⟨π₁, hπ₁, hlen₁⟩
            rcases lift_delVertex_refutation G e π₁ hπ₁ with ⟨π₁', hder₁', hmem₁', hlen₁'⟩
            have hPow0 : 2 ^ Z₀.card ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) hZ0le
            have hPow1 : 2 ^ Z₁.card ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) hZ1le
            have hPowPos : 1 ≤ 2 ^ (k - 1) := Nat.one_le_pow _ _ (by omega)
            have hPowK : 2 ^ k = 2 * 2 ^ (k - 1) := by
              cases k with
              | zero => omega
              | succ k' => simp [Nat.pow_succ, Nat.mul_comm]
            have hBnd0 : π₀'.length ≤ (2 * eCard - 1) * 2 ^ (k - 1) := by
              calc π₀'.length ≤ π₀.length := hlen₀'
                _ ≤ (2 * Fintype.card (GEdge G₀) + 1) * 2 ^ Z₀.card := hlen₀
                _ ≤ (2 * eCard - 1) * 2 ^ (k - 1) := Nat.mul_le_mul (by omega) hPow0
            have hBnd1 : π₁'.length ≤ (2 * eCard - 1) * 2 ^ (k - 1) := by
              set B := ((rightNbrs G e.1.2).erase e.1.1).card
              calc π₁'.length ≤ π₁.length + 2 * B := hlen₁'
                _ ≤ (2 * Fintype.card (GEdge G₁) + 1) * 2 ^ Z₁.card + 2 * B := Nat.add_le_add_right hlen₁ _
                _ ≤ (2 * Fintype.card (GEdge G₁) + 1) * 2 ^ (k - 1) + 2 * B * 2 ^ (k - 1) := by
                  apply Nat.add_le_add
                  · exact Nat.mul_le_mul_left _ hPow1
                  · exact Nat.le_mul_of_pos_right _ (by omega)
                _ = (2 * Fintype.card (GEdge G₁) + 1 + 2 * B) * 2 ^ (k - 1) := by ring
                _ ≤ (2 * eCard - 1) * 2 ^ (k - 1) := Nat.mul_le_mul_right _ (by omega)
            rcases hEmpty₀ with hE0 | hU0
            · refine ⟨π₀', ⟨hder₀', hE0⟩, ?_⟩
              have : (2 * eCard - 1) * 2 ^ (k - 1) ≤ (2 * eCard + 1) * 2 ^ k := by
                rw [hPowK]
                have := Nat.mul_le_mul (show 2 * eCard - 1 ≤ 2 * eCard + 1 by omega)
                  (show 2 ^ (k - 1) ≤ 2 * 2 ^ (k - 1) by omega)
                exact this
              omega
            · rcases hmem₁' with hE1 | hU1
              · refine ⟨π₁', ⟨hder₁', hE1⟩, ?_⟩
                have : (2 * eCard - 1) * 2 ^ (k - 1) ≤ (2 * eCard + 1) * 2 ^ k := by
                  rw [hPowK]
                  exact Nat.mul_le_mul (by omega) (by omega)
                omega
              · have hderApp : IsDerivation (graphPHP G) (π₀' ++ π₁') :=
                  isDerivation_append hder₀' hder₁'
                have hRes : IsResolvent {(e, true)} {(e, false)} (∅ : Clause (GEdge G)) :=
                  ⟨e, by simp, by simp, by simp⟩
                have hderFin : IsDerivation (graphPHP G) (∅ :: (π₀' ++ π₁')) :=
                  .res hderApp (List.mem_append_left _ (by simpa using hU0))
                    (List.mem_append_right _ hU1) hRes
                refine ⟨∅ :: (π₀' ++ π₁'), ⟨hderFin, List.mem_cons_self⟩, ?_⟩
                simp only [List.length_cons, List.length_append]
                have hSum : π₀'.length + π₁'.length ≤ (2 * eCard - 1) * 2 ^ k := by
                  calc π₀'.length + π₁'.length
                      ≤ (2 * eCard - 1) * 2 ^ (k - 1) + (2 * eCard - 1) * 2 ^ (k - 1) :=
                        Nat.add_le_add hBnd0 hBnd1
                    _ = (2 * eCard - 1) * (2 * 2 ^ (k - 1)) := by ring
                    _ = (2 * eCard - 1) * 2 ^ k := by rw [← hPowK]
                have hOne : 1 ≤ 2 * 2 ^ k := by
                  have : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by omega)
                  omega
                have hDiff : (2 * eCard - 1) * 2 ^ k + 2 * 2 ^ k = (2 * eCard + 1) * 2 ^ k := by
                  have hepos : 1 ≤ eCard := by
                    rw [← heCard]
                    exact Fintype.card_pos_iff.mpr ⟨e⟩
                  have hsub : 2 * eCard - 1 + 2 = 2 * eCard + 1 := by omega
                  rw [← Nat.add_mul, hsub]
                omega

lemma linKOfClause_card_le {V : Type} [DecidableEq V] (C : Clause V) (k : ℕ) (hk : 1 ≤ k) :
    ∀ T ∈ linKOfClause C, T.card ≤ k := by
  intro T hT
  rcases Finset.mem_image.mp hT with ⟨q, _, rfl⟩
  simpa using hk

lemma linKOfClause_empty {V : Type} [DecidableEq V] :
    linKOfClause (∅ : Clause V) = ∅ := by
  simp [linKOfClause, linOfClause]

lemma linKOfClause_lit_inj {V : Type} [DecidableEq V] :
    Function.Injective (fun l : Literal V => ({(({l.1} : Finset V), l.2)} : LinTerm V)) := by
  intro a b h
  have h1 := Finset.singleton_injective h
  have h2 := congrArg Prod.fst h1
  have h3 := congrArg Prod.snd h1
  exact Prod.ext (Finset.singleton_injective h2) h3

lemma linKOfClause_eq_image {V : Type} [DecidableEq V] (C : Clause V) :
    linKOfClause C = C.image (fun l : Literal V => ({(({l.1} : Finset V), l.2)} : LinTerm V)) := by
  rw [linKOfClause, linOfClause, Finset.image_image]
  rfl

lemma res_to_linK_derivation {V : Type} [DecidableEq V] (F : Set (Clause V)) (k : ℕ) (hk : 1 ≤ k)
    {π : List (Clause V)} (hπ : IsDerivation F π) :
    IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F) (π.map linKOfClause) := by
  induction hπ with
  | nil => exact .nil
  | ax _ hC ih =>
    exact .ax ih ⟨_, hC, rfl⟩ (linKOfClause_card_le _ k hk)
  | res =>
    rename_i π C D R _ hC hD hR ih
    rcases hR with ⟨v, hvC, hvD, rfl⟩
    let qT : LinEq V := ({v}, true)
    let qF : LinEq V := ({v}, false)
    let T : LinTerm V := {qT}
    have hCut : IsLinKCut (linKOfClause C) (linKOfClause D)
        (linKOfClause (C.erase (v, true) ∪ D.erase (v, false))) := by
      refine ⟨T, ?_, ?_, ?_⟩
      · rw [linKOfClause_eq_image]
        exact Finset.mem_image.mpr ⟨(v, true), hvC, rfl⟩
      · intro e he
        rw [Finset.mem_singleton.mp he, linKOfClause_eq_image]
        exact Finset.mem_image.mpr ⟨(v, false), hvD, rfl⟩
      · have hImgT : T.image (fun e => ({negLinEq e} : LinTerm V)) = {{qF}} := by
          ext X; simp [T, qT, qF, negLinEq]
        rw [hImgT, Finset.sdiff_singleton_eq_erase]
        rw [linKOfClause_eq_image, linKOfClause_eq_image, linKOfClause_eq_image, Finset.image_union]
        congr 1
        · exact Finset.image_erase linKOfClause_lit_inj C (v, true)
        · exact Finset.image_erase linKOfClause_lit_inj D (v, false)
    exact .cut ih (List.mem_map_of_mem hC) (List.mem_map_of_mem hD) hCut
      (linKOfClause_card_le _ k hk)

theorem linK_refutation_bound {m n : ℕ} (G : BipGraph m n)
    (Z : Finset (GEdge G))
    (hZ : ∀ s : Finset (GEdge G), Disjoint s Z →
      ¬ ((s.image (fun e => e.1.1)).card + (s.image (fun e => e.1.2)).card < s.card))
    (hnm : n < m) (k : ℕ) (hk : 1 ≤ k) :
    ∃ π : List (LinKLine (GEdge G)),
      IsLinKRefutation k (funGraphPHP G) π ∧
      π.length ≤ (2 * Fintype.card (GEdge G) + 1) * 2 ^ Z.card := by
  rcases res_refutation_bound_aux Z.card (Fintype.card (GEdge G)) G Z rfl rfl hZ hnm
    with ⟨π₀, hπ₀, hlen₀⟩
  have hfun : IsRefutation (funGraphPHP G) π₀ :=
    isRefutation_mono Set.subset_union_left hπ₀
  refine ⟨π₀.map linKOfClause, ⟨res_to_linK_derivation _ k hk hfun.1, ?_⟩, by simpa using hlen₀⟩
  exact List.mem_map.mpr ⟨∅, hfun.2, linKOfClause_empty⟩

end Half2

end PEqualNP.Outside.L_pcx_348

theorem PEqualNP.Outside.L_pcx_348 : ∃ C : ℕ, 0 < C ∧ ∀ (m n p : ℕ) (G : PEqualNP.Expanders.BipGraph m n),
  let E := PEqualNP.Expanders.GEdge G
  let dense := fun (s : Finset E) =>
    (s.image (fun e => e.val.1)).card + (s.image (fun e => e.val.2)).card < s.card
  (∀ family : Finset (Finset E), (∀ s ∈ family, dense s) →
    (∀ a ∈ family, ∀ b ∈ family, a ≠ b → Disjoint a b) → family.card ≤ p) →
  ∃ Z : Finset E, Z.card ≤ C*p*Nat.clog 2 (p+2) ∧
    (∀ s : Finset E, Disjoint s Z → ¬ dense s) ∧
    (n < m → ∀ k : ℕ, 1 ≤ k →
      ∃ π : List (PEqualNP.ProofComplexity.LinKLine E),
        PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.Expanders.funGraphPHP G) π ∧
        π.length ≤ (2*Fintype.card E+1)*2^Z.card) := by
  refine ⟨56, by omega, ?_⟩
  intro m n p G E dense hpack
  rcases PEqualNP.Outside.L_pcx_348.dense_hitting_bound m n p G hpack with ⟨Z, hZcard, hZhit⟩
  refine ⟨Z, hZcard, hZhit, ?_⟩
  intro hnm k hk
  exact PEqualNP.Outside.L_pcx_348.linK_refutation_bound G Z hZhit hnm k hk
