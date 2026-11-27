import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_312

open PEqualNP.ProofComplexity

abbrev Raw {n : ℕ} (a : Fin n → ℕ) : Type := (v : Fin n) × Fin (a v)

def val {n : ℕ} (a : Fin n → ℕ) (x : Raw a → Bool) (v : Fin n) : Bool :=
  decide (Odd (((Finset.univ : Finset (Fin (a v))).filter (fun j => x ⟨v,j⟩ = true)).card))

def blk {n : ℕ} (a : Fin n → ℕ) (V : Finset (Fin n)) : Finset (Raw a) :=
  (Finset.univ : Finset (Raw a)).filter (fun z => z.1 ∈ V)

def cl {n : ℕ} {a : Fin n → ℕ} (x : Raw a → Bool) (S : Finset (Raw a)) : Clause (Raw a) :=
  S.image (fun z => (z, !(x z)))

def lifted {n : ℕ} (a : Fin n → ℕ) (F : Set (Clause (Fin n))) : Set (Clause (Raw a)) :=
  {A | ∃ C ∈ F, ∃ x : Raw a → Bool, (∀ l ∈ C, val a x l.1 ≠ l.2) ∧
    A = cl x (blk a (C.image Prod.fst))}

def can {n : ℕ} (a : Fin n → ℕ) (F : Set (Clause (Fin n))) (W : ℕ) : Prop :=
  ∃ π : List (Clause (Raw a)), IsRefutation (lifted a F) π ∧ ∀ C ∈ π, C.card ≤ W

inductive LD {n : ℕ} (a : Fin n → ℕ) (F : Set (Clause (Fin n))) (W : ℕ) :
    Clause (Raw a) → Prop
  | ax {A : Clause (Raw a)} : A ∈ lifted a F → A.card ≤ W → LD a F W A
  | res {A1 A2 R : Clause (Raw a)} : LD a F W A1 → LD a F W A2 → IsResolvent A1 A2 R →
      R.card ≤ W → LD a F W R

def wt {n : ℕ} (w : Fin n → ℕ) (V : Finset (Fin n)) : ℕ := ∑ v ∈ V, w v

inductive Der {n : ℕ} (w : Fin n → ℕ) (F : Set (Clause (Fin n))) (i s : ℕ) :
    Clause (Fin n) → Prop
  | ax {C : Clause (Fin n)} : C ∈ F → wt w (C.image Prod.fst) ≤ i → Der w F i s C
  | res {B1 B2 : Clause (Fin n)} {v : Fin n} : Der w F i s B1 → Der w F i s B2 →
      (v, true) ∈ B1 → (v, false) ∈ B2 → (v, false) ∉ B1 → (v, true) ∉ B2 →
      wt w (B1.image Prod.fst ∪ B2.image Prod.fst) ≤ s →
      Der w F i s (B1.erase (v, true) ∪ B2.erase (v, false))

def Fals {V : Type} (x : V → Bool) (A : Clause V) : Prop := ∀ m ∈ A, x m.1 ≠ m.2

def InvLit {n : ℕ} (a : Fin n → ℕ) (A : Clause (Raw a)) (l : Literal (Fin n)) : Prop :=
  (∀ j : Fin (a l.1), (⟨l.1, j⟩ : Raw a) ∈ A.image Prod.fst) ∧
    ∀ x : Raw a → Bool, Fals x A → val a x l.1 ≠ l.2

def seg {n : ℕ} (a : Fin n → ℕ) (V0 : Finset (Fin n)) (v : Fin n) (k : ℕ) : Finset (Raw a) :=
  blk a V0 ∪ (Finset.univ : Finset (Raw a)).filter (fun z => z.1 = v ∧ z.2.val < k)

theorem deriv_append {V : Type} [DecidableEq V] {G : Set (Clause V)} {π1 π2 : List (Clause V)}
    (h1 : IsDerivation G π1) (h2 : IsDerivation G π2) : IsDerivation G (π1 ++ π2) := by
  induction h1 with
  | nil => simpa using h2
  | ax _ hC ih => exact IsDerivation.ax ih hC
  | res _ hC hD hR ih =>
    exact IsDerivation.res ih (List.mem_append_left _ hC) (List.mem_append_left _ hD) hR

theorem LD_of_deriv {n : ℕ} {a : Fin n → ℕ} {F : Set (Clause (Fin n))} {W : ℕ}
    {π : List (Clause (Raw a))} (h : IsDerivation (lifted a F) π) :
    (∀ C ∈ π, C.card ≤ W) → ∀ C ∈ π, LD a F W C := by
  induction h with
  | nil => intro _ C hC; simp at hC
  | ax _ hC ih =>
    intro hw C' hC'
    rcases List.mem_cons.1 hC' with rfl | h'
    · exact LD.ax hC (hw _ (by simp))
    · exact ih (fun D hD => hw D (List.mem_cons_of_mem _ hD)) C' h'
  | res _ hC hD hR ih =>
    intro hw C' hC'
    have ih' := ih (fun D hD => hw D (List.mem_cons_of_mem _ hD))
    rcases List.mem_cons.1 hC' with rfl | h'
    · exact LD.res (ih' _ hC) (ih' _ hD) hR (hw _ (by simp))
    · exact ih' C' h'

theorem deriv_of_LD {n : ℕ} {a : Fin n → ℕ} {F : Set (Clause (Fin n))} {W : ℕ}
    {A : Clause (Raw a)} (h : LD a F W A) :
    ∃ π : List (Clause (Raw a)), IsDerivation (lifted a F) π ∧
      (∀ C ∈ π, C.card ≤ W) ∧ A ∈ π := by
  induction h with
  | ax hA hW =>
    exact ⟨[_], IsDerivation.ax IsDerivation.nil hA, by simpa using hW, by simp⟩
  | res _ _ hR hW ih1 ih2 =>
    obtain ⟨π1, d1, w1, m1⟩ := ih1
    obtain ⟨π2, d2, w2, m2⟩ := ih2
    refine ⟨_ :: (π1 ++ π2), IsDerivation.res (deriv_append d1 d2)
      (List.mem_append_left _ m1) (List.mem_append_right _ m2) hR, ?_, by simp⟩
    intro C hC
    rcases List.mem_cons.1 hC with rfl | hC
    · exact hW
    · rcases List.mem_append.1 hC with hC | hC
      · exact w1 C hC
      · exact w2 C hC

theorem can_iff {n : ℕ} (a : Fin n → ℕ) (F : Set (Clause (Fin n))) (W : ℕ) :
    can a F W ↔ LD a F W ∅ := by
  constructor
  · rintro ⟨π, ⟨hd, he⟩, hw⟩
    exact LD_of_deriv hd hw _ he
  · intro h
    obtain ⟨π, hd, hw, he⟩ := deriv_of_LD h
    exact ⟨π, ⟨hd, he⟩, hw⟩

theorem val_congr {n : ℕ} {a : Fin n → ℕ} {x y : Raw a → Bool} {u : Fin n}
    (h : ∀ j : Fin (a u), x ⟨u, j⟩ = y ⟨u, j⟩) : val a x u = val a y u := by
  unfold val
  simp only [h]

theorem val_update_other {n : ℕ} {a : Fin n → ℕ} (x : Raw a → Bool) (z : Raw a) (b : Bool)
    {u : Fin n} (hu : u ≠ z.1) : val a (Function.update x z b) u = val a x u := by
  apply val_congr
  intro j
  exact Function.update_of_ne (fun h => hu (congrArg Sigma.fst h)) _ _

theorem val_flip {n : ℕ} {a : Fin n → ℕ} (x : Raw a → Bool) (z : Raw a) :
    val a (Function.update x z true) z.1 ≠ val a (Function.update x z false) z.1 := by
  obtain ⟨v, i⟩ := z
  have e1 : (Finset.univ : Finset (Fin (a v))).filter
      (fun j => Function.update x ⟨v, i⟩ true ⟨v, j⟩ = true) =
      insert i ((Finset.univ : Finset (Fin (a v))).filter
        (fun j => j ≠ i ∧ x ⟨v, j⟩ = true)) := by
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_apply, h]
  have e2 : (Finset.univ : Finset (Fin (a v))).filter
      (fun j => Function.update x ⟨v, i⟩ false ⟨v, j⟩ = true) =
      ((Finset.univ : Finset (Fin (a v))).filter (fun j => j ≠ i ∧ x ⟨v, j⟩ = true)) := by
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_apply, h]
  unfold val
  rw [e1, e2, Finset.card_insert_of_notMem (by simp)]
  rw [ne_eq, decide_eq_decide, Nat.odd_add_one]
  tauto

theorem mem_cl {n : ℕ} {a : Fin n → ℕ} {x : Raw a → Bool} {S : Finset (Raw a)} {z : Raw a}
    {b : Bool} : (z, b) ∈ cl x S ↔ z ∈ S ∧ b = !(x z) := by
  unfold cl
  constructor
  · intro h
    obtain ⟨z', hz', he⟩ := Finset.mem_image.1 h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨hz', rfl⟩
  · rintro ⟨hz, rfl⟩
    exact Finset.mem_image_of_mem _ hz

theorem cl_fst {n : ℕ} {a : Fin n → ℕ} (x : Raw a → Bool) (S : Finset (Raw a)) :
    (cl x S).image Prod.fst = S := by
  unfold cl
  rw [Finset.image_image]
  exact Finset.image_id

theorem card_cl {n : ℕ} {a : Fin n → ℕ} (x : Raw a → Bool) (S : Finset (Raw a)) :
    (cl x S).card = S.card :=
  Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)

theorem card_blk {n : ℕ} (a : Fin n → ℕ) (V : Finset (Fin n)) : (blk a V).card = wt a V := by
  have : blk a V = V.sigma (fun v => (Finset.univ : Finset (Fin (a v)))) := by
    ext z; simp [blk]
  rw [this, Finset.card_sigma]
  simp [wt]

theorem blk_union {n : ℕ} (a : Fin n → ℕ) (X Y : Finset (Fin n)) :
    blk a (X ∪ Y) = blk a X ∪ blk a Y := by
  ext z; simp [blk]

theorem fals_cl {n : ℕ} {a : Fin n → ℕ} {x y : Raw a → Bool} {S : Finset (Raw a)} :
    Fals y (cl x S) ↔ ∀ z ∈ S, y z = x z := by
  constructor
  · intro h z hz
    have := h (z, !(x z)) (mem_cl.2 ⟨hz, rfl⟩)
    revert this
    cases y z <;> cases x z <;> simp
  · intro h m hm
    obtain ⟨u, c⟩ := m
    obtain ⟨hu, rfl⟩ := mem_cl.1 hm
    simp [h u hu]

theorem res_cl {n : ℕ} {a : Fin n → ℕ} (y : Raw a → Bool) (z : Raw a) (S1 S2 : Finset (Raw a))
    (h1 : z ∈ S1) (h2 : z ∈ S2) :
    IsResolvent (cl (Function.update y z false) S1) (cl (Function.update y z true) S2)
      (cl y ((S1 ∪ S2).erase z)) := by
  refine ⟨z, mem_cl.2 ⟨h1, by simp⟩, mem_cl.2 ⟨h2, by simp⟩, ?_⟩
  ext ⟨u, b⟩
  simp only [Finset.mem_union, Finset.mem_erase, mem_cl, ne_eq, Prod.mk.injEq]
  by_cases hu : u = z
  · subst hu; simp; tauto
  · simp only [Function.update_apply, hu, ite_false]
    tauto

theorem der_map {n : ℕ} {w1 w2 : Fin n → ℕ} {F : Set (Clause (Fin n))} {i1 s1 i2 s2 : ℕ}
    (hi : ∀ V, wt w1 V ≤ i1 → wt w2 V ≤ i2) (hs : ∀ V, wt w1 V ≤ s1 → wt w2 V ≤ s2)
    {B : Clause (Fin n)} (h : Der w1 F i1 s1 B) : Der w2 F i2 s2 B := by
  induction h with
  | ax hC hw => exact Der.ax hC (hi _ hw)
  | res _ _ h1 h2 h1' h2' hU ih1 ih2 => exact Der.res ih1 ih2 h1 h2 h1' h2' (hs _ hU)

theorem der_res_gen {n : ℕ} {w : Fin n → ℕ} {F : Set (Clause (Fin n))} {i s : ℕ}
    {B1 B2 : Clause (Fin n)} {v : Fin n} (p : Bool) (d1 : Der w F i s B1) (d2 : Der w F i s B2)
    (h1 : (v, p) ∈ B1) (h2 : (v, !p) ∈ B2) (h1' : (v, !p) ∉ B1) (h2' : (v, p) ∉ B2)
    (hU : wt w (B1.image Prod.fst ∪ B2.image Prod.fst) ≤ s) :
    Der w F i s (B1.erase (v, p) ∪ B2.erase (v, !p)) := by
  cases p with
  | true => exact Der.res d1 d2 h1 h2 h1' h2' hU
  | false =>
    rw [Finset.union_comm]
    exact Der.res d2 d1 h2 h1 h2' h1' (by rwa [Finset.union_comm])

theorem seg_zero {n : ℕ} (a : Fin n → ℕ) (V0 : Finset (Fin n)) (v : Fin n) :
    seg a V0 v 0 = blk a V0 := by
  ext z; simp [seg]

theorem seg_mono {n : ℕ} (a : Fin n → ℕ) (V0 : Finset (Fin n)) (v : Fin n) {k k' : ℕ}
    (h : k ≤ k') : seg a V0 v k ⊆ seg a V0 v k' := by
  intro z hz
  simp only [seg, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  rcases hz with hz | ⟨h1, h2⟩
  · exact Or.inl hz
  · exact Or.inr ⟨h1, by omega⟩

theorem mem_seg_succ {n : ℕ} (a : Fin n → ℕ) (V0 : Finset (Fin n)) {v : Fin n} {z : Raw a}
    (hz : z.1 = v) : z ∈ seg a V0 v (z.2.val + 1) := by
  simp [seg, hz]

theorem seg_last {n : ℕ} (a : Fin n → ℕ) {V0 : Finset (Fin n)} {v : Fin n} (hv0 : v ∉ V0)
    {z : Raw a} (hz : z.1 = v) (hk : z.2.val + 1 = a v) :
    (blk a (insert v V0)).erase z = seg a V0 v z.2.val := by
  obtain ⟨zv, zj⟩ := z
  simp only at hz hk
  subst hz
  ext ⟨u, j⟩
  simp only [seg, blk, Finset.mem_erase, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, ne_eq]
  by_cases hu : u = zv
  · subst hu
    have := j.isLt
    simp [hv0, Fin.ext_iff]
    omega
  · simp [hu]

theorem seg_step {n : ℕ} (a : Fin n → ℕ) {V0 : Finset (Fin n)} {v : Fin n} (hv0 : v ∉ V0)
    {z : Raw a} (hz : z.1 = v) :
    (seg a V0 v (z.2.val + 1)).erase z = seg a V0 v z.2.val := by
  obtain ⟨zv, zj⟩ := z
  simp only at hz
  subst hz
  ext ⟨u, j⟩
  simp only [seg, blk, Finset.mem_erase, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and, ne_eq]
  by_cases hu : u = zv
  · subst hu
    simp [hv0, Fin.ext_iff]
    omega
  · simp [hu]

theorem upper_step {n : ℕ} {a : Fin n → ℕ} (ha : ∀ v, 0 < a v) {F : Set (Clause (Fin n))}
    {W : ℕ} {B1 B2 : Clause (Fin n)} {v : Fin n}
    (h1 : (v, true) ∈ B1) (h2 : (v, false) ∈ B2) (h1' : (v, false) ∉ B1) (h2' : (v, true) ∉ B2)
    (hs : wt a (B1.image Prod.fst ∪ B2.image Prod.fst) ≤ W + 1)
    (ih1 : ∀ x : Raw a → Bool, (∀ l ∈ B1, val a x l.1 ≠ l.2) →
      LD a F W (cl x (blk a (B1.image Prod.fst))))
    (ih2 : ∀ x : Raw a → Bool, (∀ l ∈ B2, val a x l.1 ≠ l.2) →
      LD a F W (cl x (blk a (B2.image Prod.fst)))) :
    ∀ x : Raw a → Bool, (∀ l ∈ B1.erase (v, true) ∪ B2.erase (v, false), val a x l.1 ≠ l.2) →
      LD a F W (cl x (blk a ((B1.erase (v, true) ∪ B2.erase (v, false)).image Prod.fst))) := by
  generalize hB : B1.erase (v, true) ∪ B2.erase (v, false) = B
  generalize hV0 : B.image Prod.fst = V0
  have p1 : ∀ l ∈ B1, l.1 = v → l.2 = true := by
    rintro ⟨u, c⟩ hl hlv
    simp only at hlv
    subst hlv
    cases c
    · exact absurd hl h1'
    · rfl
  have p2 : ∀ l ∈ B2, l.1 = v → l.2 = false := by
    rintro ⟨u, c⟩ hl hlv
    simp only at hlv
    subst hlv
    cases c
    · rfl
    · exact absurd hl h2'
  have q1 : ∀ l ∈ B1, l.1 ≠ v → l ∈ B := by
    intro l hl hne
    rw [← hB]
    exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨fun h => hne (by rw [h]), hl⟩)
  have q2 : ∀ l ∈ B2, l.1 ≠ v → l ∈ B := by
    intro l hl hne
    rw [← hB]
    exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨fun h => hne (by rw [h]), hl⟩)
  have hv0 : v ∉ V0 := by
    intro hv
    rw [← hV0] at hv
    obtain ⟨l, hl, hlv⟩ := Finset.mem_image.1 hv
    rw [← hB] at hl
    rcases Finset.mem_union.1 hl with hl | hl
    · obtain ⟨hne, hl⟩ := Finset.mem_erase.1 hl
      exact hne (Prod.ext hlv (p1 l hl hlv))
    · obtain ⟨hne, hl⟩ := Finset.mem_erase.1 hl
      exact hne (Prod.ext hlv (p2 l hl hlv))
  have hU : B1.image Prod.fst ∪ B2.image Prod.fst = insert v V0 := by
    ext u
    rw [← hV0]
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro (⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩)
      · by_cases h : l.1 = v
        · exact Or.inl h
        · exact Or.inr ⟨l, q1 l hl h, rfl⟩
      · by_cases h : l.1 = v
        · exact Or.inl h
        · exact Or.inr ⟨l, q2 l hl h, rfl⟩
    · rintro (rfl | ⟨l, hl, rfl⟩)
      · exact Or.inl ⟨_, h1, rfl⟩
      · rw [← hB] at hl
        rcases Finset.mem_union.1 hl with hl | hl
        · exact Or.inl ⟨l, (Finset.mem_erase.1 hl).2, rfl⟩
        · exact Or.inr ⟨l, (Finset.mem_erase.1 hl).2, rfl⟩
  have hwt : a v + wt a V0 ≤ W + 1 := by
    rw [hU] at hs
    unfold wt at hs ⊢
    rwa [Finset.sum_insert hv0] at hs
  have hBv : ∀ l ∈ B, l.1 ≠ v := by
    intro l hl e
    apply hv0
    rw [← hV0]
    exact Finset.mem_image.2 ⟨l, hl, e⟩
  have hTcard : ∀ k, k + 1 ≤ a v → (seg a V0 v k).card ≤ W := by
    intro k hk
    have hz : (⟨v, ⟨a v - 1, by omega⟩⟩ : Raw a) ∈ blk a (insert v V0) := by simp [blk]
    have e := seg_last a hv0 (z := (⟨v, ⟨a v - 1, by omega⟩⟩ : Raw a)) rfl
      (by simp only; omega)
    calc (seg a V0 v k).card ≤ (seg a V0 v (a v - 1)).card :=
          Finset.card_le_card (seg_mono a V0 v (by omega))
      _ = ((blk a (insert v V0)).erase ⟨v, ⟨a v - 1, by omega⟩⟩).card := by rw [e]
      _ = (blk a (insert v V0)).card - 1 := Finset.card_erase_of_mem hz
      _ ≤ W := by
          rw [card_blk]
          unfold wt
          rw [Finset.sum_insert hv0]
          unfold wt at hwt
          omega
  have fB : ∀ (y : Raw a → Bool) (z : Raw a) (c : Bool), z.1 = v →
      (∀ l ∈ B, val a y l.1 ≠ l.2) → ∀ l ∈ B, val a (Function.update y z c) l.1 ≠ l.2 := by
    intro y z c hz hy l hl
    rw [val_update_other _ _ _ (by rw [hz]; exact hBv l hl)]
    exact hy l hl
  have fB1 : ∀ (y : Raw a → Bool) (z : Raw a) (c : Bool), z.1 = v →
      (∀ l ∈ B, val a y l.1 ≠ l.2) → val a (Function.update y z c) v = false →
      ∀ l ∈ B1, val a (Function.update y z c) l.1 ≠ l.2 := by
    intro y z c hz hy hval l hl
    by_cases hlv : l.1 = v
    · rw [hlv, hval, p1 l hl hlv]
      simp
    · rw [val_update_other _ _ _ (by rw [hz]; exact hlv)]
      exact hy l (q1 l hl hlv)
  have fB2 : ∀ (y : Raw a → Bool) (z : Raw a) (c : Bool), z.1 = v →
      (∀ l ∈ B, val a y l.1 ≠ l.2) → val a (Function.update y z c) v = true →
      ∀ l ∈ B2, val a (Function.update y z c) l.1 ≠ l.2 := by
    intro y z c hz hy hval l hl
    by_cases hlv : l.1 = v
    · rw [hlv, hval, p2 l hl hlv]
      simp
    · rw [val_update_other _ _ _ (by rw [hz]; exact hlv)]
      exact hy l (q2 l hl hlv)
  have hvB1 : v ∈ B1.image Prod.fst := Finset.mem_image.2 ⟨_, h1, rfl⟩
  have hvB2 : v ∈ B2.image Prod.fst := Finset.mem_image.2 ⟨_, h2, rfl⟩
  have main : ∀ i k, k + 1 + i = a v → ∀ y : Raw a → Bool, (∀ l ∈ B, val a y l.1 ≠ l.2) →
      LD a F W (cl y (seg a V0 v k)) := by
    intro i
    induction i with
    | zero =>
      intro k hk y hy
      have hkv : k < a v := by omega
      obtain ⟨z, hz⟩ : ∃ z : Raw a, z = ⟨v, ⟨k, hkv⟩⟩ := ⟨_, rfl⟩
      have hzv : z.1 = v := by rw [hz]
      have hzk : z.2.val = k := by subst hz; rfl
      have hz1 : z ∈ blk a (B1.image Prod.fst) := by
        simp only [blk, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hzv]
        exact hvB1
      have hz2 : z ∈ blk a (B2.image Prod.fst) := by
        simp only [blk, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hzv]
        exact hvB2
      have hflip : val a (Function.update y z true) v ≠ val a (Function.update y z false) v := by
        have := val_flip y z
        rwa [hzv] at this
      have hset : (blk a (B1.image Prod.fst) ∪ blk a (B2.image Prod.fst)).erase z =
          seg a V0 v k := by
        rw [← blk_union, hU, seg_last a hv0 hzv (by omega), hzk]
      have hcard := hTcard k (by omega)
      cases hc : val a (Function.update y z false) v with
      | false =>
        have ht : val a (Function.update y z true) v = true := by
          revert hflip; rw [hc]; cases val a (Function.update y z true) v <;> simp
        have L1 := ih1 _ (fB1 y z false hzv hy hc)
        have L2 := ih2 _ (fB2 y z true hzv hy ht)
        have R := res_cl y z _ _ hz1 hz2
        rw [hset] at R
        exact LD.res L1 L2 R (by rw [card_cl]; exact hcard)
      | true =>
        have ht : val a (Function.update y z true) v = false := by
          revert hflip; rw [hc]; cases val a (Function.update y z true) v <;> simp
        have L1 := ih1 _ (fB1 y z true hzv hy ht)
        have L2 := ih2 _ (fB2 y z false hzv hy hc)
        have R := res_cl y z _ _ hz2 hz1
        rw [Finset.union_comm, hset] at R
        exact LD.res L2 L1 R (by rw [card_cl]; exact hcard)
    | succ i ih =>
      intro k hk y hy
      have hkv : k < a v := by omega
      obtain ⟨z, hz⟩ : ∃ z : Raw a, z = ⟨v, ⟨k, hkv⟩⟩ := ⟨_, rfl⟩
      have hzv : z.1 = v := by rw [hz]
      have hzk : z.2.val = k := by subst hz; rfl
      have L1 := ih (k + 1) (by omega) _ (fB y z false hzv hy)
      have L2 := ih (k + 1) (by omega) _ (fB y z true hzv hy)
      have hzT : z ∈ seg a V0 v (k + 1) := by
        have := mem_seg_succ a V0 hzv
        rwa [hzk] at this
      have R := res_cl y z _ _ hzT hzT
      have e := seg_step a hv0 hzv
      rw [hzk] at e
      rw [Finset.union_self, e] at R
      exact LD.res L1 L2 R (by rw [card_cl]; exact hTcard k (by omega))
  intro x hx
  have := main (a v - 1) 0 (by have := ha v; omega) x hx
  rwa [seg_zero] at this

theorem upper {n : ℕ} {a : Fin n → ℕ} (ha : ∀ v, 0 < a v) {F : Set (Clause (Fin n))} {W : ℕ}
    {B : Clause (Fin n)} (hB : Der a F W (W + 1) B) :
    ∀ x : Raw a → Bool, (∀ l ∈ B, val a x l.1 ≠ l.2) →
      LD a F W (cl x (blk a (B.image Prod.fst))) := by
  induction hB with
  | ax hC hwt =>
    intro x hx
    exact LD.ax ⟨_, hC, x, hx, rfl⟩ (by rw [card_cl, card_blk]; exact hwt)
  | res _ _ h1 h2 h1' h2' hs ih1 ih2 =>
    exact upper_step ha h1 h2 h1' h2' hs ih1 ih2

theorem invlit_mono {n : ℕ} {a : Fin n → ℕ} {A R : Clause (Raw a)} (hsub : A ⊆ R)
    {l : Literal (Fin n)} (h : InvLit a A l) : InvLit a R l :=
  ⟨fun j => Finset.image_subset_image hsub (h.1 j),
    fun x hx => h.2 x (fun m hm => hx m (hsub hm))⟩

theorem invlit_transfer {n : ℕ} {a : Fin n → ℕ} {A R : Clause (Raw a)} {z : Raw a} {b : Bool}
    {l : Literal (Fin n)}
    (hsub : ∀ m ∈ A, m.1 ≠ z → m ∈ R) (hf : ∀ x, Fals x R → Fals (Function.update x z b) A)
    (hl : l.1 ≠ z.1) (h : InvLit a A l) : InvLit a R l := by
  refine ⟨fun j => ?_, fun x hx => ?_⟩
  · obtain ⟨m, hm, hmj⟩ := Finset.mem_image.1 (h.1 j)
    have hmz : m.1 ≠ z := by
      rw [hmj]
      intro e
      exact hl (congrArg Sigma.fst e)
    exact Finset.mem_image.2 ⟨m, hsub m hm hmz, hmj⟩
  · have := h.2 _ (hf x hx)
    rwa [val_update_other _ _ _ hl] at this

theorem bool_aux {p q c d : Bool} (h : p ≠ q) (h1 : p ≠ c) (h2 : q ≠ d) : c = !d := by
  revert h h1 h2
  cases p <;> cases q <;> cases c <;> cases d <;> decide

theorem bool_aux2 {p c d : Bool} (h1 : p ≠ c) (h2 : p ≠ d) : c = d := by
  revert h1 h2
  cases p <;> cases c <;> cases d <;> decide

theorem lower_step {n : ℕ} {a : Fin n → ℕ} {F : Set (Clause (Fin n))} {W : ℕ}
    {A1 A2 : Clause (Raw a)} {z : Raw a}
    (hz1 : (z, true) ∈ A1) (hz2 : (z, false) ∈ A2)
    (hW : (A1.erase (z, true) ∪ A2.erase (z, false)).card ≤ W)
    (ih1 : (∃ x, Fals x A1) → ∃ B, Der a F W (W + 1) B ∧ ∀ l ∈ B, InvLit a A1 l)
    (ih2 : (∃ x, Fals x A2) → ∃ B, Der a F W (W + 1) B ∧ ∀ l ∈ B, InvLit a A2 l)
    (x0 : Raw a → Bool) (hx0 : Fals x0 (A1.erase (z, true) ∪ A2.erase (z, false))) :
    ∃ B, Der a F W (W + 1) B ∧
      ∀ l ∈ B, InvLit a (A1.erase (z, true) ∪ A2.erase (z, false)) l := by
  generalize hR : A1.erase (z, true) ∪ A2.erase (z, false) = R at hW hx0 ⊢
  by_cases c1 : (z, false) ∈ A1
  · have hsub : A2 ⊆ R := by
      intro m hm
      rw [← hR]
      by_cases e : m = (z, false)
      · subst e
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨by simp, c1⟩)
      · exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨e, hm⟩)
    obtain ⟨B, hB, hI⟩ := ih2 ⟨x0, fun m hm => hx0 m (hsub hm)⟩
    exact ⟨B, hB, fun l hl => invlit_mono hsub (hI l hl)⟩
  by_cases c2 : (z, true) ∈ A2
  · have hsub : A1 ⊆ R := by
      intro m hm
      rw [← hR]
      by_cases e : m = (z, true)
      · subst e
        exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨by simp, c2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨e, hm⟩)
    obtain ⟨B, hB, hI⟩ := ih1 ⟨x0, fun m hm => hx0 m (hsub hm)⟩
    exact ⟨B, hB, fun l hl => invlit_mono hsub (hI l hl)⟩
  have hs1 : ∀ m ∈ A1, m.1 ≠ z → m ∈ R := by
    intro m hm hne
    rw [← hR]
    exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨fun e => hne (by rw [e]), hm⟩)
  have hs2 : ∀ m ∈ A2, m.1 ≠ z → m ∈ R := by
    intro m hm hne
    rw [← hR]
    exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨fun e => hne (by rw [e]), hm⟩)
  have hf1 : ∀ x, Fals x R → Fals (Function.update x z false) A1 := by
    intro x hx m hm
    by_cases e : m.1 = z
    · obtain ⟨u, c⟩ := m
      simp only at e
      subst e
      cases c
      · exact absurd hm c1
      · simp
    · rw [Function.update_of_ne e]
      exact hx m (hs1 m hm e)
  have hf2 : ∀ x, Fals x R → Fals (Function.update x z true) A2 := by
    intro x hx m hm
    by_cases e : m.1 = z
    · obtain ⟨u, c⟩ := m
      simp only at e
      subst e
      cases c
      · simp
      · exact absurd hm c2
    · rw [Function.update_of_ne e]
      exact hx m (hs2 m hm e)
  obtain ⟨B1, d1, I1⟩ := ih1 ⟨_, hf1 x0 hx0⟩
  obtain ⟨B2, d2, I2⟩ := ih2 ⟨_, hf2 x0 hx0⟩
  by_cases e1 : ∀ l ∈ B1, l.1 ≠ z.1
  · exact ⟨B1, d1, fun l hl => invlit_transfer hs1 hf1 (e1 l hl) (I1 l hl)⟩
  by_cases e2 : ∀ l ∈ B2, l.1 ≠ z.1
  · exact ⟨B2, d2, fun l hl => invlit_transfer hs2 hf2 (e2 l hl) (I2 l hl)⟩
  simp only [not_forall, not_not] at e1 e2
  obtain ⟨l1, hl1, hl1v⟩ := e1
  obtain ⟨l2, hl2, hl2v⟩ := e2
  have hflip := val_flip x0 z
  have P1 : ∀ l ∈ B1, l.1 = z.1 → l.2 = l1.2 := by
    intro l hl hlv
    have a1 := (I1 l hl).2 _ (hf1 x0 hx0)
    have a2 := (I1 l1 hl1).2 _ (hf1 x0 hx0)
    rw [hlv] at a1
    rw [hl1v] at a2
    exact bool_aux2 a1 a2
  have P2 : ∀ l ∈ B2, l.1 = z.1 → l.2 = !l1.2 := by
    intro l hl hlv
    have a1 := (I2 l hl).2 _ (hf2 x0 hx0)
    have a2 := (I1 l1 hl1).2 _ (hf1 x0 hx0)
    rw [hlv] at a1
    rw [hl1v] at a2
    exact bool_aux hflip a1 a2
  have mem1 : (z.1, l1.2) ∈ B1 := by
    have : l1 = (z.1, l1.2) := Prod.ext hl1v rfl
    rw [← this]; exact hl1
  have mem2 : (z.1, !l1.2) ∈ B2 := by
    have : l2 = (z.1, !l1.2) := Prod.ext hl2v (P2 l2 hl2 hl2v)
    rw [← this]; exact hl2
  have nmem1 : (z.1, !l1.2) ∉ B1 := by
    intro h
    have := P1 _ h rfl
    revert this; cases l1.2 <;> simp
  have nmem2 : (z.1, l1.2) ∉ B2 := by
    intro h
    have := P2 _ h rfl
    revert this; cases l1.2 <;> simp
  have hU : wt a (B1.image Prod.fst ∪ B2.image Prod.fst) ≤ W + 1 := by
    rw [← card_blk]
    have hsubU : blk a (B1.image Prod.fst ∪ B2.image Prod.fst) ⊆
        insert z (R.image Prod.fst) := by
      rintro ⟨u, j⟩ hu
      simp only [blk, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_image] at hu
      rcases hu with ⟨⟨lv, lb⟩, hl, hlu⟩ | ⟨⟨lv, lb⟩, hl, hlu⟩
      · simp only at hlu
        subst hlu
        obtain ⟨m, hm, hmj⟩ := Finset.mem_image.1 ((I1 _ hl).1 j)
        by_cases e : m.1 = z
        · rw [← hmj, e]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨m, hs1 m hm e, hmj⟩)
      · simp only at hlu
        subst hlu
        obtain ⟨m, hm, hmj⟩ := Finset.mem_image.1 ((I2 _ hl).1 j)
        by_cases e : m.1 = z
        · rw [← hmj, e]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨m, hs2 m hm e, hmj⟩)
    have c1 := Finset.card_le_card hsubU
    have c2 := Finset.card_insert_le z (R.image Prod.fst)
    have c3 : (R.image Prod.fst).card ≤ R.card := Finset.card_image_le
    omega
  refine ⟨B1.erase (z.1, l1.2) ∪ B2.erase (z.1, !l1.2),
    der_res_gen l1.2 d1 d2 mem1 mem2 nmem1 nmem2 hU, ?_⟩
  intro l hl
  rcases Finset.mem_union.1 hl with hl | hl
  · obtain ⟨hne, hl⟩ := Finset.mem_erase.1 hl
    have : l.1 ≠ z.1 := fun e => hne (Prod.ext e (P1 l hl e))
    exact invlit_transfer hs1 hf1 this (I1 l hl)
  · obtain ⟨hne, hl⟩ := Finset.mem_erase.1 hl
    have : l.1 ≠ z.1 := fun e => hne (Prod.ext e (P2 l hl e))
    exact invlit_transfer hs2 hf2 this (I2 l hl)

theorem lower {n : ℕ} {a : Fin n → ℕ} {F : Set (Clause (Fin n))} {W : ℕ}
    {A : Clause (Raw a)} (h : LD a F W A) :
    (∃ x, Fals x A) → ∃ B, Der a F W (W + 1) B ∧ ∀ l ∈ B, InvLit a A l := by
  induction h with
  | ax hA hW =>
    intro _
    obtain ⟨C, hC, x0, hx0, rfl⟩ := hA
    have hmem : ∀ l ∈ C, ∀ j : Fin (a l.1), (⟨l.1, j⟩ : Raw a) ∈ blk a (C.image Prod.fst) := by
      intro l hl j
      simp only [blk, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.mem_image_of_mem _ hl
    refine ⟨C, Der.ax hC ?_, fun l hl => ⟨fun j => ?_, fun x hx => ?_⟩⟩
    · rw [← card_blk, ← card_cl x0]; exact hW
    · rw [cl_fst]; exact hmem l hl j
    · have hagree := fals_cl.1 hx
      rw [val_congr (fun j => hagree _ (hmem l hl j))]
      exact hx0 l hl
  | res _ _ hR hW ih1 ih2 =>
    rintro ⟨x0, hx0⟩
    obtain ⟨z, hz1, hz2, rfl⟩ := hR
    exact lower_step hz1 hz2 hW ih1 ih2 x0 hx0

theorem charac {n : ℕ} (w : Fin n → ℕ) (hw : ∀ v, 0 < w v) (F : Set (Clause (Fin n)))
    (t : ℕ) (ht : 0 < t) (W : ℕ) :
    can (fun v => t * w v) F W ↔ Der w F (W / t) ((W + 1) / t) ∅ := by
  have ha : ∀ v, 0 < (fun v => t * w v) v := fun v => Nat.mul_pos ht (hw v)
  have hwt : ∀ V, wt (fun v => t * w v) V = wt w V * t := by
    intro V
    unfold wt
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun v _ => mul_comm _ _)
  rw [can_iff]
  constructor
  · intro h
    obtain ⟨B, hB, hI⟩ := lower h ⟨fun _ => true, fun m hm => by simp at hm⟩
    have hBe : B = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro l hl
      have := (hI l hl).1 ⟨0, ha l.1⟩
      simp at this
    subst hBe
    refine der_map ?_ ?_ hB
    · intro V hV
      rw [hwt] at hV
      exact (Nat.le_div_iff_mul_le ht).2 hV
    · intro V hV
      rw [hwt] at hV
      exact (Nat.le_div_iff_mul_le ht).2 hV
  · intro h
    have h' : Der (fun v => t * w v) F W (W + 1) ∅ := by
      refine der_map ?_ ?_ h
      · intro V hV
        rw [hwt]
        exact (Nat.le_div_iff_mul_le ht).1 hV
      · intro V hV
        rw [hwt]
        exact (Nat.le_div_iff_mul_le ht).1 hV
    have := upper ha h' (fun _ => true) (by simp)
    simpa [cl, blk] using this

theorem der_mono {n : ℕ} {w : Fin n → ℕ} {F : Set (Clause (Fin n))} {i s i' s' : ℕ}
    (h : Der w F i s ∅) (hi : i ≤ i') (hs : s ≤ s') : Der w F i' s' ∅ :=
  der_map (fun _ hV => le_trans hV hi) (fun _ hV => le_trans hV hs) h

theorem div_le_of_lt {t W k : ℕ} (ht : 0 < t) (h : W < t * (k + 1)) : W / t ≤ k :=
  Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul ht).2 (by rw [mul_comm]; exact h))

theorem le_div_of_le {t W k : ℕ} (ht : 0 < t) (h : t * k ≤ W) : k ≤ W / t :=
  (Nat.le_div_iff_mul_le ht).2 (by rw [mul_comm]; exact h)

end PEqualNP.Outside.L_pcx_312

theorem PEqualNP.Outside.L_pcx_312 : (∀ (n : ℕ) (w : Fin n → ℕ), (∀ v, 0 < w v) →
  let Base := PEqualNP.ProofComplexity.Clause (Fin n)
  let can := fun (a : Fin n → ℕ) (F : Set Base) (W : ℕ) =>
    let Raw := (v : Fin n) × Fin (a v)
    let val := fun (x : Raw → Bool) (v : Fin n) =>
      decide (Odd (((Finset.univ : Finset (Fin (a v))).filter (fun j => x ⟨v,j⟩ = true)).card))
    let lifted : Set (PEqualNP.ProofComplexity.Clause Raw) := {A |
      ∃ C ∈ F, ∃ x : Raw → Bool, (∀ l ∈ C, val x l.1 ≠ l.2) ∧
        A = ((Finset.univ : Finset Raw).filter (fun z => z.1 ∈ C.image Prod.fst)).image
          (fun z => (z, !(x z)))}
    ∃ π : List (PEqualNP.ProofComplexity.Clause Raw),
      PEqualNP.ProofComplexity.IsRefutation lifted π ∧ ∀ C ∈ π, C.card ≤ W
  let scaled := fun (t : ℕ) (F : Set Base) (W : ℕ) => can (fun v => t * w v) F W
  ∀ (F : Set Base) (d : ℕ), scaled 1 F d → (∀ j < d, ¬ scaled 1 F j) →
    ∀ t : ℕ, 1 ≤ t → ∀ W : ℕ,
      Iff (scaled t F W)
        (@ite Prop (scaled 2 F (2*d)) (Classical.propDecidable _) (t*d ≤ W) (t*(d+1)-1 ≤ W))) := by
  intro n w hw Base can scaled F d hd hlt t ht W
  have key : ∀ t : ℕ, 0 < t → ∀ W : ℕ, scaled t F W ↔
      PEqualNP.Outside.L_pcx_312.Der w F (W / t) ((W + 1) / t) ∅ :=
    fun t ht W => PEqualNP.Outside.L_pcx_312.charac w hw F t ht W
  have hQ1 : PEqualNP.Outside.L_pcx_312.Der w F d (d + 1) ∅ := by
    simpa using (key 1 Nat.one_pos d).1 hd
  have hQ0 : ∀ j < d, ¬ PEqualNP.Outside.L_pcx_312.Der w F j (j + 1) ∅ :=
    fun j hj hq => hlt j hj ((key 1 Nat.one_pos j).2 (by simpa using hq))
  have h2 : scaled 2 F (2 * d) ↔ PEqualNP.Outside.L_pcx_312.Der w F d d ∅ := by
    rw [key 2 (by norm_num) (2 * d)]
    have e1 : 2 * d / 2 = d := by omega
    have e2 : (2 * d + 1) / 2 = d := by omega
    rw [e1, e2]
  have htp : 0 < t := ht
  refine (key t htp W).trans ?_
  have hmul : t * (d + 1) = t * d + t := by ring
  by_cases hc : scaled 2 F (2 * d)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    have hQd := h2.1 hc
    constructor
    · intro hq
      by_contra hlt'
      rw [not_le] at hlt'
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by
        rcases Nat.eq_zero_or_pos d with h0 | h0
        · subst h0; simp at hlt'
        · omega⟩
      apply hQ0 e (by omega)
      have hmul2 : t * (e + 1 + 1) = t * (e + 1) + t := by ring
      refine PEqualNP.Outside.L_pcx_312.der_mono hq ?_ ?_
      · exact PEqualNP.Outside.L_pcx_312.div_le_of_lt htp hlt'
      · exact PEqualNP.Outside.L_pcx_312.div_le_of_lt htp (by omega)
    · intro hle
      refine PEqualNP.Outside.L_pcx_312.der_mono hQd ?_ ?_
      · exact PEqualNP.Outside.L_pcx_312.le_div_of_le htp hle
      · exact PEqualNP.Outside.L_pcx_312.le_div_of_le htp (by omega)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    have hQd : ¬ PEqualNP.Outside.L_pcx_312.Der w F d d ∅ := fun h => hc (h2.2 h)
    constructor
    · intro hq
      by_contra hlt'
      rw [not_le] at hlt'
      apply hQd
      refine PEqualNP.Outside.L_pcx_312.der_mono hq ?_ ?_
      · exact PEqualNP.Outside.L_pcx_312.div_le_of_lt htp (by omega)
      · exact PEqualNP.Outside.L_pcx_312.div_le_of_lt htp (by omega)
    · intro hle
      refine PEqualNP.Outside.L_pcx_312.der_mono hQ1 ?_ ?_
      · exact PEqualNP.Outside.L_pcx_312.le_div_of_le htp (by omega)
      · exact PEqualNP.Outside.L_pcx_312.le_div_of_le htp (by omega)
