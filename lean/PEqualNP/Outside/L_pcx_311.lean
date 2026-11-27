import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_311_aux

open PEqualNP.ProofComplexity

variable {n : ℕ} {w : Fin n → ℕ} {F : Set (Clause (Fin n))} {W : ℕ}

abbrev Raw {n : ℕ} (w : Fin n → ℕ) := (v : Fin n) × Fin (w v)

def par (x : Raw w → Bool) (v : Fin n) : Bool :=
  decide (Odd (((Finset.univ : Finset (Fin (w v))).filter (fun j => x ⟨v, j⟩ = true)).card))

def blk (w : Fin n → ℕ) (S : Finset (Fin n)) : Finset (Raw w) :=
  (Finset.univ : Finset (Raw w)).filter (fun z => z.1 ∈ S)

def rc (X : Finset (Raw w)) (y : Raw w → Bool) : Clause (Raw w) :=
  X.image (fun z => (z, !(y z)))

def bv (C : Clause (Fin n)) : Finset (Fin n) := C.image Prod.fst

def lifted (w : Fin n → ℕ) (F : Set (Clause (Fin n))) : Set (Clause (Raw w)) :=
  {A | ∃ C ∈ F, ∃ x : Raw w → Bool, (∀ l ∈ C, par x l.1 ≠ l.2) ∧
    A = rc (blk w (C.image Prod.fst)) x}

def RD (w : Fin n → ℕ) (F : Set (Clause (Fin n))) (W : ℕ) (A : Clause (Raw w)) : Prop :=
  ∃ π : List (Clause (Raw w)), IsDerivation (lifted w F) π ∧ A ∈ π ∧ ∀ C ∈ π, C.card ≤ W

def SD (w : Fin n → ℕ) (F : Set (Clause (Fin n))) (W : ℕ) (A : Clause (Raw w)) : Prop :=
  ∃ B ⊆ A, RD w F W B

lemma deriv_append {V : Type} [DecidableEq V] {G : Set (Clause V)}
    {π₁ π₂ : List (Clause V)} (h₁ : IsDerivation G π₁) (h₂ : IsDerivation G π₂) :
    IsDerivation G (π₁ ++ π₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | ax _ hC ih => exact IsDerivation.ax ih hC
  | res _ hC hD hR ih =>
    exact IsDerivation.res ih (List.mem_append_left _ hC) (List.mem_append_left _ hD) hR

lemma rd_res {A B R : Clause (Raw w)} (h1 : RD w F W A) (h2 : RD w F W B)
    (hres : IsResolvent A B R) (hR : R.card ≤ W) : RD w F W R := by
  obtain ⟨π1, hd1, hm1, hw1⟩ := h1
  obtain ⟨π2, hd2, hm2, hw2⟩ := h2
  refine ⟨R :: (π1 ++ π2), IsDerivation.res (deriv_append hd1 hd2)
    (List.mem_append_left _ hm1) (List.mem_append_right _ hm2) hres, List.mem_cons_self .., ?_⟩
  intro C hC
  rcases List.mem_cons.mp hC with rfl | hC
  · exact hR
  · rcases List.mem_append.mp hC with h | h
    · exact hw1 _ h
    · exact hw2 _ h

lemma sd_mono {A A' : Clause (Raw w)} (h : SD w F W A) (hs : A ⊆ A') : SD w F W A' := by
  obtain ⟨B, hB, hd⟩ := h
  exact ⟨B, hB.trans hs, hd⟩

lemma sd_res {A : Clause (Raw w)} (z : Raw w) (hA : A.card ≤ W)
    (h1 : SD w F W (insert (z, true) A)) (h2 : SD w F W (insert (z, false) A)) :
    SD w F W A := by
  obtain ⟨B1, hB1, hd1⟩ := h1
  obtain ⟨B2, hB2, hd2⟩ := h2
  by_cases ht : (z, true) ∈ B1
  · by_cases hf : (z, false) ∈ B2
    · have hsub : B1.erase (z, true) ∪ B2.erase (z, false) ⊆ A := by
        intro l hl
        rcases Finset.mem_union.mp hl with hl | hl
        · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
          rcases Finset.mem_insert.mp (hB1 hl) with h | h
          · exact absurd h hne
          · exact h
        · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
          rcases Finset.mem_insert.mp (hB2 hl) with h | h
          · exact absurd h hne
          · exact h
      exact ⟨_, hsub, rd_res hd1 hd2 ⟨z, ht, hf, rfl⟩ (le_trans (Finset.card_le_card hsub) hA)⟩
    · refine ⟨B2, ?_, hd2⟩
      intro l hl
      rcases Finset.mem_insert.mp (hB2 hl) with h | h
      · exact absurd (h ▸ hl) hf
      · exact h
  · refine ⟨B1, ?_, hd1⟩
    intro l hl
    rcases Finset.mem_insert.mp (hB1 hl) with h | h
    · exact absurd (h ▸ hl) ht
    · exact h

lemma rc_card (X : Finset (Raw w)) (y : Raw w → Bool) : (rc X y).card = X.card := by
  unfold rc
  exact Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.fst h)

lemma mem_rc {X : Finset (Raw w)} {y : Raw w → Bool} {l : Literal (Raw w)} :
    l ∈ rc X y ↔ l.1 ∈ X ∧ l.2 = !y l.1 := by
  obtain ⟨z, b⟩ := l
  simp only [rc, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, rfl, rfl⟩
    exact ⟨ha, rfl⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨z, ha, rfl, rfl⟩

lemma rc_insert (z : Raw w) (X : Finset (Raw w)) (y : Raw w → Bool) :
    rc (insert z X) y = insert (z, !y z) (rc X y) := by
  unfold rc
  rw [Finset.image_insert]

lemma rc_congr {X : Finset (Raw w)} {y y' : Raw w → Bool} (h : ∀ z ∈ X, y z = y' z) :
    rc X y = rc X y' := by
  unfold rc
  apply Finset.image_congr
  intro z hz
  simp [h z hz]

lemma rc_mono {X X' : Finset (Raw w)} (y : Raw w → Bool) (h : X ⊆ X') : rc X y ⊆ rc X' y :=
  Finset.image_subset_image h

lemma rc_vars (X : Finset (Raw w)) (y : Raw w → Bool) : (rc X y).image Prod.fst = X := by
  ext z
  simp only [rc, Finset.mem_image]
  constructor
  · rintro ⟨l, ⟨a, ha, rfl⟩, rfl⟩
    exact ha
  · intro hz
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩

lemma mem_blk {S : Finset (Fin n)} {z : Raw w} : z ∈ blk w S ↔ z.1 ∈ S := by
  simp [blk]

lemma blk_card (S : Finset (Fin n)) : (blk w S).card = S.sum w := by
  have : blk w S = S.sigma (fun v => (Finset.univ : Finset (Fin (w v)))) := by
    ext ⟨v, j⟩
    simp [blk]
  rw [this, Finset.card_sigma]
  simp

lemma par_congr {y y' : Raw w → Bool} {v : Fin n} (h : ∀ j, y ⟨v, j⟩ = y' ⟨v, j⟩) :
    par y v = par y' v := by
  simp only [par, h]

lemma par_update_ne {y : Raw w → Bool} {z : Raw w} {v : Fin n} (b : Bool) (hz : z.1 ≠ v) :
    par (Function.update y z b) v = par y v := by
  apply par_congr
  intro j
  apply Function.update_of_ne
  intro h
  apply hz
  subst h
  rfl

lemma par_update_self (y : Raw w → Bool) (z : Raw w) :
    par (Function.update y z true) z.1 = !par (Function.update y z false) z.1 := by
  obtain ⟨v, j0⟩ := z
  unfold par
  have h1 : ((Finset.univ : Finset (Fin (w v))).filter
      fun j => Function.update y ⟨v, j0⟩ true ⟨v, j⟩ = true) =
      insert j0 ((Finset.univ : Finset (Fin (w v))).filter
      fun j => Function.update y ⟨v, j0⟩ false ⟨v, j⟩ = true) := by
    ext j
    by_cases hj : j = j0
    · subst hj
      simp
    · have hne : (⟨v, j⟩ : Raw w) ≠ ⟨v, j0⟩ := by
        intro h
        apply hj
        simpa using h
      simp [hj]
  have h0 : j0 ∉ ((Finset.univ : Finset (Fin (w v))).filter
      fun j => Function.update y ⟨v, j0⟩ false ⟨v, j⟩ = true) := by
    simp
  simp only
  rw [h1, Finset.card_insert_of_notMem h0]
  simp only [Nat.odd_add_one, decide_not]

def Lift (w : Fin n → ℕ) (F : Set (Clause (Fin n))) (W : ℕ) (D : Clause (Fin n)) : Prop :=
  ∀ x : Raw w → Bool, (∀ l ∈ D, par x l.1 ≠ l.2) → SD w F W (rc (blk w (bv D)) x)

lemma lift_leaf {D : Clause (Fin n)} (hF : D ∈ F) (hW : (bv D).sum w ≤ W) : Lift w F W D := by
  intro x hx
  refine ⟨_, subset_refl _, [rc (blk w (bv D)) x],
    IsDerivation.ax IsDerivation.nil ⟨D, hF, x, hx, rfl⟩, List.mem_singleton_self _, ?_⟩
  intro C hC
  rw [List.mem_singleton.mp hC, rc_card, blk_card]
  exact hW

lemma sd_elim (G : Finset (Raw w)) (Ok : (Raw w → Bool) → Prop) :
    ∀ X : Finset (Raw w), Disjoint G X →
      (∀ y z b, z ∈ X → Ok y → Ok (Function.update y z b)) →
      G.card + X.card ≤ W + 1 → (∀ y, Ok y → SD w F W (rc (G ∪ X) y)) →
      ∀ y, Ok y → SD w F W (rc G y) := by
  intro X
  induction X using Finset.induction_on with
  | empty =>
    intro _ _ _ h y hy
    simpa using h y hy
  | insert z X hz ih =>
    intro hdis hok hcard h
    have hcard' : G.card + X.card + 1 ≤ W + 1 := by
      rw [Finset.card_insert_of_notMem hz] at hcard
      omega
    apply ih (Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hdis)
      (fun y z' b hz' hy => hok y z' b (Finset.mem_insert_of_mem hz') hy) (by omega)
    intro y hy
    have hzG : z ∉ G := fun h => Finset.disjoint_left.mp hdis h (Finset.mem_insert_self _ _)
    have hzGX : z ∉ G ∪ X := by simp [hzG, hz]
    have hcongr : ∀ b, rc (G ∪ X) (Function.update y z b) = rc (G ∪ X) y := fun b =>
      rc_congr (fun z' hz' => Function.update_of_ne (fun h => hzGX (by rw [← h]; exact hz')) _ _)
    have hins : ∀ b, rc (G ∪ insert z X) (Function.update y z b) =
        insert (z, !b) (rc (G ∪ X) y) := by
      intro b
      rw [Finset.union_insert, rc_insert, hcongr]
      simp
    apply sd_res z
    · rw [rc_card]
      have := Finset.card_union_le G X
      omega
    · have := h _ (hok y z false (Finset.mem_insert_self _ _) hy)
      rw [hins] at this
      simpa using this
    · have := h _ (hok y z true (Finset.mem_insert_self _ _) hy)
      rw [hins] at this
      simpa using this

def Full (D : Finset (Raw w)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun v => ∀ j : Fin (w v), (⟨v, j⟩ : Raw w) ∈ D)

lemma full_mono {D D' : Finset (Raw w)} (h : D' ⊆ D) : Full D' ⊆ Full D := by
  intro v hv
  simp only [Full, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  exact fun j => h (hv j)

lemma full_weight (D : Finset (Raw w)) : (Full D).sum w ≤ D.card := by
  rw [← blk_card]
  apply Finset.card_le_card
  intro z hz
  rw [mem_blk] at hz
  simp only [Full, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  exact hz z.2

abbrev Row (n : ℕ) := Finset (Fin n) × Bool

def rowPar {α : Type} (S : Finset α) (x : α → Bool) : Bool :=
  decide (Odd ((S.filter (fun i => x i = true)).card))

def EqFormula {n : ℕ} (E : Set (Row n)) : Set (Clause (Fin n)) :=
  {C | ∃ z ∈ E, ∃ x : Fin n → Bool, rowPar z.1 x ≠ z.2 ∧
    C = z.1.image (fun i => (i, !(x i)))}

def xorSupport (S T : Finset (Fin n)) := (S \ T) ∪ (T \ S)

def Closed (w : Fin n → ℕ) (E : Set (Row n)) (W : ℕ) (R : Set (Row n)) : Prop :=
  (∀ z ∈ E, z.1.sum w ≤ W → z ∈ R) ∧
  (∀ p ∈ R, ∀ q ∈ R, (p.1 ∩ q.1).Nonempty → (p.1 ∪ q.1).sum w ≤ W + 1 →
    (xorSupport p.1 q.1, p.2 ^^ q.2) ∈ R)

lemma rowPar_congr {α : Type} {S : Finset α} {x y : α → Bool}
    (h : ∀ i ∈ S, x i = y i) : rowPar S x = rowPar S y := by
  unfold rowPar
  have eq : S.filter (fun i => x i = true) = S.filter (fun i => y i = true) :=
    Finset.filter_congr fun i hi => by rw [h i hi]
  rw [eq]

lemma rowPar_union {α : Type} [DecidableEq α] (S T : Finset α) (x : α → Bool)
    (h : Disjoint S T) : rowPar (S ∪ T) x = (rowPar S x ^^ rowPar T x) := by
  unfold rowPar
  rw [Finset.filter_union, Finset.card_union_of_disjoint
    (h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  have hadd (a b : ℕ) : decide (Odd (a+b)) = (decide (Odd a) ^^ decide (Odd b)) := by
    by_cases ha : Odd a <;> by_cases hb : Odd b <;>
      simp [Nat.odd_add, ← Nat.not_odd_iff_even, ha, hb]
  exact hadd _ _

lemma rowPar_add (S T : Finset (Fin n)) (x : Fin n → Bool) :
    rowPar (xorSupport S T) x = (rowPar S x ^^ rowPar T x) := by
  have hdis : Disjoint (S \ T) (T \ S) :=
    Finset.disjoint_left.mpr fun _ ha hb => (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  have hs := rowPar_union (S \ T) (S ∩ T) x (Finset.disjoint_sdiff_inter _ _)
  have ht := rowPar_union (T \ S) (T ∩ S) x (Finset.disjoint_sdiff_inter _ _)
  rw [Finset.sdiff_union_inter] at hs ht
  rw [xorSupport, rowPar_union _ _ x hdis, hs, ht, Finset.inter_comm T S]
  cases rowPar (S \ T) x <;> cases rowPar (T \ S) x <;> cases rowPar (S ∩ T) x <;> rfl

lemma rowPar_flip (S : Finset (Fin n)) {x y : Fin n → Bool} {i : Fin n}
    (hi : i ∈ S) (h : ∀ j, j ≠ i → x j = y j) (hne : x i ≠ y i) :
    rowPar S x = !(rowPar S y) := by
  have e : S.erase i ∪ {i} = S := by
    ext j
    by_cases hj : j = i <;> simp [hj,hi]
  have d : Disjoint (S.erase i) ({i} : Finset (Fin n)) := by simp
  have ux := rowPar_union (S.erase i) {i} x d
  have uy := rowPar_union (S.erase i) {i} y d
  rw [e] at ux uy
  have he := rowPar_congr (S := S.erase i) (fun j hj => h j (Finset.mem_erase.mp hj).1)
  have sing (q : Fin n → Bool) : rowPar {i} q = q i := by
    cases he : q i <;> simp [rowPar, Finset.filter_singleton, he]
  rw [ux, uy, he, sing, sing]
  cases rowPar (S.erase i) y <;> cases hx : x i <;> cases hy : y i <;> simp_all

lemma par_updates_ne (x : Raw w → Bool) (z : Raw w) :
    par (Function.update x z false) z.1 ≠ par (Function.update x z true) z.1 := by
  rw [par_update_self]
  cases par (Function.update x z false) z.1 <;> decide

end PEqualNP.Outside.L_pcx_311_aux

namespace PEqualNP.Outside.L_pcx_311_aux

open PEqualNP.ProofComplexity

variable {n : ℕ} {w : Fin n → ℕ} {E : Set (Row n)} {W : ℕ}

def RowSD (w : Fin n → ℕ) (E : Set (Row n)) (W : ℕ) (q : Row n) : Prop :=
  ∀ y : Raw w → Bool, rowPar q.1 (par y) ≠ q.2 → SD w (EqFormula E) W (rc (blk w q.1) y)

lemma rowSD_ax {q : Row n} (hq : q ∈ E) (hwt : q.1.sum w ≤ W) :
    RowSD w E W q := by
  intro y hy
  let C : Clause (Fin n) := q.1.image (fun i => (i, !par y i))
  have cvars : bv C = q.1 := by simp [C, bv, Finset.image_image, Function.comp_def]
  have cax : C ∈ EqFormula E := ⟨q,hq,par y,hy,rfl⟩
  have sz : (bv C).sum w ≤ W := by rwa [cvars]
  have fail : ∀ l ∈ C, par y l.1 ≠ l.2 := by
    intro l hl
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hl
    simp
  have out := lift_leaf (w := w) cax sz y fail
  simpa only [cvars] using out

lemma rowSD_xor {p q : Row n} (hp : RowSD w E W p) (hq : RowSD w E W q)
    (hwt : (p.1 ∪ q.1).sum w ≤ W + 1) :
    RowSD w E W (xorSupport p.1 q.1, p.2 ^^ q.2) := by
  let G := blk w (xorSupport p.1 q.1)
  let X := blk w (p.1 ∩ q.1)
  have disj : Disjoint G X := by
    rw [Finset.disjoint_left]
    intro z hz hzx
    have hG : z.1 ∈ xorSupport p.1 q.1 := mem_blk.mp hz
    have hX : z.1 ∈ p.1 ∩ q.1 := mem_blk.mp hzx
    simp only [xorSupport, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at hG hX
    tauto
  have un : G ∪ X = blk w (p.1 ∪ q.1) := by
    ext z
    simp only [G, X, xorSupport, Finset.mem_union, mem_blk, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  let Ok := fun y : Raw w → Bool => rowPar (xorSupport p.1 q.1) (par y) ≠ (p.2 ^^ q.2)
  have upto : G.card + X.card ≤ W + 1 := by
    rw [← Finset.card_union_of_disjoint disj, un, blk_card]
    exact hwt
  refine sd_elim (F := EqFormula E) G Ok X disj ?_ upto ?_
  · intro y z b hz hy
    dsimp only [Ok] at hy ⊢
    have hX : z.1 ∈ p.1 ∩ q.1 := mem_blk.mp hz
    have heq : rowPar (xorSupport p.1 q.1) (par (Function.update y z b)) =
        rowPar (xorSupport p.1 q.1) (par y) := by
      apply rowPar_congr
      intro i hi
      apply par_update_ne
      intro h
      subst i
      simp only [xorSupport, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at hi hX
      tauto
    exact heq ▸ hy
  · intro y hy
    have hx : rowPar p.1 (par y) ≠ p.2 ∨ rowPar q.1 (par y) ≠ q.2 := by
      by_contra! no
      apply hy
      rw [rowPar_add, no.1, no.2]
    rw [un]
    rcases hx with fail|fail
    · apply sd_mono (hp y fail)
      exact rc_mono y (fun _ h => mem_blk.mpr (Finset.mem_union_left _ (mem_blk.mp h)))
    · apply sd_mono (hq y fail)
      exact rc_mono y (fun _ h => mem_blk.mpr (Finset.mem_union_right _ (mem_blk.mp h)))

lemma closure_to_resolution
    (h : ∀ R : Set (Row n), Closed w E W R → ((∅ : Finset (Fin n)), true) ∈ R) :
    ∃ π : List (Clause (Raw w)), IsRefutation (lifted w (EqFormula E)) π ∧
      ∀ C ∈ π, C.card ≤ W := by
  let R : Set (Row n) := {q | RowSD w E W q}
  have hc : Closed w E W R :=
    ⟨fun z hz hwt => rowSD_ax hz hwt, fun p hp q hq _ hwt => rowSD_xor hp hq hwt⟩
  have hempty : RowSD w E W (∅,true) := h R hc
  have hsd := hempty (fun _ => false) (by simp [rowPar])
  have empty : rc (blk w (∅ : Finset (Fin n))) (fun _ => false) = ∅ := by simp [rc, blk]
  rw [empty] at hsd
  obtain ⟨C,sub,π,hd,hm,hW⟩ := hsd
  have e : C = ∅ := Finset.subset_empty.mp sub
  exact ⟨π,⟨hd,e ▸ hm⟩,hW⟩

end PEqualNP.Outside.L_pcx_311_aux

namespace PEqualNP.Outside.L_pcx_311_aux

open PEqualNP.ProofComplexity

variable {n : ℕ} {w : Fin n → ℕ} {E R : Set (Row n)} {W : ℕ}

def Supp (C : Clause (Raw w)) : Finset (Raw w) := C.image Prod.fst

def Fals (x : Raw w → Bool) (C : Clause (Raw w)) : Prop :=
  ∀ l ∈ C, x l.1 ≠ l.2

def Bad (R : Set (Row n)) (D : Finset (Raw w)) (x : Raw w → Bool) : Prop :=
  ∃ p ∈ R, p.1 ⊆ Full D ∧ rowPar p.1 (par x) ≠ p.2

lemma bad_mono {D D' : Finset (Raw w)} {x : Raw w → Bool}
    (h : Bad R D x) (hs : D ⊆ D') : Bad R D' x := by
  obtain ⟨p, hp, hD, hf⟩ := h
  exact ⟨p, hp, hD.trans (full_mono hs), hf⟩

lemma supp_erase {C T : Clause (Raw w)} {v : Raw w} {b : Bool}
    (h : C.erase (v,b) ⊆ T) : Supp C ⊆ insert v (Supp T) := by
  intro z hz
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
  by_cases he : l = (v,b)
  · rw [he]
    exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (h (Finset.mem_erase.mpr ⟨he,hl⟩)))

lemma fals_erase {C T : Clause (Raw w)} {x : Raw w → Bool} {v : Raw w} {b : Bool}
    (h : C.erase (v,b) ⊆ T) (hx : Fals x T) (hv : x v ≠ b) : Fals x C := by
  intro l hl
  by_cases e : l = (v,b)
  · subst l
    exact hv
  · exact hx l (h (Finset.mem_erase.mpr ⟨e,hl⟩))

lemma fals_update {T : Clause (Raw w)} {x : Raw w → Bool} {v : Raw w}
    (h : Fals x T) (hv : v ∉ Supp T) (b : Bool) :
    Fals (Function.update x v b) T := by
  intro l hl
  have e : l.1 ≠ v := fun a => hv (Finset.mem_image.mpr ⟨l,hl,a⟩)
  rw [Function.update_of_ne e]
  exact h l hl

lemma full_of_insert {D : Finset (Raw w)} {v : Raw w} {i : Fin n}
    (h : i ∈ Full (insert v D)) (hne : i ≠ v.1) : i ∈ Full D := by
  simp only [Full, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  intro j
  rcases Finset.mem_insert.mp (h j) with h' | h'
  · exact absurd (congrArg Sigma.fst h') hne
  · exact h'

lemma rowPar_update_away (P : Finset (Fin n)) (x : Raw w → Bool) (v : Raw w) (b : Bool)
    (h : v.1 ∉ P) : rowPar P (par (Function.update x v b)) = rowPar P (par x) := by
  apply rowPar_congr
  intro i hi
  exact par_update_ne b (fun e => h (e ▸ hi))

lemma xor_ne_of_ne_of_eq {a b c d : Bool} (ha : a ≠ c) (hb : b = d) :
    (a ^^ b) ≠ (c ^^ d) := by
  subst d
  cases a <;> cases b <;> cases c <;> simp_all

lemma bad_resolve {D : Finset (Raw w)} {x : Raw w → Bool} {v : Raw w}
    (hclose : Closed w E W R) (width : D.card ≤ W)
    (h0 : Bad R (insert v D) (Function.update x v false))
    (h1 : Bad R (insert v D) (Function.update x v true)) :
    Bad R D x := by
  obtain ⟨p,hp,ps,hpf⟩ := h0
  obtain ⟨q,hq,qs,hqf⟩ := h1
  by_cases pbit : v.1 ∈ p.1
  · by_cases qbit : v.1 ∈ q.1
    · have cost : (p.1 ∪ q.1).sum w ≤ W + 1 := by
        calc
          _ ≤ (Full (insert v D)).sum w :=
            Finset.sum_le_sum_of_subset (Finset.union_subset ps qs)
          _ ≤ (insert v D).card := full_weight _
          _ ≤ D.card + 1 := Finset.card_insert_le _ _
          _ ≤ W + 1 := by omega
      have hmem := hclose.2 p hp q hq ⟨v.1, Finset.mem_inter.mpr ⟨pbit,qbit⟩⟩ cost
      have absent : v.1 ∉ xorSupport p.1 q.1 := by simp [xorSupport,pbit,qbit]
      have hsupp : xorSupport p.1 q.1 ⊆ Full D := by
        intro i hi
        apply full_of_insert (v := v)
        · rcases Finset.mem_union.mp hi with h | h
          · exact ps (Finset.mem_sdiff.mp h).1
          · exact qs (Finset.mem_sdiff.mp h).1
        · intro e
          exact absent (e ▸ hi)
      have same : ∀ i, i ≠ v.1 →
          par (Function.update x v false) i = par (Function.update x v true) i := by
        intro i hi
        rw [par_update_ne false (Ne.symm hi), par_update_ne true (Ne.symm hi)]
      have flip := rowPar_flip q.1 qbit same (par_updates_ne x v)
      have goodq : rowPar q.1 (par (Function.update x v false)) = q.2 := by
        rw [flip]
        exact (show ∀ a b : Bool, a ≠ b → (!a) = b by decide) _ _ hqf
      refine ⟨_,hmem,hsupp,?_⟩
      change rowPar (xorSupport p.1 q.1) (par x) ≠ (p.2 ^^ q.2)
      rw [← rowPar_update_away _ x v false absent, rowPar_add]
      exact xor_ne_of_ne_of_eq hpf goodq
    · exact ⟨q,hq,fun i hi => full_of_insert (qs hi) (fun e => qbit (e ▸ hi)),
        rowPar_update_away q.1 x v true qbit ▸ hqf⟩
  · exact ⟨p,hp,fun i hi => full_of_insert (ps hi) (fun e => pbit (e ▸ hi)),
      rowPar_update_away p.1 x v false pbit ▸ hpf⟩

lemma lit_ne_compl_imp_eq {a b : Bool} (h : a ≠ !b) : a = b := by
  cases a <;> cases b <;> simp_all

lemma bad_ax {C : Clause (Raw w)} (hclose : Closed w E W R)
    (hax : C ∈ lifted w (EqFormula E)) (hwidth : C.card ≤ W)
    (x : Raw w → Bool) (hx : Fals x C) :
    Bad R (Supp C) x := by
  obtain ⟨A,hA,y,hy,rfl⟩ := hax
  obtain ⟨q,hq,a,ha,rfl⟩ := hA
  have hbv : (q.1.image (fun i => (i,!a i))).image Prod.fst = q.1 := by
    simp [Finset.image_image, Function.comp_def]
  rw [hbv] at hx hwidth ⊢
  have weight : q.1.sum w ≤ W := by
    simpa only [rc_card, blk_card] using hwidth
  have hs : Supp (rc (blk w q.1) y) = blk w q.1 := rc_vars _ _
  rw [hs]
  refine ⟨q,hclose.1 q hq weight,?_,?_⟩
  · intro i hi
    simp only [Full, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j
    exact mem_blk.mpr hi
  · have agree : rowPar q.1 (par x) = rowPar q.1 a := by
      apply rowPar_congr
      intro i hi
      have hyi : par y i = a i := by
        apply lit_ne_compl_imp_eq
        exact hy (i,!a i) (Finset.mem_image_of_mem _ hi)
      rw [← hyi]
      apply par_congr
      intro j
      let z : Raw w := ⟨i,j⟩
      exact lit_ne_compl_imp_eq
        (hx (z,!y z) (Finset.mem_image_of_mem _ (mem_blk.mpr hi)))
    exact agree ▸ ha

lemma resolution_bad (hc : Closed w E W R) {π : List (Clause (Raw w))}
    (h : IsDerivation (lifted w (EqFormula E)) π) :
    (∀ C ∈ π, C.card ≤ W) → ∀ C ∈ π, ∀ x, Fals x C → Bad R (Supp C) x := by
  induction h with
  | nil => simp
  | @ax π C hπ hC ih =>
    intro hw T hT x hx
    rcases List.mem_cons.mp hT with hEq | ht
    · subst T
      exact bad_ax hc hC (hw C (List.mem_cons_self ..)) x hx
    · exact ih (fun A ha => hw A (List.mem_cons_of_mem _ ha)) T ht x hx
  | @res π C D T hπ hC hD hres ih =>
    intro hw A ha x hx
    have ih' := ih (fun B hb => hw B (List.mem_cons_of_mem _ hb))
    rcases List.mem_cons.mp ha with hEq | ht
    · subst A
      obtain ⟨v,hvC,hvD,heq⟩ := hres
      have cs : C.erase (v,true) ⊆ T := heq ▸ Finset.subset_union_left
      have ds : D.erase (v,false) ⊆ T := heq ▸ Finset.subset_union_right
      have ch := supp_erase cs
      have dh := supp_erase ds
      by_cases hv : v ∈ Supp T
      · rw [Finset.insert_eq_of_mem hv] at ch dh
        cases e : x v
        · exact bad_mono (ih' C hC x (fals_erase cs hx (by simp [e]))) ch
        · exact bad_mono (ih' D hD x (fals_erase ds hx (by simp [e]))) dh
      · have hwidth : (Supp T).card ≤ W := Finset.card_image_le.trans (hw T (List.mem_cons_self ..))
        have f0 := fals_erase cs (fals_update hx hv false) (by simp : Function.update x v false v ≠ true)
        have f1 := fals_erase ds (fals_update hx hv true) (by simp : Function.update x v true v ≠ false)
        exact bad_resolve hc hwidth (bad_mono (ih' C hC _ f0) ch) (bad_mono (ih' D hD _ f1) dh)
    · exact ih' A ht x hx

lemma resolution_to_closure (hw : ∀ i, 0 < w i)
    (h : ∃ π : List (Clause (Raw w)), IsRefutation (lifted w (EqFormula E)) π ∧
      ∀ C ∈ π, C.card ≤ W) :
    ∀ R : Set (Row n), Closed w E W R → ((∅ : Finset (Fin n)), true) ∈ R := by
  rintro R hc
  obtain ⟨π,⟨hd,he⟩,hwid⟩ := h
  obtain ⟨⟨S,b⟩,hb,hS,hfail⟩ := resolution_bad hc hd hwid ∅ he (fun _ => false) (by simp [Fals])
  have empty : Full (Supp (∅ : Clause (Raw w))) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    simp only [Full, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simpa [Supp] using hi ⟨0,hw i⟩
  change S ⊆ Full (Supp (∅ : Clause (Raw w))) at hS
  rw [empty] at hS
  have hS0 := Finset.subset_empty.mp hS
  subst S
  have hb1 : b = true := by
    cases b <;> simp_all [rowPar]
  subst b
  exact hb

end PEqualNP.Outside.L_pcx_311_aux

open PEqualNP.Outside.L_pcx_311_aux PEqualNP.ProofComplexity in
theorem PEqualNP.Outside.L_pcx_311 : (∀ (n : ℕ) (w : Fin n → ℕ), (∀ v, 0 < w v) →
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
  let Row := Finset (Fin n) × Bool
  ∀ E : Set Row,
    let F : Set Base := {C | ∃ z ∈ E, ∃ x : Fin n → Bool,
      decide (Odd ((z.1.filter (fun i => x i = true)).card)) ≠ z.2 ∧
      C = z.1.image (fun i => (i, !(x i)))}
    ∀ W : ℕ, Iff (can w F W)
      (∀ R : Set Row,
        (∀ z ∈ E, z.1.sum w ≤ W → z ∈ R) →
        (∀ p ∈ R, ∀ q ∈ R, (p.1 ∩ q.1).Nonempty → (p.1 ∪ q.1).sum w ≤ W+1 →
          ((p.1 \ q.1) ∪ (q.1 \ p.1), p.2 ^^ q.2) ∈ R) →
        ((∅ : Finset (Fin n)), true) ∈ R)) := by
  intro n w hw Base can RawRow E F W
  change (∃ π : List (Clause (Raw w)), IsRefutation (lifted w (EqFormula E)) π ∧
      ∀ C ∈ π, C.card ≤ W) ↔ _
  constructor
  · intro h R hAx hXor
    exact resolution_to_closure hw h R ⟨hAx, hXor⟩
  · intro h
    exact closure_to_resolution (fun R hc => h R hc.1 hc.2)
