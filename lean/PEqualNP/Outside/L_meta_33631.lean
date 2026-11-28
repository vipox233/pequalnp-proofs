import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25883

namespace PEqualNP.Outside.L_meta_33631

open Finset PEqualNP.Outside.L_meta_25883_aux

def active (b : ℕ → Bool) (j : ℕ) := b (j+1) || b (j+2)
def pivot (b : ℕ → Bool) (j : ℕ) := if b (j+1) then j+2 else j+1
def rhs (b t : ℕ → Bool) (j : ℕ) := if b (j+1) then xor (b j) (t j) else !(xor (b j) (t j))
def obs (b y : ℕ → Bool) (p : ℕ) := if b p then xor (y (p-1)) (y p) else y p

def goodRow (b t y : ℕ → Bool) (j : ℕ) :=
  if active b j then obs b y (pivot b j) = rhs b t j else b j = t j

def badPair (R : Finset ℕ) (b t : ℕ → Bool) (j : ℕ) :=
  j+1 ∈ R ∧ b (j+1) = true ∧ b (j+2) = false ∧ b (j+3) = true ∧ xor (b j) (t j) ≠ t (j+1)

lemma pair_wrong {R : Finset ℕ} {b t y : ℕ → Bool} {j : ℕ} (hj : j ∈ R)
    (hp : badPair R b t j) (hg : ∀ i ∈ R, goodRow b t y i) : False := by
  obtain ⟨hj',h1,h2,h3,hh⟩ := hp
  have g1 := hg j hj
  have g2 := hg (j+1) hj'
  simp [goodRow,active,pivot,rhs,h1,h2,h3,Nat.add_assoc] at g1 g2
  exact hh (g1.symm.trans g2)

lemma rhs_order {R : Finset ℕ} {b t : ℕ → Bool}
    (hn : ∀ j ∈ R, ¬badPair R b t j) {i j : ℕ}
    (hi : i ∈ R) (hj : j ∈ R) (hi' : active b i = true) (hj' : active b j = true)
    (hlt : i < j) (he : pivot b i = pivot b j) : rhs b t i = rhs b t j := by
  have key : j=i+1 ∧ b (i+1)=true ∧ b (j+1)=false := by
    cases h1 : b (i+1) <;> cases h2 : b (j+1) <;> simp [pivot,h1,h2] at he ⊢ <;> omega
  obtain ⟨rfl,h1,h2⟩ := key
  have h2' : b (i+2) = false := h2
  have h3 : b (i+3) = true := by simpa [active,h2,Nat.add_assoc,h2'] using hj'
  have heq : xor (b i) (t i) = t (i+1) := by
    by_contra h
    exact hn i hi ⟨hj,h1,h2',h3,h⟩
  simp [rhs,h1,h2',Nat.add_assoc,heq]

lemma normalize {R : Finset ℕ} (b t : ℕ → Bool)
    (hn : ∀ j ∈ R, ¬badPair R b t j)
    (hw : ∀ j ∈ R, b (j+1)=false → b (j+2)=false → b j=t j) :
    ∃ target : ℕ → Bool, ∀ y : ℕ → Bool, (∀ j ∈ R, goodRow b t y j) ↔
      ∀ p ∈ (R.filter (fun j => active b j)).image (pivot b), obs b y p = target p := by
  classical
  let S := R.filter (fun j => active b j)
  let P := S.image (pivot b)
  have rep (p : ℕ) (h : p ∈ P) : ∃ j ∈ S, pivot b j = p := mem_image.mp h
  let target (p : ℕ) := if h : p ∈ P then rhs b t (rep p h).choose else false
  have lab {j} (hj : j ∈ S) : target (pivot b j) = rhs b t j := by
    have hp : pivot b j ∈ P := mem_image_of_mem _ hj
    simp only [target, dite_eq_left hp]
    obtain ⟨hi,he⟩ := (rep _ hp).choose_spec
    rcases lt_trichotomy (rep _ hp).choose j with h|h|h
    · exact rhs_order hn (mem_filter.mp hi).1 (mem_filter.mp hj).1 (mem_filter.mp hi).2 (mem_filter.mp hj).2 h he
    · rw [h]
    · exact (rhs_order hn (mem_filter.mp hj).1 (mem_filter.mp hi).1 (mem_filter.mp hj).2 (mem_filter.mp hi).2 h he.symm).symm
  refine ⟨target, fun y => ⟨?_,?_⟩⟩
  · intro h p hp
    obtain ⟨j,hj,rfl⟩ := rep _ hp
    obtain ⟨hR,ha⟩ := mem_filter.mp hj
    simpa [goodRow,ha,lab hj] using h j hR
  · intro h j hj
    by_cases ha : active b j = true
    · have hS : j ∈ S := mem_filter.mpr ⟨hj,ha⟩
      simpa [goodRow,ha,lab hS] using h (pivot b j) (mem_image_of_mem _ hS)
    · have hboth : b (j+1) = false ∧ b (j+2) = false := by simpa [active] using ha
      simpa [goodRow,ha] using hw j hj hboth.1 hboth.2

lemma pivot_count (R : Finset ℕ) (b : ℕ → Bool) :
    ((R.filter (fun j => active b j)).image (pivot b)).card =
      (R.filter (fun j => b (j+1)=true ∧ b (j+2)=true)).card +
      ((R.filter (fun j => b (j+1) ≠ b (j+2))).image (pivot b)).card := by
  classical
  let E := R.filter (fun j => b (j+1)=true ∧ b (j+2)=true)
  let S := R.filter (fun j => b (j+1) ≠ b (j+2))
  have hu : R.filter (fun j => active b j) = E ∪ S := by
    ext j
    cases h1 : b (j+1) <;> cases h2 : b (j+2) <;> simp [E,S,active,h1,h2]
  have hd : Disjoint (E.image (pivot b)) (S.image (pivot b)) := by
    apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨i,hi,he⟩ := mem_image.mp hp
    obtain ⟨j,hj,hf⟩ := mem_image.mp hq
    obtain ⟨_,h1,h2⟩ := mem_filter.mp hi
    have ht : b p = true := by simpa [← he,pivot,h1] using h2
    have hne := (mem_filter.mp hj).2
    rw [← hf] at ht
    cases h3 : b (j+1) <;> cases h4 : b (j+2) <;> simp [pivot,h3,h4] at hne ht
  have hcard : (E.image (pivot b)).card = E.card := by
    apply card_image_of_injOn
    intro i hi j hj he
    simpa [pivot,(mem_filter.mp hi).2.1,(mem_filter.mp hj).2.1] using he
  rw [hu,image_union,card_union_of_disjoint hd,hcard]

lemma count_sites (k : ℕ) (g : ℕ → ℕ → Bool) (q : ℕ → ℕ) (v : ℕ → Bool) (P : Finset ℕ)
    (hq : ∀ p ∈ P, q p < k) (hc : P.card ≤ k)
    (hs : ∀ p ∈ P, ∀ x < 2^k, g (x ^^^ 2^(q p)) p = !(g x p))
    (hl : ∀ p ∈ P, ∀ i < p, ∀ x < 2^k, g (x ^^^ 2^(q p)) i = g x i) :
    ((range (2^k)).filter (fun x => ∀ p ∈ P, g x p = v p)).card = 2^(k-P.card) := by
  induction P using induction_on_max with
  | empty => simp
  | insert p S hm ih =>
    have hp : p ∉ S := fun h => (Nat.lt_irrefl _ (hm _ h))
    rw [card_insert_of_notMem hp] at hc ⊢
    have hsub {i} (h : i ∈ S) : i ∈ insert p S := mem_insert_of_mem h
    let keys := (range (2^k)).filter (fun x => ∀ i ∈ S, g x i = v i)
    have hkeys : keys.card = 2^(k-S.card) := ih (fun i h => hq i (hsub h)) (by omega)
      (fun i h => hs i (hsub h)) (fun i h => hl i (hsub h))
    have he : (range (2^k)).filter (fun x => ∀ i ∈ insert p S, g x i = v i) =
        keys.filter (fun x => g x p = v p) := by ext x; simp [keys,and_assoc,and_left_comm,and_comm]
    rw [he]
    have hh := halving keys (fun x => x ^^^ 2^(q p)) (by
      intro x hx
      obtain ⟨hx0,hx1⟩ := mem_filter.mp hx
      refine mem_filter.mpr ⟨mem_range.mpr (flip_lt (mem_range.mp hx0) (hq p (mem_insert_self ..))), ?_⟩
      intro i hi
      rw [hl p (mem_insert_self ..) i (hm _ hi) x (mem_range.mp hx0)]
      exact hx1 i hi) (fun x _ => flip_flip x _) (fun x => g x p)
      (fun x hx => hs p (mem_insert_self ..) x (mem_range.mp (mem_filter.mp hx).1)) (v p)
    rw [hkeys] at hh
    have he2 : 2^(k-S.card) = 2 * 2^(k-(S.card+1)) := by rw [← pow_succ']; congr 1; omega
    omega

def diffBit (b y : ℕ → Bool) (j : ℕ) :=
  xor (b j) (xor (!(y (j+1)) && y (j+2))
    (!(xor (y (j+1)) (b (j+1))) && xor (y (j+2)) (b (j+2))))

lemma truth : ∀ c l r x y t : Bool,
    (xor c (xor (!x && y) (!(xor x l) && xor y r)) = t) ↔
    (if l then (if r then xor x y else y) = xor c t else if r then x = !(xor c t) else c=t) := by decide

lemma row_equiv (b t y : ℕ → Bool) (j : ℕ) : diffBit b y j = t j ↔ goodRow b t y j := by
  unfold diffBit
  rw [truth]
  cases h1 : b (j+1) <;> cases h2 : b (j+2) <;> simp [goodRow,active,pivot,obs,rhs,h1,h2]

lemma xorBit : ∀ a b c : Bool, (a ≠ b ↔ c = true) → xor a b = c := by decide

lemma strip_count {k a : ℕ} (R : Finset ℕ) (b t : ℕ → Bool) (Y : ℕ → ℕ → Bool)
    (q : ℕ → ℕ) (hR : R ⊆ range a) (hak : a+2 ≤ k) (hq : ∀ p, q p < k)
    (hs : ∀ p < a+2, ∀ x < 2^k, Y (x ^^^ 2^(q p)) p = !(Y x p))
    (hl : ∀ p < a+2, ∀ i < p, ∀ x < 2^k, Y (x ^^^ 2^(q p)) i = Y x i) :
    ((range (2^k)).filter (fun x => ∀ j ∈ R, diffBit b (Y x) j = t j)).card =
      if (R.filter (fun j => b (j+1)=false ∧ b (j+2)=false ∧ b j ≠ t j)).Nonempty ∨
        (R.filter (fun j => j+1 ∈ R ∧ b (j+1)=true ∧ b (j+2)=false ∧ b (j+3)=true ∧
          xor (b j) (t j) ≠ t (j+1))).Nonempty then 0 else
      2^(k-((R.filter (fun j => b (j+1)=true ∧ b (j+2)=true)).card +
        ((R.filter (fun j => b (j+1) ≠ b (j+2))).image (pivot b)).card)) := by
  classical
  simp_rw [row_equiv]
  split_ifs with h
  · apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hg := (mem_filter.mp hx).2
    rcases h with ⟨j,hj⟩|⟨j,hj⟩
    · obtain ⟨hj,h1,h2,hne⟩ := mem_filter.mp hj
      exact hne (by simpa [goodRow,active,h1,h2] using hg j hj)
    · exact pair_wrong (mem_filter.mp hj).1 (mem_filter.mp hj).2 hg
  · have hn j (hj : j ∈ R) (hh : badPair R b t j) : False := h (Or.inr ⟨j,mem_filter.mpr ⟨hj,hh⟩⟩)
    have hw j (hj : j ∈ R) (h1 : b (j+1)=false) (h2 : b (j+2)=false) : b j=t j := by
      by_contra he
      exact h (Or.inl ⟨j,mem_filter.mpr ⟨hj,h1,h2,he⟩⟩)
    obtain ⟨target, ht⟩ := normalize b t hn hw
    rw [filter_congr (fun x _ => ht (Y x)), ← pivot_count]
    let P := (R.filter (fun j => active b j)).image (pivot b)
    have bounds {p} (hp : p ∈ P) : 0 < p ∧ p < a+2 := by
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hp
      have := mem_range.mp (hR (mem_filter.mp hj).1)
      unfold pivot; split <;> omega
    apply count_sites k (fun x p => obs b (Y x) p) q target P (fun p _ => hq p)
    · have hsub : P ⊆ range (a+2) := fun _ hp => mem_range.mpr (bounds hp).2
      exact (card_le_card hsub).trans ((card_range _).le.trans hak)
    · intro p hp x hx
      obtain ⟨hpos,hlt⟩ := bounds hp
      simp only [obs,hs p hlt x hx,hl p hlt (p-1) (by omega) x hx]
      cases b p <;> cases Y x (p-1) <;> cases Y x p <;> rfl
    · intro p hp i hi x hx
      simp only [obs,hl p (bounds hp).2 i hi x hx,hl p (bounds hp).2 (i-1) (by omega) x hx]

end PEqualNP.Outside.L_meta_33631

open PEqualNP.Outside.L_meta_33631 PEqualNP.Outside.L_meta_25883_aux Finset

theorem PEqualNP.Outside.L_meta_33631 : (∀ (k d a start init last c : Nat), 0 < d → 0 < a → a + 2 + 2*d ≤ k →
  let words := Finset.range (2^k)
  let rot := fun (s z : Nat) =>
    ((z <<< (s % k)) ||| (z >>> (k - s % k))) % 2^k
  let mix := fun z : Nat => z ^^^ rot d z ^^^ rot (k-d) z
  let site := fun j : Nat => (start+j) % k
  let label := fun (u x j : Nat) =>
    let y := mix (rot init x ^^^ u)
    xor (xor (y.testBit (site j))
      (!(y.testBit (site (j+1))) && y.testBit (site (j+2))))
      (xor ((rot last x).testBit (site j)) (c.testBit (site j)))
  ∀ u ∈ words, ∀ v ∈ words, ∀ (marks : Finset Nat) (target : Nat),
    let rows := (Finset.range a) ∩ marks
    let b := fun j : Nat => (mix u).testBit (site j) != (mix v).testBit (site j)
    let t := fun j : Nat => target.testBit j
    let wrong := rows.filter (fun j =>
      b (j+1) = false ∧ b (j+2) = false ∧ b j ≠ t j)
    let conflict := rows.filter (fun j =>
      j+1 ∈ rows ∧ b (j+1) = true ∧ b (j+2) = false ∧ b (j+3) = true ∧
      xor (b j) (t j) ≠ t (j+1))
    let edges := rows.filter (fun j => b (j+1) = true ∧ b (j+2) = true)
    let single := rows.filter (fun j => b (j+1) ≠ b (j+2))
    let pins := single.image (fun j => if b (j+1) then j+2 else j+1)
    (words.filter (fun x => ∀ j ∈ rows, xor (label u x j) (label v x j) = t j)).card =
      if wrong.Nonempty ∨ conflict.Nonempty then 0 else 2^(k - (edges.card + pins.card))) := by
  intro k d a start init last c hd ha hk words rot mix site label u hu v hv marks target rows b t wrong conflict edges single pins
  have hk0 : 0 < k := by omega
  have hu' : u < 2^k := mem_range.mp hu
  have hv' : v < 2^k := mem_range.mp hv
  let Y := fun x j => (mix (rot init x ^^^ u)).testBit (site j)
  let q := fun p => (((site p + d) % k + k - init % k) % k)
  have he (x j : ℕ) : xor (label u x j) (label v x j) = diffBit b (Y x) j :=
    xorBit _ _ _ (labelDiff start init last c x j hd (by omega) hu' hv')
  have hlt (p : ℕ) : (site p+d)%k < k := Nat.mod_lt _ hk0
  have flip (p i x : ℕ) (hx : x < 2^k) : Y (x ^^^ 2^(q p)) i =
      xor (Y x i) (ind k d ((site p+d)%k) (site i)) :=
    keyFlip init hd (by omega) (Nat.mod_lt _ hk0) (hlt p) hx hu'
  have result := strip_count (k:=k) (a:=a) rows b t Y q inter_subset_left (by omega)
    (fun p => Nat.mod_lt _ hk0) (by
      intro p hp x hx
      have hbit : ind k d ((site p+d)%k) (site p) = true := indName start hd hk hp
      rw [flip p p x hx, hbit]
      simp) (by
      intro p hp i hi x hx
      have hbit : ind k d ((site p+d)%k) (site i) = false := indName' start hd hk hp hi
      rw [flip p i x hx, hbit]
      simp)
  have heq : words.filter (fun x => ∀ j ∈ rows, xor (label u x j) (label v x j) = t j) =
      (range (2^k)).filter (fun x => ∀ j ∈ rows, diffBit b (Y x) j = t j) := by
    change (range (2^k)).filter _ = _
    apply filter_congr
    intro x _
    simp only [he]
  rw [heq]
  have pp : pivot b = (fun j : ℕ => if b (j+1) then j+2 else j+1) := by funext j; rfl
  rw [pp] at result
  exact result
