import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_712

variable {α β : Type*} [Fintype α]

noncomputable def cost (event : α → Prop) : Nat := by
  classical
  exact ∑ point, if event point then 1 else 0

lemma cost_card (event : α → Prop) [DecidablePred event] :
    cost event = (Finset.univ.filter event).card := by
  calc
    _ = ∑ point, if event point then 1 else 0 := by
      unfold cost
      apply Finset.sum_congr rfl
      intro point _
      by_cases yes : event point <;> simp [yes]
    _ = _ := by simpa only [Nat.cast_id] using Finset.sum_boole (R := Nat) event Finset.univ

lemma cost_transport (event : α → Prop) (perm : Equiv.Perm α) :
    cost (fun point => event (perm point)) = cost event := by
  classical
  exact Equiv.sum_comp perm (fun point => if event point then 1 else 0)

lemma cost_mono {left right : α → Prop} (imp : ∀ point, left point → right point) :
    cost left ≤ cost right := by
  classical
  unfold cost
  exact Finset.sum_le_sum fun point _ => by specialize imp point; split_ifs <;> simp_all

lemma cost_split {event left right : α → Prop}
    (imp : ∀ point, event point → left point ∨ right point) :
    cost event ≤ cost left + cost right := by
  classical
  unfold cost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun point _ => by specialize imp point; split_ifs <;> simp_all

def permute {ι : Type*} (relabel : Equiv.Perm ι) : Equiv.Perm (Equiv.Perm ι) where
  toFun perm := relabel.trans perm
  invFun perm := relabel.symm.trans perm
  left_inv perm := by ext; simp
  right_inv perm := by ext; simp

variable {b : Nat} {V : Type*} [AddCommGroup V]

abbrev Vertex (size : Nat) := Fin size × Bool
abbrev Match (size : Nat) := Equiv.Perm (Vertex size)

def score (table : Vertex b → Vertex b → V) (perm : Match b) :=
  ∑ slot, table (perm (slot,false)) (perm (slot,true))

lemma compare_scores (table : Vertex b → Vertex b → V) (target : V)
    (left right : Match b) (event : Match b → Prop)
    (witness : ∀ perm, event perm → score table (left.trans perm) ≠ score table (right.trans perm)) :
    cost event ≤ 2 * cost (fun perm => score table perm ≠ target) := by
  let bad := fun perm => score table perm ≠ target
  have bound := cost_split (left := fun perm => bad (permute left perm))
    (right := fun perm => bad (permute right perm)) (event := event) (by
      intro perm hit
      change score table (left.trans perm) ≠ target ∨ score table (right.trans perm) ≠ target
      by_contra! contra
      exact witness perm hit (contra.1.trans contra.2.symm))
  rw [cost_transport, cost_transport] at bound
  simpa [bad, two_mul] using bound

def edge (table : Vertex b → Vertex b → V) (first last : Vertex b) (perm : Match b) :=
  table (perm first) (perm last)

lemma reversal (table : Vertex b → Vertex b → V) (target : V) (slot : Fin b)
    {first last : Vertex b} (hne : first ≠ last) :
    cost (fun perm => edge table first last perm ≠ edge table last first perm) ≤
      2 * cost (fun perm => score table perm ≠ target) := by
  classical
  let src : Bool → Vertex b := fun side => (slot, side)
  let dst : Bool → Vertex b := fun side => if side then last else first
  obtain ⟨arrange, ha⟩ := Equiv.Perm.exists_extending_pair src dst
    (fun _ _ hh => congrArg Prod.snd hh) (by intro x y hh; cases x <;> cases y <;> simp_all [dst])
  let flip := Equiv.swap (slot,false) (slot,true)
  apply compare_scores table target arrange (flip.trans arrange)
  intro perm hit eqn
  let term := fun (map : Match b) (idx : Fin b) => table (map (idx,false)) (map (idx,true))
  change (∑ idx, term (arrange.trans perm) idx) = ∑ idx, term ((flip.trans arrange).trans perm) idx at eqn
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ slot),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ slot)] at eqn
  have rest : (∑ idx ∈ Finset.univ.erase slot, term (arrange.trans perm) idx) =
      ∑ idx ∈ Finset.univ.erase slot, term ((flip.trans arrange).trans perm) idx := by
    apply Finset.sum_congr rfl
    intro idx hi
    have hn := (Finset.mem_erase.mp hi).1
    simp [term, flip, Equiv.swap_apply_def, hn]
  rw [rest] at eqn
  have loc := add_right_cancel eqn
  have hl : arrange (slot,false) = first := ha false
  have hr : arrange (slot,true) = last := ha true
  exact hit (by simpa [term, flip, hl, hr, edge] using loc)

lemma rectangle (table : Vertex b → Vertex b → V) (target : V) {slot next : Fin b}
    (hs : slot ≠ next) {aa bb cc dd : Vertex b}
    (hab : aa ≠ bb) (hac : aa ≠ cc) (had : aa ≠ dd)
    (hbc : bb ≠ cc) (hbd : bb ≠ dd) (hcd : cc ≠ dd) :
    cost (fun perm => edge table aa bb perm + edge table cc dd perm ≠
      edge table aa dd perm + edge table cc bb perm) ≤
      2 * cost (fun perm => score table perm ≠ target) := by
  classical
  let src : Fin 4 → Vertex b := ![(slot,false), (slot,true), (next,false), (next,true)]
  let dst : Fin 4 → Vertex b := ![aa, bb, cc, dd]
  obtain ⟨arrange, ha⟩ := Equiv.Perm.exists_extending_pair src dst
    (by intro x y hh; fin_cases x <;> fin_cases y <;> simp_all [src])
    (by intro x y hh; fin_cases x <;> fin_cases y <;> simp_all [dst])
  let flip := Equiv.swap (slot,true) (next,true)
  apply compare_scores table target arrange (flip.trans arrange)
  intro perm hit eqn
  let term := fun (map : Match b) (idx : Fin b) => table (map (idx,false)) (map (idx,true))
  have extract (map : Match b) : (∑ idx, term map idx) =
      term map slot + term map next + ∑ idx ∈ (Finset.univ.erase slot).erase next, term map idx := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ slot),
      ← Finset.add_sum_erase _ _ (show next ∈ Finset.univ.erase slot by simp [Ne.symm hs]), add_assoc]
  change (∑ idx, term (arrange.trans perm) idx) = ∑ idx, term ((flip.trans arrange).trans perm) idx at eqn
  rw [extract, extract] at eqn
  have rest : (∑ idx ∈ (Finset.univ.erase slot).erase next, term (arrange.trans perm) idx) =
      ∑ idx ∈ (Finset.univ.erase slot).erase next, term ((flip.trans arrange).trans perm) idx := by
    apply Finset.sum_congr rfl
    intro idx hi
    obtain ⟨hn, hi⟩ := Finset.mem_erase.mp hi
    have hm := (Finset.mem_erase.mp hi).1
    simp [term, flip, Equiv.swap_apply_def, hm, hn]
  rw [rest] at eqn
  have loc := add_right_cancel eqn
  have h0 : arrange (slot,false) = aa := ha 0
  have h1 : arrange (slot,true) = bb := ha 1
  have h2 : arrange (next,false) = cc := ha 2
  have h3 : arrange (next,true) = dd := ha 3
  exact hit (by simpa [term, flip, Equiv.swap_apply_def, hs, hs.symm, h0, h1, h2, h3, edge] using loc)

def tri (table : Vertex b → Vertex b → V) (anchor row col : Vertex b) (perm : Match b) :=
  edge table row col perm - edge table anchor row perm - edge table anchor col perm

noncomputable def dist (left right : α → β) := cost (fun point => left point ≠ right point)

lemma dist_triangle (left middle right : α → β) :
    dist left right ≤ dist left middle + dist middle right := by
  apply cost_split
  intro point hit
  by_contra! same
  exact hit (same.1.trans same.2)

lemma tri_bound (table : Vertex b → Vertex b → V) (target : V) {slot next : Fin b}
    (hs : slot ≠ next) {anchor first last row col : Vertex b}
    (haf : anchor ≠ first) (hal : anchor ≠ last) (hfl : first ≠ last)
    (har : anchor ≠ row) (hac : anchor ≠ col) (hrc : row ≠ col) :
    dist (tri table anchor row col) (tri table anchor first last) ≤
      13 * cost (fun perm => score table perm ≠ target) := by
  let bad := cost (fun perm => score table perm ≠ target)
  let triangle := tri table anchor
  have rev (ii jj : Vertex b) (hne : ii ≠ jj) : dist (triangle ii jj) (triangle jj ii) ≤ 2 * bad := by
    apply le_trans _ (reversal table target slot hne)
    apply cost_mono
    intro perm hit same
    apply hit
    change edge table ii jj perm - _ - _ = edge table jj ii perm - _ - _
    rw [same]
    abel
  have column (ii jj kk : Vertex b) (hai : anchor ≠ ii) (haj : anchor ≠ jj) (hak : anchor ≠ kk)
      (hij : ii ≠ jj) (hik : ii ≠ kk) : dist (triangle ii jj) (triangle ii kk) ≤ 2 * bad := by
    by_cases hjk : jj = kk
    · subst kk; simp [dist, cost]
    apply le_trans _ (rectangle table target hs haj hai hak hij.symm hjk hik)
    apply cost_mono
    intro perm hit same
    apply hit
    change edge table ii jj perm - _ - _ = edge table ii kk perm - _ - _
    change edge table anchor jj perm + edge table ii kk perm =
      edge table anchor kk perm + edge table ii jj perm at same
    have swap : edge table ii jj perm = (edge table anchor jj perm + edge table ii kk perm) -
        edge table anchor kk perm := by rw [same]; abel
    rw [swap]
    abel
  have line (ii jj kk : Vertex b) (hai : anchor ≠ ii) (haj : anchor ≠ jj) (hak : anchor ≠ kk)
      (hij : ii ≠ jj) (hik : ii ≠ kk) : dist (triangle jj ii) (triangle kk ii) ≤ 6 * bad := by
    have h1 := rev jj ii hij.symm
    have h2 := column ii jj kk hai haj hak hij hik
    have h3 := rev ii kk hik
    have h4 := dist_triangle (triangle jj ii) (triangle ii jj) (triangle ii kk)
    have h5 := dist_triangle (triangle jj ii) (triangle ii kk) (triangle kk ii)
    omega
  change dist (triangle row col) (triangle first last) ≤ 13 * bad
  by_cases hrl : row = last
  · subst row
    by_cases hcf : col = first
    · subst col; have hh := rev last first hfl.symm; omega
    have h1 := line col last first hac hal haf hrc.symm hcf
    have h2 := column first col last haf hac hal (Ne.symm hcf) hfl
    have h3 := dist_triangle (triangle last col) (triangle first col) (triangle first last)
    omega
  have h1 := column row col last har hac hal hrc hrl
  have h2 := line last row first hal har haf (Ne.symm hrl) hfl.symm
  have h3 := dist_triangle (triangle row col) (triangle row last) (triangle first last)
  omega

lemma average {ι π : Type*} [Fintype ι] [Fintype π] [Nonempty π]
    (event : π → ι → Prop) (budget : ι → Nat)
    (bounds : ∀ idx, cost (fun perm => event perm idx) ≤ budget idx) :
    ∃ perm, cost (event perm) * Fintype.card π ≤ ∑ idx, budget idx := by
  classical
  obtain ⟨best, _, least⟩ := Finset.univ.exists_min_image (fun perm => cost (event perm))
    Finset.univ_nonempty
  refine ⟨best, ?_⟩
  calc
    _ = ∑ _ : π, cost (event best) := by simp [Nat.mul_comm]
    _ ≤ ∑ perm : π, cost (event perm) := Finset.sum_le_sum fun perm hp => least perm hp
    _ = ∑ idx, cost (fun perm => event perm idx) := by unfold cost; rw [Finset.sum_comm]
    _ ≤ _ := Finset.sum_le_sum fun idx _ => bounds idx

lemma obtain_table (table : Vertex b → Vertex b → V) (target : V) {slot next : Fin b}
    (hs : slot ≠ next) : ∃ (constant : V) (labels : Vertex b → V),
    cost (fun pair : Vertex b × Vertex b => pair.1 ≠ pair.2 ∧
      table pair.1 pair.2 ≠ constant + labels pair.1 + labels pair.2) * Nat.factorial (2*b) ≤
      13 * cost (fun perm => score table perm ≠ target) * (2*b) * (2*b-1) := by
  classical
  let anchor : Vertex b := (slot,false)
  let first : Vertex b := (slot,true)
  let last : Vertex b := (next,false)
  have haf : anchor ≠ first := by simp [anchor, first]
  have hal : anchor ≠ last := by simp [anchor, last, hs]
  have hfl : first ≠ last := by simp [first, last]
  let constant := tri table anchor first last
  let labels (perm : Match b) (idx : Vertex b) :=
    if idx = anchor then -constant perm else edge table anchor idx perm
  let event (perm : Match b) (pair : Vertex b × Vertex b) :=
    pair.1 ≠ pair.2 ∧ edge table pair.1 pair.2 perm ≠
      constant perm + labels perm pair.1 + labels perm pair.2
  let limit := 13 * cost (fun perm => score table perm ≠ target)
  let budget (pair : Vertex b × Vertex b) := if pair.1 ≠ pair.2 then limit else 0
  have bounds (pair : Vertex b × Vertex b) : cost (fun perm => event perm pair) ≤ budget pair := by
    obtain ⟨row,col⟩ := pair
    by_cases hrc : row = col
    · subst col; simp [event, cost, budget]
    change _ ≤ if row ≠ col then limit else 0
    rw [ite_eq_left hrc]
    by_cases har : anchor = row
    · subst row; simp [event, cost, labels, Ne.symm hrc]
    by_cases hac : anchor = col
    · subst col
      have hh := reversal table target slot hrc
      have ht : cost (fun perm => event perm (row,anchor)) ≤
          cost (fun perm => edge table row anchor perm ≠ edge table anchor row perm) := by
        apply cost_mono
        intro perm hit eqn
        exact hit.2 (by simp [labels, hrc, eqn, add_comm])
      exact ht.trans (hh.trans (Nat.mul_le_mul_right _ (by decide : 2 ≤ 13)))
    apply le_trans _ (tri_bound table target hs haf hal hfl har hac hrc)
    apply cost_mono
    intro perm hit eqn
    apply hit.2
    simp only [labels, ite_eq_right (Ne.symm har), ite_eq_right (Ne.symm hac)]
    change edge table row col perm - edge table anchor row perm - edge table anchor col perm = constant perm at eqn
    rw [← eqn]
    abel
  obtain ⟨best, bound⟩ := average event budget bounds
  refine ⟨constant best, fun idx => labels best (best.symm idx), ?_⟩
  let actual (pair : Vertex b × Vertex b) := pair.1 ≠ pair.2 ∧ table pair.1 pair.2 ≠
    constant best + labels best (best.symm pair.1) + labels best (best.symm pair.2)
  have shift := cost_transport actual (best.prodCongr best)
  have agree : (fun point => actual ((best.prodCongr best) point)) = event best := by
    funext point; simp [actual, event, edge]
  rw [agree] at shift
  have count : Fintype.card (Vertex b) = 2*b := by simp [Vertex, Nat.mul_comm]
  have perms : Fintype.card (Match b) = Nat.factorial (2*b) := by rw [Fintype.card_perm, count]
  have pairs : (Finset.univ.filter (fun pair : Vertex b × Vertex b => pair.1 ≠ pair.2)) =
      (Finset.univ : Finset (Vertex b)).offDiag := by ext; simp
  have total : (∑ idx, budget idx) = limit * (2*b) * (2*b-1) := by
    simp only [budget, ← Finset.sum_filter, Finset.sum_const, pairs, Finset.offDiag_card,
      Finset.card_univ, count, nsmul_eq_mul]
    rw [← Nat.mul_sub_one, Nat.cast_id, Nat.mul_comm _ limit, ← Nat.mul_assoc]
  rw [shift, perms, total] at bound
  exact bound

end PEqualNP.Outside.L_lib_712

theorem PEqualNP.Outside.L_lib_712 : (∀ (b w : Nat), 2 ≤ b →
  let I := Fin b × Bool
  let V := Fin w → ZMod 2
  ∀ (f : I → I → V) (h : V),
    let failures := (Finset.univ : Finset (Equiv.Perm I)).filter (fun p =>
      (∑ u : Fin b, f (p (u,false)) (p (u,true))) ≠ h)
    ∃ (c : V) (z : I → V),
      let errors := (Finset.univ : Finset (I × I)).filter (fun pair =>
        pair.1 ≠ pair.2 ∧ f pair.1 pair.2 ≠ c + z pair.1 + z pair.2)
      errors.card * Nat.factorial (2*b) ≤ 13 * failures.card * (2*b) * (2*b-1)) := by
  intro b w hb
  dsimp only
  intro table target
  classical
  obtain ⟨constant, labels, bound⟩ := PEqualNP.Outside.L_lib_712.obtain_table table target
    (slot := ⟨0, by omega⟩) (next := ⟨1, by omega⟩) (by intro eqn; cases eqn)
  refine ⟨constant, labels, ?_⟩
  simpa only [PEqualNP.Outside.L_lib_712.cost_card, PEqualNP.Outside.L_lib_712.score] using bound
