import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_30272

open PEqualNP.CircuitLowerBounds

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

section FreeNot

def ops {n : ℕ} (x y : BitVec n) : List (BitVec n) :=
  [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]

abbrev basicOps {n : ℕ} (a b : BitVec n) : Finset (BitVec n) := (ops a b).toFinset

theorem ops_swap {n : ℕ} (a b : BitVec n) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def holds {n : ℕ} (av : Finset (BitVec n)) (z : BitVec n) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {n : ℕ} {av : Finset (BitVec n)} {z a : BitVec n} (h : holds av z) :
    holds (insert a av) z := by
  rcases h with h | h | ⟨u, hu, he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u, Finset.mem_insert_of_mem hu, he⟩)

theorem holds_mono {n : ℕ} {av av' : Finset (BitVec n)} (sub : av ⊆ av') {x : BitVec n}
    (h : holds av x) : holds av' x := by
  rcases h with h | h | ⟨a, ha, e⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨a, sub ha, e⟩)

theorem holds_not {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} (h : holds av z) :
    holds av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable {n : ℕ} (av : Finset (BitVec n)) (z : BitVec n) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} (h : reachable av z) :
    reachable av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds_not hw⟩

theorem bv_zero_and {n : ℕ} (x : BitVec n) : (0 : BitVec n) &&& x = 0 := BitVec.zero_and
theorem bv_and_zero {n : ℕ} (x : BitVec n) : x &&& (0 : BitVec n) = 0 := BitVec.and_zero
theorem bv_zero_or {n : ℕ} (x : BitVec n) : (0 : BitVec n) ||| x = x := BitVec.zero_or
theorem bv_or_zero {n : ℕ} (x : BitVec n) : x ||| (0 : BitVec n) = x := BitVec.or_zero
theorem bv_not_zero_and {n : ℕ} (x : BitVec n) : ~~~(0 : BitVec n) &&& x = x := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
theorem bv_and_not_zero {n : ℕ} (x : BitVec n) : x &&& ~~~(0 : BitVec n) = x := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
theorem bv_not_zero_or {n : ℕ} (x : BitVec n) : ~~~(0 : BitVec n) ||| x = ~~~0 := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
theorem bv_or_not_zero {n : ℕ} (x : BitVec n) : x ||| ~~~(0 : BitVec n) = ~~~0 := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp

set_option maxRecDepth 5000 in
theorem and_reach {n : ℕ} {av : Finset (BitVec n)} {x y : BitVec n}
    (hx : holds av x) (hy : holds av y) : reachable av (x &&& y) := by
  have const0 : holds av (0 : BitVec n) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [bv_zero_and]; exact .inl const0
  · rw [bv_not_zero_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [bv_and_zero]; exact .inl const0
  · rw [bv_and_not_zero]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const0 | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : BitVec n) (hw : w ∈ basicOps a b) (z : BitVec n) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps, ops]) _ (.inl rfl)
  · exact add _ (by simp [basicOps, ops]) _ (.inl rfl)
  · exact add _ (by simp [basicOps, ops]) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps, ops]) _ (.inr BitVec.not_or.symm)

theorem or_reach {n : ℕ} {av : Finset (BitVec n)} {x y : BitVec n}
    (hx : holds av x) (hy : holds av y) : reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using
    reachable_not (and_reach (holds_not hx) (holds_not hy))

theorem mem_ops_reach {n : ℕ} {av : Finset (BitVec n)} {x y z : BitVec n}
    (hx : holds av x) (hy : holds av y) (hz : z ∈ basicOps x y) : reachable av z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact and_reach hx hy
  · exact or_reach hx hy
  · exact and_reach hx (holds_not hy)
  · exact and_reach hy (holds_not hx)

theorem mem_ops_const {n : ℕ} {av : Finset (BitVec n)} {x y z : BitVec n}
    (hx : holds av x) (hy : holds av y)
    (hconst : (x = 0 ∨ x = ~~~0) ∨ (y = 0 ∨ y = ~~~0))
    (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  have h0 : holds av (0 : BitVec n) := .inl rfl
  have h1 : holds av (~~~(0 : BitVec n)) := .inr (.inl rfl)
  have hnx : holds av (~~~x) := holds_not hx
  have hny : holds av (~~~y) := holds_not hy
  rcases hconst with (rfl | rfl) | (rfl | rfl) <;> rcases hz with rfl | rfl | rfl | rfl
  · rw [bv_zero_and]; exact h0
  · rw [bv_zero_or]; exact hy
  · rw [bv_zero_and]; exact h0
  · rw [bv_and_not_zero]; exact hy
  · rw [bv_not_zero_and]; exact hy
  · rw [bv_not_zero_or]; exact h1
  · rw [bv_not_zero_and]; exact hny
  · rw [BitVec.not_not, bv_and_zero]; exact h0
  · rw [bv_and_zero]; exact h0
  · rw [bv_or_zero]; exact hx
  · rw [bv_and_not_zero]; exact hx
  · rw [bv_zero_and]; exact h0
  · rw [bv_and_not_zero]; exact hx
  · rw [bv_or_not_zero]; exact h1
  · rw [BitVec.not_not, bv_and_zero]; exact h0
  · rw [bv_not_zero_and]; exact hnx

def SignedBuild {n : ℕ} (k : ℕ) (av : Finset (BitVec n)) (z : BitVec n) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps z k av ∨ build basicOps (~~~z) k av

theorem sb_zero {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} (h : holds av z) :
    SignedBuild 0 av z := by
  rcases h with h | h | ⟨a, ha, e | e⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · subst z; exact Or.inr (Or.inr (Or.inl ha))
  · subst z; exact Or.inr (Or.inr (Or.inr (by simpa only [BitVec.not_not, build] using ha)))

theorem sb_wait {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} {k : ℕ}
    (h : SignedBuild k av z) : SignedBuild (k + 1) av z := by
  rcases h with h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl (.inl h)))
  · exact .inr (.inr (.inr (.inl h)))

theorem sb_le {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} {k l : ℕ} (hkl : k ≤ l)
    (h : SignedBuild k av z) : SignedBuild l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb_wait ih

theorem sb_step {n : ℕ} {av : Finset (BitVec n)} {t a b z : BitVec n} {k : ℕ}
    (ha : a ∈ av) (hb : b ∈ av) (hne : a ≠ b) (hz : z ∈ basicOps a b)
    (h : SignedBuild k (insert z av) t) : SignedBuild (k + 1) av t := by
  rcases h with h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl (.inr ⟨a, ha, b, hb, hne, z, hz, h⟩)))
  · exact .inr (.inr (.inr (.inr ⟨a, ha, b, hb, hne, z, hz, h⟩)))

theorem sb_advance {n : ℕ} {av : Finset (BitVec n)} {z t : BitVec n} {k : ℕ}
    (hz : reachable av z)
    (next : ∀ av' : Finset (BitVec n), av ⊆ av' → holds av' z → SignedBuild k av' t) :
    SignedBuild (k + 1) av t := by
  rcases hz with h | ⟨a, ha, b, hb, hn, w, hw, ok⟩
  · exact sb_wait (next av (fun _ h => h) h)
  · exact sb_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

theorem ops_map_of {n m : ℕ} {f : BitVec n → BitVec m}
    (hAnd : ∀ a b, f (a &&& b) = (f a &&& f b))
    (hOr : ∀ a b, f (a ||| b) = (f a ||| f b))
    (hNot : ∀ a, f (~~~a) = ~~~(f a)) :
    ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b) := by
  intro a b z hz
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hAnd, hOr, hNot]

theorem live_transport {n m : ℕ} {f : BitVec n → BitVec m}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : BitVec n} {k : ℕ} {s : Finset (BitVec n)} {av : Finset (BitVec m)}
    (run : live basicOps g k s)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild k av (f g) := by
  induction k generalizing s av with
  | zero =>
    change s = {g} at run
    exact sb_zero (hav g (by simp [run]))
  | succ k ih =>
    rcases run with skip | ⟨a, ha, b, hb, hn, z, hz, hout, r, he, tail⟩
    · exact sb_wait (ih skip hav)
    · apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) (hm a b z hz))
      intro av' sub ok
      apply ih tail
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hr
      · exact ok
      · exact holds_mono sub (hav u (by simp [he, hr]))

theorem live_transport_save_const {n m : ℕ} {f : BitVec n → BitVec m}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g p : BitVec n} {k : ℕ} {s : Finset (BitVec n)} {av : Finset (BitVec m)}
    (run : live basicOps g k s)
    (hp : p ∈ s) (hconst : f p = 0 ∨ f p = ~~~0)
    (hng : f g ≠ 0 ∧ f g ≠ ~~~0)
    (hav : ∀ w ∈ s, holds av (f w)) :
    1 ≤ k ∧ SignedBuild (k - 1) av (f g) := by
  induction k generalizing s av with
  | zero =>
    change s = {g} at run
    have hpg : p = g := by simpa [run] using hp
    subst hpg
    rcases hconst with h | h
    · exact (hng.1 h).elim
    · exact (hng.2 h).elim
  | succ k ih =>
    simp only [Nat.add_sub_cancel]
    rcases run with skip | ⟨a, ha, b, hb, hn, z, hz, hout, r, he, tail⟩
    · obtain ⟨hk, hsb⟩ := ih skip hp hav
      exact ⟨by omega, sb_le (by omega) hsb⟩
    · have mapped := hm a b z hz
      have inOld : ∀ u ∈ r, holds av (f u) := fun u hu => hav u (by simp [he, hu])
      by_cases touches : p = a ∨ p = b
      · have hc : (f a = 0 ∨ f a = ~~~0) ∨ (f b = 0 ∨ f b = ~~~0) :=
          touches.elim (fun h => .inl (h ▸ hconst)) (fun h => .inr (h ▸ hconst))
        have collapsed := mem_ops_const (hav a ha) (hav b hb) hc mapped
        refine ⟨by omega, live_transport hm tail ?_⟩
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hr
        · exact collapsed
        · exact inOld u hr
      · have pr : p ∈ r := by
          rw [he] at hp
          simpa [Finset.mem_insert, not_or.mp touches |>.1, not_or.mp touches |>.2] using hp
        have pt : p ∈ insert z r := Finset.mem_insert_of_mem pr
        refine ⟨by omega, ?_⟩
        rcases mem_ops_reach (hav a ha) (hav b hb) mapped with hok | ⟨x, hx, y, hy, hxy, w, hw, hok⟩
        · obtain ⟨hk, hsb⟩ := ih tail pt (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hr
            · exact hok
            · exact inOld u hr)
          exact sb_le (by omega) hsb
        · obtain ⟨hk, hsb⟩ := ih tail pt (av := insert w av) (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hr
            · exact hok
            · exact holds_insert (inOld u hr))
          have hstep := sb_step hx hy hxy hw hsb
          exact sb_le (by omega) hstep

def selectRows {n m : ℕ} (rows : Fin m → Fin n) (w : BitVec n) : BitVec m :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin m => w[(rows k).val]))).cast List.length_ofFn

theorem selectRows_bit {n m : ℕ} (rows : Fin m → Fin n) (w : BitVec n) (j : Fin m) :
    (selectRows rows w)[j.val] = w[(rows j).val] := by
  rw [← BitVec.getLsbD_eq_getElem j.isLt]
  simp only [selectRows, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, dite_eq_left, Option.getD_some]

theorem selectRows_land {n m : ℕ} (rows : Fin m → Fin n) (u v : BitVec n) :
    selectRows rows (u &&& v) = (selectRows rows u &&& selectRows rows v) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin m := ⟨j, hj⟩
  change (selectRows rows (u &&& v))[k.val] = (selectRows rows u &&& selectRows rows v)[k.val]
  simp only [selectRows_bit, BitVec.getElem_and]

theorem selectRows_lor {n m : ℕ} (rows : Fin m → Fin n) (u v : BitVec n) :
    selectRows rows (u ||| v) = (selectRows rows u ||| selectRows rows v) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin m := ⟨j, hj⟩
  change (selectRows rows (u ||| v))[k.val] = (selectRows rows u ||| selectRows rows v)[k.val]
  simp only [selectRows_bit, BitVec.getElem_or]

theorem selectRows_neg {n m : ℕ} (rows : Fin m → Fin n) (u : BitVec n) :
    selectRows rows (~~~u) = ~~~selectRows rows u := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin m := ⟨j, hj⟩
  change (selectRows rows (~~~u))[k.val] = (~~~selectRows rows u)[k.val]
  simp only [selectRows_bit, BitVec.getElem_not]

def bitDiff {n : ℕ} (a b : Fin n) (w : BitVec n) : Prop :=
  w[a.val] ≠ w[b.val]

theorem ops_bitDiff {n : ℕ} (a b : Fin n) (x y z : BitVec n) (hz : z ∈ basicOps x y)
    (hd : bitDiff a b z) : bitDiff a b x ∨ bitDiff a b y := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨hx, hy⟩ := fail
  apply hd
  unfold bitDiff at hx hy
  simp only [not_not] at hx hy
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, hx, hy]

theorem bitDiff_not {n : ℕ} {a b : Fin n} {w : BitVec n} (h : bitDiff a b w) :
    bitDiff a b (~~~w) := by
  intro heq
  apply h
  simp only [BitVec.getElem_not] at heq
  cases ha : w[a.val] <;> cases hb : w[b.val] <;> simp_all

theorem live_has_unique_sep {n : ℕ} {g p : BitVec n} {k : ℕ}
    {s : Finset (BitVec n)} {ls : List (BitVec n)}
    (hs : s ⊆ ls.toFinset) (hl : live basicOps g k s)
    (a b : Fin n) (hd : bitDiff a b g)
    (huniq : ∀ w ∈ ls, bitDiff a b w → w = p) : p ∈ s := by
  obtain ⟨w, hw, hdw⟩ := live_separates (bitDiff a b) hd (ops_bitDiff a b) hl
  have hwp : w = p := huniq w (List.mem_toFinset.mp (hs hw)) hdw
  exact hwp ▸ hw

theorem sep_of_all {n : ℕ} (a b : Fin n) (ls : List (BitVec n)) (p : BitVec n)
    (h : ls.all (fun w => !(w[a.val] != w[b.val]) || w == p) = true) :
    ∀ w ∈ ls, bitDiff a b w → w = p := by
  intro w hw hdiff
  have h1 := List.all_eq_true.mp h w hw
  simp only [Bool.or_eq_true, Bool.not_eq_true', bne_eq_false_iff_eq, beq_iff_eq] at h1
  exact h1.resolve_left hdiff

theorem map_holds_list {n m : ℕ} (f : BitVec n → BitVec m) (src : List (BitVec n)) (dst : List (BitVec m))
    (h : src.all (fun w => f w == 0 || f w == ~~~0 || dst.any (fun d => f w == d)) = true) :
    ∀ w ∈ src, holds dst.toFinset (f w) := by
  intro w hw
  have h1 := List.all_eq_true.mp h w hw
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h1
  rcases h1 with (h0 | h1) | ⟨d, hd, hwd⟩
  · exact .inl h0
  · exact .inr (.inl h1)
  · exact .inr (.inr ⟨d, List.mem_toFinset.mpr hd, .inl hwd⟩)

theorem unwrap_sb {n : ℕ} {k : ℕ} {av : Finset (BitVec n)} {z : BitVec n}
    (h0 : z ≠ 0) (h1 : z ≠ ~~~0) (h : SignedBuild k av z) :
    ∃ t, (t = z ∨ t = ~~~z) ∧ build basicOps t k av := by
  rcases h with hz | hz | hb | hb
  · exact (h0 hz).elim
  · exact (h1 hz).elim
  · exact ⟨z, .inl rfl, hb⟩
  · exact ⟨~~~z, .inr rfl, hb⟩

theorem not_const_of_neg {n : ℕ} {w : BitVec n} (h : w ≠ 0 ∧ w ≠ ~~~0) :
    ~~~w ≠ 0 ∧ ~~~w ≠ ~~~0 := by
  refine ⟨fun heq => h.2 ?_, fun heq => h.1 ?_⟩
  · simpa only [BitVec.not_not] using congrArg (fun u : BitVec n => ~~~u) heq
  · simpa only [BitVec.not_not] using congrArg (fun u : BitVec n => ~~~u) heq

end FreeNot

section SearchP

abbrev WP (P : ℕ) := BitVec (P + P)
def sepP {P : ℕ} (x : WP P) : BitVec P := ((x >>> P) ^^^ x).setWidth P
def cutsP {P : ℕ} (ws : List (WP P)) : BitVec P := ws.foldr (fun w v => sepP w ||| v) 0
def goalP (P : ℕ) : WP P := BitVec.allOnes P ++ (0 : BitVec P)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def differsP {P : ℕ} (i : Fin P) (w : WP P) : Prop :=
  w.getLsbD (P + i.val) ≠ w.getLsbD i.val

theorem goalP_differs {P : ℕ} (i : Fin P) : differsP i (goalP P) := by
  unfold differsP goalP
  have hi : i.val < P := i.isLt
  have hlo : (BitVec.allOnes P ++ (0 : BitVec P)).getLsbD i.val = false := by
    rw [BitVec.getLsbD_append]
    simp [hi]
  have hhi : (BitVec.allOnes P ++ (0 : BitVec P)).getLsbD (P + i.val) = true := by
    rw [BitVec.getLsbD_append]
    have hnot : ¬ (P + i.val < P) := by omega
    simp only [hnot, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_allOnes]
  rw [hlo, hhi]
  decide

theorem ngoalP_differs {P : ℕ} (i : Fin P) : differsP i (~~~goalP P) := by
  have h := goalP_differs i
  unfold differsP at h ⊢
  have h1 : P + i.val < P + P := by omega
  have h2 : i.val < P + P := by omega
  simp only [BitVec.getLsbD_not, h1, h2, decide_true, Bool.true_and]
  intro heq
  apply h
  cases a : (goalP P).getLsbD (P + i.val) <;> cases b : (goalP P).getLsbD i.val <;> simp_all

theorem ops_differsP {P : ℕ} (i : Fin P) (a b z : WP P) (hz : z ∈ basicOps a b)
    (hd : differsP i z) : differsP i a ∨ differsP i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differsP at ha hb
  simp only [not_not] at ha hb
  have hi : P + i.val < P + P := by omega
  have hi' : i.val < P + P := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cutsP_spec {P : ℕ} (ws : List (WP P)) (i : Fin P) :
    (cutsP ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differsP i w := by
  induction ws with
  | nil => simp [cutsP]
  | cons a rest ih =>
    change (sepP a ||| cutsP rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sepP, i.isLt, differsP, Nat.add_comm, bx]

theorem cutsP_full {P : ℕ} {g : WP P} (hg : g = goalP P ∨ g = ~~~goalP P) {k : ℕ} {ws : List (WP P)}
    (h : live basicOps g k ws.toFinset) : cutsP ws = BitVec.allOnes P := by
  have hd : ∀ i, differsP i g := by
    intro i; rcases hg with rfl | rfl
    · exact goalP_differs i
    · exact ngoalP_differs i
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differsP ⟨j, hj⟩) (hd ⟨j, hj⟩) (ops_differsP ⟨j, hj⟩) h
  have hbit := (cutsP_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

def keepChoices {α : Type} (a b : α) (r : List α) : List (List α) :=
  [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {α : Type} [DecidableEq α] {ws r : List α} {a b : α} {needed : Finset α}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {α : Type} [DecidableEq α] {goal : α} {ws : List α} (hn : ws.Nodup)
    (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatchP (P : ℕ) (extra : ℕ) (next : ℕ → List (WP P) → Bool) (a b : WP P) (r : List (WP P)) : Bool :=
  let base := cutsP r
  let full := BitVec.allOnes P
  (ops a b).any fun w =>
    let v := sepP w ||| base
    ((v == full) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sepP a == full) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sepP b == full) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sepP a ||| sepP b == full) && next (extra - 2) (w :: a :: b :: r))

def optimizedP (P : ℕ) : ℕ → ℕ → List (WP P) → Bool
  | 0, _, ws => (ws == [goalP P] || ws == [~~~goalP P])
  | k + 1, extra, ws => (ws == [goalP P] || ws == [~~~goalP P]) ||
    (pairs ws).any (fun (a, b, r) => dispatchP P extra (optimizedP P k) a b r)

theorem dispatchP_complete {P k extra : ℕ} {a b z : WP P} {r kept : List (WP P)}
    (next : ℕ → List (WP P) → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cutsP (z :: kept) = BitVec.allOnes P) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatchP P extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cutsP, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimizedP_complete {P : ℕ} {g : WP P} (hg : g = goalP P ∨ g = ~~~goalP P) (n : ℕ)
    (ws : List (WP P)) (extra : ℕ) (hn : ws.Nodup) (room : extra + ws.length = n + 1)
    (h : live basicOps g n ws.toFinset) : optimizedP P n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimizedP, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimizedP, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : WP P} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatchP P extra (optimizedP P k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatchP_complete (k := k) (extra := extra) (optimizedP P k) hop hk (by omega)
          (by omega) (cutsP_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimizedP, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap,
          go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def searchP (P : ℕ) (n : ℕ) (inputs : List (WP P)) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n + 1) && (cutsP ws == BitVec.allOnes P) && optimizedP P n (n + 1 - ws.length) ws

theorem searchP_complete {P : ℕ} {g : WP P} (hg : g = goalP P ∨ g = ~~~goalP P) (n : ℕ)
    (inputs : List (WP P)) (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) :
    searchP P n inputs = true := by
  classical
  obtain ⟨s, hs, hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws, List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cutsP_full hg hl',
      optimizedP_complete hg n ws _ hnd (by omega : n + 1 - ws.length + ws.length = n + 1) hl']⟩

theorem goalP_ne_const {P : ℕ} (hP : 0 < P) :
    goalP P ≠ 0 ∧ goalP P ≠ ~~~0 ∧ ~~~goalP P ≠ 0 ∧ ~~~goalP P ≠ ~~~0 := by
  have hd := goalP_differs ⟨0, hP⟩
  have hdn := ngoalP_differs ⟨0, hP⟩
  have h0 : ¬ differsP ⟨0, hP⟩ (0 : WP P) := by unfold differsP; simp
  have h1 : ¬ differsP ⟨0, hP⟩ (~~~(0 : WP P)) := by
    unfold differsP
    have hb : 0 < P + P := by omega
    simp [hb]
    omega
  exact ⟨fun e => h0 (e ▸ hd), fun e => h1 (e ▸ hd), fun e => h0 (e ▸ hdn), fun e => h1 (e ▸ hdn)⟩

theorem signed_rejectP {P k : ℕ} (hP : 0 < P) {ws : List (WP P)} (hn : ws.Nodup)
    (hf : searchP P k ws = false) {t : WP P} (ht : t = goalP P ∨ t = ~~~goalP P)
    (h : SignedBuild k ws.toFinset t) : False := by
  have nt := goalP_ne_const hP
  rcases ht with rfl | rfl
  all_goals
    rcases h with h | h | h | h
    · first | exact nt.1 h | exact nt.2.2.1 h
    · first | exact nt.2.1 h | exact nt.2.2.2 h
    · exact Bool.noConfusion (hf.symm.trans (searchP_complete (by simp) k ws hn h))
    · exact Bool.noConfusion (hf.symm.trans (searchP_complete (by simp) k ws hn h))

end SearchP

section K4Base

def k4_16_vars : List (BitVec 16) := [0xaaaa#16, 0xcccc#16, 0xf0f0#16, 0xff00#16]
def k4v16 (i : Fin 4) : BitVec 16 := k4_16_vars.getD i.val 0
def k4_tt16 : BitVec 16 := 0xfee8#16

def k4a : WP 30 := 0x2cb2cb2c0000fc0#60
def k4b : WP 30 := 0x55555554003f000#60
def k4c : WP 30 := 0x9a69a6980fc0000#60
def k4d : WP 30 := 0xe38e38e3f000000#60
def k4inputs : List (WP 30) := [k4a, k4b, k4c, k4d]

def k4Base60 : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8,
    3, 5, 6, 9, 10, 12, 3, 5, 6, 9, 10, 12, 3, 5, 6, 9, 10, 12, 3, 5, 6, 9, 10, 12, 3, 5, 6, 9, 10, 12]

def permBits4 (p0 p1 p2 p3 : ℕ) (y : ℕ) : Fin 16 :=
  let m := (if y.testBit 0 then 1 <<< p0 else 0) |||
           (if y.testBit 1 then 1 <<< p1 else 0) |||
           (if y.testBit 2 then 1 <<< p2 else 0) |||
           (if y.testBit 3 then 1 <<< p3 else 0)
  ⟨m % 16, Nat.mod_lt _ (by decide)⟩

def k4RowMap (i j : Fin 4) (k : Fin 60) : Fin 16 :=
  let rem := (List.finRange 4).filter (fun q => q != i && q != j)
  permBits4 i.val j.val (rem.getD 0 0).val (rem.getD 1 0).val (k4Base60[k.val]!)

def k4Proj (i j : Fin 4) : BitVec 16 → WP 30 := selectRows (k4RowMap i j)

def checkK4Proj : Bool :=
  (List.finRange 4).all fun i =>
    (List.finRange 4).all fun j =>
      if i == j then true else
        (k4Proj i j k4_tt16 == goalP 30) &&
        (k4Proj i j (k4v16 i) == k4a) &&
        (k4Proj i j (k4v16 j) == k4b) &&
        k4_16_vars.all fun w => k4inputs.any fun d => k4Proj i j w == d

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem k4Proj_ok : checkK4Proj = true := by decide +kernel

theorem k4_16_cover {w : BitVec 16} (hw : w ∈ k4_16_vars.toFinset) : ∃ i : Fin 4, k4v16 i = w := by
  rw [List.mem_toFinset] at hw
  simp only [k4_16_vars, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩

theorem k4_16_not_target : ∀ i : Fin 4, k4v16 i ≠ k4_tt16 ∧ k4v16 i ≠ ~~~k4_tt16 := by decide

theorem k4_nd0 : ((k4a &&& k4b) :: k4inputs).Nodup := by decide
theorem k4_nd1 : ((k4a ||| k4b) :: k4inputs).Nodup := by decide
theorem k4_nd2 : ((k4a &&& ~~~k4b) :: k4inputs).Nodup := by decide

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem k4_s0 : searchP 30 5 ((k4a &&& k4b) :: k4inputs) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem k4_s1 : searchP 30 5 ((k4a ||| k4b) :: k4inputs) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem k4_s2 : searchP 30 5 ((k4a &&& ~~~k4b) :: k4inputs) = false := by decide +kernel

theorem k4_step_aux (i j : Fin 4) (hij : i ≠ j) {t z : BitVec 16}
    (ht : t = k4_tt16 ∨ t = ~~~k4_tt16)
    (hz : z = k4v16 i &&& k4v16 j ∨ z = k4v16 i ||| k4v16 j ∨ z = k4v16 i &&& ~~~k4v16 j)
    (rest : Finset (BitVec 16)) (hsub : rest ⊆ k4_16_vars.toFinset)
    (tail : live basicOps t 5 (insert z rest)) : False := by
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp k4Proj_ok i (List.mem_finRange i)) j (List.mem_finRange j)
  have hne : (i == j) = false := beq_false_of_ne hij
  simp only [hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨⟨⟨hg, hi⟩, hj⟩, hall⟩ := h1
  let f := k4Proj i j
  have hi' : f (k4v16 i) = k4a := hi
  have hj' : f (k4v16 j) = k4b := hj
  have hAnd : ∀ u v, f (u &&& v) = f u &&& f v := selectRows_land (k4RowMap i j)
  have hOr : ∀ u v, f (u ||| v) = f u ||| f v := selectRows_lor (k4RowMap i j)
  have hNot : ∀ u, f (~~~u) = ~~~f u := selectRows_neg (k4RowMap i j)
  have hm := ops_map_of hAnd hOr hNot
  have hft : f t = goalP 30 ∨ f t = ~~~goalP 30 := by
    rcases ht with rfl | rfl
    · exact .inl hg
    · exact .inr ((hNot k4_tt16).trans (congrArg (fun u : WP 30 => ~~~u) hg))
  have hrest : ∀ u ∈ rest, holds k4inputs.toFinset (f u) := by
    intro u hu
    have hallu := List.all_eq_true.mp hall u (List.mem_toFinset.mp (hsub hu))
    obtain ⟨d, hd, heq⟩ := List.any_eq_true.mp hallu
    exact .inr (.inr ⟨d, List.mem_toFinset.mpr hd, .inl (beq_iff_eq.mp heq)⟩)
  have run_with (w0 : WP 30) (hfw : f z = w0) (hnd : (w0 :: k4inputs).Nodup)
      (hsch : searchP 30 5 (w0 :: k4inputs) = false) : False := by
    apply signed_rejectP (by decide) hnd hsch hft
    apply live_transport hm tail
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hr
    · exact .inr (.inr ⟨w0, List.mem_toFinset.mpr (List.mem_cons_self ..), .inl hfw⟩)
    · exact holds_mono (by intro x hx; exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp hx))) (hrest u hr)
  rcases hz with rfl | rfl | rfl
  · exact run_with (k4a &&& k4b) (by rw [hAnd, hi', hj']) k4_nd0 k4_s0
  · exact run_with (k4a ||| k4b) (by rw [hOr, hi', hj']) k4_nd1 k4_s1
  · exact run_with (k4a &&& ~~~k4b) (by rw [hAnd, hNot, hi', hj']) k4_nd2 k4_s2

theorem k4_no6_16 (t : BitVec 16) (ht : t = k4_tt16 ∨ t = ~~~k4_tt16)
    (hb : build basicOps t 6 k4_16_vars.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  rcases first_live (k := 5) hl with done | ⟨a, ha, b, hb', hab, z, hz, _, rest, he, tail⟩
  · have mt := hs (show t ∈ s by simp [done])
    obtain ⟨i, hi⟩ := k4_16_cover mt
    rcases ht with rfl | rfl
    · exact (k4_16_not_target i).1 hi
    · exact (k4_16_not_target i).2 hi
  · obtain ⟨i, rfl⟩ := k4_16_cover (hs ha)
    obtain ⟨j, rfl⟩ := k4_16_cover (hs hb')
    have hij : i ≠ j := fun e => hab (congrArg k4v16 e)
    have hsub : rest ⊆ k4_16_vars.toFinset := fun u hu =>
      hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact k4_step_aux i j hij ht (.inl rfl) rest hsub tail
    · exact k4_step_aux i j hij ht (.inr (.inl rfl)) rest hsub tail
    · exact k4_step_aux i j hij ht (.inr (.inr rfl)) rest hsub tail
    · exact k4_step_aux j i hij.symm ht (.inr (.inr rfl)) rest hsub tail

end K4Base

section Compile128

abbrev W128 := BitVec 128

def bit128 (k : Fin 128) (z : W128) : Bool := z[k.val]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem read_bit128 (w : List W128) (i : ℕ) (k : Fin 128) :
    (w.map (bit128 k)).getD i false = bit128 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit128]

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W128) (g : Gate) : W128 := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W128) (g : Gate) (hg : legal g) (k : Fin 128) :
    step (w.map (bit128 k)) g = (w ++ [action w g]).map (bit128 k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W128)[k.val] = false := by change (0#128)[k.val] = false; simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_bit128, List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit128, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def binaryCost (gs : List Gate) : ℕ := (gs.filter isBinary).length

theorem available_read {av : Finset W128} {w : List W128} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W128) (av : Finset W128) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
    action, List.head?_nil, List.head?_cons, List.map_nil, List.map_cons, List.foldr_nil, List.foldr_cons,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
    show ∀ x : W128, x ||| (0 : W128) = x from fun x => BitVec.or_zero,
    show ∀ x : W128, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (target : W128) (hnt0 : target ≠ 0) (hnt1 : target ≠ ~~~0)
    (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W128) (av : Finset W128) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit128 k))).getD out false = bit128 k target) :
    ∃ t, (t = target ∨ t = ~~~target) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = target := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit128, bit128] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim (hnt0 zero)
    · exact False.elim (hnt1 ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun u : W128 => ~~~u) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit128 k))).getD out false = bit128 k target := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W128) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, neg] using cont av hw stepClass
    · simp only [neg, ite_true] at stepClass
      have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, neg]
      rw [len]
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
      · obtain ⟨t, ht, run⟩ := cont av hw existing
        exact ⟨t, ht, Or.inl run⟩
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

end Compile128

theorem sb_not {n k : ℕ} {av : Finset (BitVec n)} {z : BitVec n}
    (h : SignedBuild k av z) : SignedBuild k av (~~~z) := by
  rcases h with rfl | rfl | h | h
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not] using h)))
  · exact .inr (.inr (.inl h))

theorem sb_supply {n k : ℕ} {src dst : Finset (BitVec n)} {z : BitVec n}
    (h : SignedBuild k src z) (supply : ∀ w ∈ src, holds dst w) :
    SignedBuild k dst z := by
  have hm : ∀ a b w : BitVec n, w ∈ basicOps a b →
      id w ∈ basicOps (id a) (id b) := fun _ _ _ h => h
  rcases h with h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · obtain ⟨s, hs, hl⟩ := compress h
    exact live_transport hm hl (fun w hw => supply w (hs hw))
  · obtain ⟨s, hs, hl⟩ := compress h
    have hh := live_transport hm hl (fun w hw => supply w (hs hw))
    simpa only [id_eq, BitVec.not_not] using sb_not hh

theorem sb_reachable_step {n k : ℕ} {av : Finset (BitVec n)} {z t : BitVec n}
    (hz : reachable av z) (h : SignedBuild k (insert z av) t) :
    SignedBuild (k + 1) av t := by
  rcases hz with old | ⟨a, ha, b, hb, ne, w, hw, rep⟩
  · apply sb_wait
    apply sb_supply h
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact old
    · exact .inr (.inr ⟨u, hu, .inl rfl⟩)
  · apply sb_step ha hb ne hw
    apply sb_supply h
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact rep
    · exact holds_insert (.inr (.inr ⟨u, hu, .inl rfl⟩))

theorem absorbing {n m : ℕ} (p : BitVec n) (f : Bool → BitVec n → BitVec m)
    (hAnd : ∀ c a b, f c (a &&& b) = f c a &&& f c b)
    (hOr : ∀ c a b, f c (a ||| b) = f c a ||| f c b)
    (hNot : ∀ c a, f c (~~~a) = ~~~f c a)
    (h0 : f false p = 0) (h1 : f true p = ~~~0) :
    ∀ a b z, z ∈ basicOps a b → a = p ∨ b = p →
      ∃ c, f c z = 0 ∨ f c z = ~~~0 := by
  intro a b z hz hp
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons,
    List.not_mem_nil, or_false] at hz
  rcases hp with rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨false, .inl (by rw [hAnd, h0, bv_zero_and])⟩
  · exact ⟨true, .inr (by rw [hOr, h1, bv_not_zero_or])⟩
  · exact ⟨false, .inl (by rw [hAnd, h0, bv_zero_and])⟩
  · exact ⟨true, .inl (by rw [hAnd, hNot, h1, BitVec.not_not, bv_and_zero])⟩
  · exact ⟨false, .inl (by rw [hAnd, h0, bv_and_zero])⟩
  · exact ⟨true, .inr (by rw [hOr, h1, bv_or_not_zero])⟩
  · exact ⟨true, .inl (by rw [hAnd, hNot, h1, BitVec.not_not, bv_and_zero])⟩
  · exact ⟨false, .inl (by rw [hAnd, h0, bv_zero_and])⟩

theorem double_cut {n m : ℕ} (p target : BitVec n)
    (f : Bool → BitVec n → BitVec m)
    (hm : ∀ c a b z, z ∈ basicOps a b → f c z ∈ basicOps (f c a) (f c b))
    (hnon : ∀ c, f c target ≠ 0 ∧ f c target ≠ ~~~0)
    (hcan : ∀ a b z, z ∈ basicOps a b → a = p ∨ b = p →
      ∃ c, f c z = 0 ∨ f c z = ~~~0)
    (hne : p ≠ target) :
    ∀ k (s : Finset (BitVec n)) (av : Bool → Finset (BitVec m)),
      live basicOps target k s → p ∈ s →
      (∀ c w, w ∈ s → holds (av c) (f c w)) →
      ∃ c, 2 ≤ k ∧ SignedBuild (k - 2) (av c) (f c target) := by
  intro k
  induction k with
  | zero =>
    intro s av run hp _
    change s = {target} at run
    exact (hne (Finset.mem_singleton.mp (run ▸ hp))).elim
  | succ k ih =>
    intro s av run hp hav
    rcases run with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, he, tail⟩
    · obtain ⟨c, cap, built⟩ := ih s av skip hp hav
      exact ⟨c, by omega, sb_le (by omega) built⟩
    · by_cases touch : a = p ∨ b = p
      · obtain ⟨c, hc⟩ := hcan a b z hz touch
        have holdTail : ∀ w ∈ insert z rest, holds (av c) (f c w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hc with hc | hc
            · exact .inl hc
            · exact .inr (.inl hc)
          · exact hav c w (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
        obtain ⟨cap, built⟩ := live_transport_save_const (hm c) tail
          (Finset.mem_insert_self z rest) hc (hnon c) holdTail
        refine ⟨c, by omega, ?_⟩
        convert built using 1 <;> omega
      · have hpRest : p ∈ rest := by
          rw [he] at hp
          rcases Finset.mem_insert.mp hp with e | hp
          · exact (touch (.inl e.symm)).elim
          rcases Finset.mem_insert.mp hp with e | hp
          · exact (touch (.inr e.symm)).elim
          exact hp
        let av' : Bool → Finset (BitVec m) := fun c => insert (f c z) (av c)
        have holdTail : ∀ c w, w ∈ insert z rest → holds (av' c) (f c w) := by
          intro c w hw
          rcases Finset.mem_insert.mp hw with hw | hw
          · exact .inr (.inr ⟨f c z, Finset.mem_insert_self _ _,
              .inl (congrArg (f c) hw)⟩)
          · exact holds_insert (hav c w
              (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)))
        obtain ⟨c, cap, built⟩ := ih (insert z rest) av' tail
          (Finset.mem_insert_of_mem hpRest) holdTail
        have hzReach : reachable (av c) (f c z) :=
          mem_ops_reach (hav c a ha) (hav c b hb) (hm c a b z hz)
        have result := sb_reachable_step hzReach built
        refine ⟨c, by omega, ?_⟩
        convert result using 1 <;> omega

theorem cut_signed {n m k : ℕ} (tgt : BitVec n) (tgt' : BitVec m)
    (ls : List (BitVec n)) (dst : List (BitVec m))
    (p : BitVec n) (a b : Fin n) (f : BitVec n → BitVec m)
    (hm : ∀ x y z, z ∈ basicOps x y → f z ∈ basicOps (f x) (f y))
    (hNot : ∀ z, f (~~~z) = ~~~f z)
    (hnc : tgt ≠ 0 ∧ tgt ≠ ~~~0) (hnc' : tgt' ≠ 0 ∧ tgt' ≠ ~~~0)
    (hd : bitDiff a b tgt)
    (hu : ∀ w ∈ ls, bitDiff a b w → w = p)
    (hp : f p = 0 ∨ f p = ~~~0) (ht : f tgt = tgt')
    (supply : ∀ w ∈ ls, holds dst.toFinset (f w))
    (built : SignedBuild k ls.toFinset tgt) :
    SignedBuild (k - 1) dst.toFinset tgt' := by
  obtain ⟨t, he, run⟩ := unwrap_sb hnc.1 hnc.2 built
  obtain ⟨s, hs, liveRun⟩ := compress run
  have hdiff : bitDiff a b t := by
    rcases he with rfl | rfl
    · exact hd
    · exact bitDiff_not hd
  have present := live_has_unique_sep hs liveRun a b hdiff hu
  have heq : f t = tgt' ∨ f t = ~~~tgt' := by
    rcases he with rfl | rfl
    · exact .inl ht
    · exact .inr (by rw [hNot, ht])
  have hnon : f t ≠ 0 ∧ f t ≠ ~~~0 := by
    rcases heq with h | h <;> rw [h]
    · exact hnc'
    · exact not_const_of_neg hnc'
  obtain ⟨_, result⟩ := live_transport_save_const hm liveRun present hp hnon
    (fun w hw => supply w (List.mem_toFinset.mp (hs hw)))
  rcases heq with h | h
  · rwa [h] at result
  · rw [h] at result
    simpa only [BitVec.not_not] using sb_not result

def v0 : W128 := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa#128
def v1 : W128 := 0xcccccccccccccccccccccccccccccccc#128
def v2 : W128 := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0#128
def v3 : W128 := 0xff00ff00ff00ff00ff00ff00ff00ff00#128
def v4 : W128 := 0xffff0000ffff0000ffff0000ffff0000#128
def v5 : W128 := 0xffffffff00000000ffffffff00000000#128
def v6 : W128 := 0xffffffffffffffff0000000000000000#128

def roots7 : List W128 := [v0, v1, v2, v3, v4, v5, v6]
def roots6 : List W128 := [v0, v1, v2, v3, v5, v6]
def roots5 (b : Bool) : List W128 :=
  if b then [v1, v2, v3, v5, v6] else [v0, v2, v3, v5, v6]
def roots4 (b : Bool) : List W128 :=
  if b then [v1, v3, v5, v6] else [v0, v3, v5, v6]

def target7 : W128 :=
  (v0 &&& v3) ||| (v1 &&& v3) ||| (v0 &&& v4) ||| (v2 &&& v4) |||
  (v0 &&& v5) ||| (v1 &&& v5) ||| (v3 &&& v5) ||| (v0 &&& v6) |||
  (v1 &&& v6) ||| (v2 &&& v6) ||| (v3 &&& v6) ||| (v5 &&& v6)

def fixBit (i : Fin 7) (val : Bool) (k : Fin 128) : Fin 128 :=
  let bit := 1 <<< i.val
  let m := if val then k.val ||| bit else k.val &&& (127 - bit)
  ⟨m % 128, Nat.mod_lt _ (by decide)⟩

def restrict (i : Fin 7) (val : Bool) : W128 → W128 := selectRows (fixBit i val)
def removeFirst (b : Bool) : Fin 7 := if b then 0 else 1
def firstVar (b : Bool) : W128 := if b then v0 else v1
def target6 (b : Bool) : W128 := restrict 4 b target7
def target5 (b : Bool) : W128 := restrict (removeFirst b) false (target6 b)
def target4 (b : Bool) : W128 := restrict 2 false (target5 b)
def sep6a (b : Bool) : Fin 128 := if b then 0 else 8
def sep6b (b : Bool) : Fin 128 := if b then 1 else 10
def sep5a (b : Bool) : Fin 128 := if b then 0 else 64
def sep5b (b : Bool) : Fin 128 := if b then 4 else 68

def coreRows (b : Bool) : Array ℕ :=
  if b then #[0, 2, 8, 10, 32, 34, 40, 42, 64, 66, 72, 74, 96, 98, 104, 106]
  else #[0, 1, 8, 9, 32, 33, 40, 41, 64, 65, 72, 73, 96, 97, 104, 105]
def coreMap (b : Bool) (k : Fin 16) : Fin 128 :=
  ⟨(coreRows b)[k.val]! % 128, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem nonconstants :
    (target7 ≠ 0 ∧ target7 ≠ ~~~0) ∧
    ∀ b, (target6 b ≠ 0 ∧ target6 b ≠ ~~~0) ∧
      (target5 b ≠ 0 ∧ target5 b ≠ ~~~0) ∧
      (target4 b ≠ 0 ∧ target4 b ≠ ~~~0) := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem core_projection : ∀ b, selectRows (coreMap b) (target4 b) = k4_tt16 := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem core_supply (b : Bool) : ∀ w ∈ roots4 b,
    holds k4_16_vars.toFinset (selectRows (coreMap b) w) := by
  apply map_holds_list
  cases b <;> decide +kernel

theorem core_no6 (b : Bool) (built : SignedBuild 6 (roots4 b).toFinset (target4 b)) : False := by
  have hnc := (nonconstants.2 b).2.2
  obtain ⟨t, ht, run⟩ := unwrap_sb hnc.1 hnc.2 built
  obtain ⟨s, hs, hl⟩ := compress run
  have hm := ops_map_of (selectRows_land (coreMap b))
    (selectRows_lor (coreMap b)) (selectRows_neg (coreMap b))
  have mapped := live_transport hm hl (fun w hw =>
    core_supply b w (List.mem_toFinset.mp (hs hw)))
  have heq : selectRows (coreMap b) t = k4_tt16 ∨
      selectRows (coreMap b) t = ~~~k4_tt16 := by
    rcases ht with rfl | rfl
    · exact .inl (core_projection b)
    · exact .inr (by rw [selectRows_neg, core_projection])
  have hcore : k4_tt16 ≠ 0 ∧ k4_tt16 ≠ ~~~0 := by decide
  have hnon : selectRows (coreMap b) t ≠ 0 ∧ selectRows (coreMap b) t ≠ ~~~0 := by
    rcases heq with h | h <;> rw [h]
    · exact hcore
    · exact not_const_of_neg hcore
  obtain ⟨z, hz, hrun⟩ := unwrap_sb hnon.1 hnon.2 mapped
  have hz' : z = k4_tt16 ∨ z = ~~~k4_tt16 := by
    rcases heq with h | h <;> rcases hz with rfl | rfl <;> rw [h]
    · exact .inl rfl
    · exact .inr rfl
    · exact .inr rfl
    · exact .inl BitVec.not_not
  exact k4_no6_16 z hz' hrun

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem cofactor_no8 (b : Bool)
    (built : SignedBuild 8 roots6.toFinset (target6 b)) : False := by
  have h6 := (nonconstants.2 b).1
  have h5 := (nonconstants.2 b).2.1
  have h4 := (nonconstants.2 b).2.2
  have first : SignedBuild 7 (roots5 b).toFinset (target5 b) :=
    cut_signed (target6 b) (target5 b) roots6 (roots5 b) (firstVar b)
      (sep6a b) (sep6b b) (restrict (removeFirst b) false)
      (ops_map_of (selectRows_land (fixBit (removeFirst b) false))
        (selectRows_lor (fixBit (removeFirst b) false))
        (selectRows_neg (fixBit (removeFirst b) false)))
      (selectRows_neg (fixBit (removeFirst b) false)) h6 h5
      (by cases b <;> unfold bitDiff <;> decide +kernel)
      (sep_of_all _ _ _ _ (by cases b <;> decide +kernel))
      (.inl (by cases b <;> decide +kernel)) rfl
      (map_holds_list _ _ _ (by cases b <;> decide +kernel)) built
  have second : SignedBuild 6 (roots4 b).toFinset (target4 b) :=
    cut_signed (target5 b) (target4 b) (roots5 b) (roots4 b) v2
      (sep5a b) (sep5b b) (restrict 2 false)
      (ops_map_of (selectRows_land (fixBit 2 false))
        (selectRows_lor (fixBit 2 false)) (selectRows_neg (fixBit 2 false)))
      (selectRows_neg (fixBit 2 false)) h5 h4
      (by cases b <;> unfold bitDiff <;> decide +kernel)
      (sep_of_all _ _ _ _ (by cases b <;> decide +kernel))
      (.inl (by decide +kernel)) rfl
      (map_holds_list _ _ _ (by cases b <;> decide +kernel)) first
  exact core_no6 b second

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem no_ten (t : W128) (ht : t = target7 ∨ t = ~~~target7)
    (built : build basicOps t 10 roots7.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress built
  have sep : bitDiff (1 : Fin 128) (17 : Fin 128) target7 := by
    unfold bitDiff
    decide +kernel
  have hd : bitDiff (1 : Fin 128) (17 : Fin 128) t := by
    rcases ht with rfl | rfl
    · exact sep
    · exact bitDiff_not sep
  have present : v4 ∈ s := live_has_unique_sep hs hl 1 17 hd
    (sep_of_all 1 17 roots7 v4 (by decide +kernel))
  have hm := fun c => ops_map_of (selectRows_land (fixBit 4 c))
    (selectRows_lor (fixBit 4 c)) (selectRows_neg (fixBit 4 c))
  have hn : ∀ c, restrict 4 c t ≠ 0 ∧ restrict 4 c t ≠ ~~~0 := by
    intro c
    rcases ht with rfl | rfl
    · exact (nonconstants.2 c).1
    · rw [restrict, selectRows_neg]
      exact not_const_of_neg (nonconstants.2 c).1
  have can := absorbing v4 (restrict 4)
    (fun c => selectRows_land (fixBit 4 c))
    (fun c => selectRows_lor (fixBit 4 c))
    (fun c => selectRows_neg (fixBit 4 c))
    (by decide +kernel) (by decide +kernel)
  have ne : v4 ≠ t := by rcases ht with rfl | rfl <;> decide +kernel
  have supply : ∀ c w, w ∈ s → holds roots6.toFinset (restrict 4 c w) := by
    intro c w hw
    exact map_holds_list (restrict 4 c) roots7 roots6
      (by cases c <;> decide +kernel) w (List.mem_toFinset.mp (hs hw))
  obtain ⟨c, _, result⟩ := double_cut v4 t (restrict 4) hm hn can ne
    10 s (fun _ => roots6.toFinset) hl present supply
  have result' : SignedBuild 8 roots6.toFinset (target6 c) := by
    rcases ht with rfl | rfl
    · exact result
    · change SignedBuild 8 roots6.toFinset (selectRows (fixBit 4 c) (~~~target7)) at result
      rw [selectRows_neg] at result
      simpa only [target6, restrict, BitVec.not_not] using sb_not result
  exact cofactor_no8 c result'

def edges : List ℕ := [0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6]
def edgeValue (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < edges.length / 2,
    (List.ofFn x).getD (edges.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edges.getD (2 * i + 1) 0) false = true)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem sample7 : ∀ k : Fin 128,
    edgeValue (fun i => (roots7.getD i.val 0)[k.val]) = target7[k.val] := by
  decide +kernel

theorem cost_bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = edgeValue x) :
    10 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ roots7, holds roots7.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 128) :
      (gs.foldl step (roots7.map (bit128 k))).getD o false = bit128 k target7 := by
    let x (i : Fin 7) : Bool := bit128 k (roots7.getD i.val 0)
    have width : roots7.length = 7 := rfl
    have same : List.ofFn x = roots7.map (bit128 k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < roots7.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (roots7.map (bit128 k)) = bit128 k target7
    rw [← same, he]
    exact sample7 k
  obtain ⟨t, ht, run⟩ := compile target7 nonconstants.1.1 nonconstants.1.2
    gs o hg roots7 roots7.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a roots7.toFinset) :
      build basicOps t b roots7.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact no_ten t ht (lift low run)

def rcStep (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) : List Gate × List (Bool ⊕ ℕ) :=
  let out := st.1
  let env := st.2
  match g.op with
  | GateOp.not =>
    match g.inputs with
    | [] => (out, env ++ [Sum.inl true])
    | i :: _ =>
      match env.getD i (Sum.inl false) with
      | Sum.inl b => (out, env ++ [Sum.inl (!b)])
      | Sum.inr w' => (out ++ [{ op := GateOp.not, inputs := [w'] }], env ++ [Sum.inr (nOut + out.length)])
  | GateOp.and =>
    if g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl false => true | _ => false) then
      (out, env ++ [Sum.inl false])
    else
      let ws' := g.inputs.filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
      match ws' with
      | [] => (out, env ++ [Sum.inl true])
      | [w'] => (out, env ++ [Sum.inr w'])
      | _ => (out ++ [{ op := GateOp.and, inputs := ws' }], env ++ [Sum.inr (nOut + out.length)])
  | GateOp.or =>
    if g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl true => true | _ => false) then
      (out, env ++ [Sum.inl true])
    else
      let ws' := g.inputs.filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
      match ws' with
      | [] => (out, env ++ [Sum.inl false])
      | [w'] => (out, env ++ [Sum.inr w'])
      | _ => (out ++ [{ op := GateOp.or, inputs := ws' }], env ++ [Sum.inr (nOut + out.length)])
  | _ => (out, env ++ [Sum.inl false])

def rcCircuit (nOut : ℕ) (env0 : List (Bool ⊕ ℕ)) (gs : List Gate) (o : ℕ) : List Gate × ℕ :=
  let res := gs.foldl (rcStep nOut) ([], env0)
  match res.2.getD o (Sum.inl false) with
  | Sum.inr w' => (res.1, w')
  | Sum.inl false => (res.1, nOut + res.1.length)
  | Sum.inl true => (res.1 ++ [{ op := GateOp.not, inputs := [] }], nOut + res.1.length)

lemma list_filterMap_len_le {α β : Type} (f : α → Option β) (l : List α) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t ih => cases h : f a <;> simp [h] <;> omega

lemma list_filterMap_len_lt {α β : Type} (f : α → Option β) (l : List α)
    (x : α) (hx : x ∈ l) (hnone : f x = none) :
    (l.filterMap f).length < l.length := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxt
    · simp only [List.filterMap_cons, hnone, List.length_cons]
      have := list_filterMap_len_le f t; omega
    · have hlt := ih hxt
      cases h : f a with
      | none => simp only [List.filterMap_cons, h, List.length_cons]; omega
      | some b => simp only [List.filterMap_cons, h, List.length_cons]; omega

lemma wfold_len (gs : List Gate) (xs : List Bool) :
    (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, List.length_cons, ih, step, List.length_append, List.length_nil]; omega

lemma rcStep_env_len (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
    (rcStep nOut st g).2.length = st.2.length + 1 := by
  rcases st with ⟨out, env⟩
  cases h : g.op
  · simp only [rcStep, h]; split_ifs
    · simp
    · cases g.inputs.filterMap _ with
      | nil => simp
      | cons a t => cases t <;> simp
  · simp only [rcStep, h]; split_ifs
    · simp
    · cases g.inputs.filterMap _ with
      | nil => simp
      | cons a t => cases t <;> simp
  · simp only [rcStep, h]
    cases g.inputs with
    | nil => simp
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) <;> simp
  · simp [rcStep, h]
  · simp [rcStep, h]

lemma rcStep_legal (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (h1 : ∀ g' ∈ st.1, legal g') (hg : legal g) :
    ∀ g' ∈ (rcStep nOut st g).1, legal g' := by
  rcases st with ⟨out, env⟩
  dsimp only at h1 ⊢
  obtain ⟨hop, hlen⟩ := hg
  change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at hop
  rcases hop with hop | hop | hop
  · simp only [rcStep, hop]
    split_ifs
    · exact h1
    · cases hins : g.inputs.filterMap _ with
      | nil => exact h1
      | cons a t =>
        cases t with
        | nil => exact h1
        | cons b t2 =>
          intro g' hg'
          simp only [List.mem_append, List.mem_singleton] at hg'
          rcases hg' with h | rfl
          · exact h1 g' h
          · have hl := list_filterMap_len_le (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) g.inputs
            rw [hins] at hl
            exact ⟨by simp, hl.trans hlen⟩
  · simp only [rcStep, hop]
    split_ifs
    · exact h1
    · cases hins : g.inputs.filterMap _ with
      | nil => exact h1
      | cons a t =>
        cases t with
        | nil => exact h1
        | cons b t2 =>
          intro g' hg'
          simp only [List.mem_append, List.mem_singleton] at hg'
          rcases hg' with h | rfl
          · exact h1 g' h
          · have hl := list_filterMap_len_le (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) g.inputs
            rw [hins] at hl
            exact ⟨by simp, hl.trans hlen⟩
  · simp only [rcStep, hop]
    cases g.inputs with
    | nil => exact h1
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) with
      | inl b => exact h1
      | inr w' =>
        intro g' hg'
        simp only [List.mem_append, List.mem_singleton] at hg'
        rcases hg' with h | rfl
        · exact h1 g' h
        · exact ⟨by simp, by simp⟩

lemma rcFold_legal (nOut : ℕ) (gs : List Gate) (st : List Gate × List (Bool ⊕ ℕ))
    (h1 : ∀ g' ∈ st.1, legal g') (hM : ∀ g ∈ gs, legal g) :
    ∀ g' ∈ (gs.foldl (rcStep nOut) st).1, legal g' := by
  induction gs generalizing st with
  | nil => exact h1
  | cons g rest ih =>
    simp only [List.foldl_cons]
    exact ih (rcStep nOut st g) (rcStep_legal nOut st g h1 (hM g List.mem_cons_self))
      (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg'))

lemma binaryCost_append_one (gs : List Gate) (g : Gate) :
    binaryCost (gs ++ [g]) = binaryCost gs + (if isBinary g then 1 else 0) := by
  unfold binaryCost
  rw [List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
  cases isBinary g <;> simp

lemma rcStep_binCost_le (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
    binaryCost (rcStep nOut st g).1 ≤ binaryCost st.1 + (if isBinary g then 1 else 0) := by
  rcases st with ⟨out, env⟩
  dsimp only
  cases h : g.op
  · simp only [rcStep, h, isBinary, ite_true]
    split_ifs
    · dsimp only; omega
    · cases g.inputs.filterMap _ with
      | nil => dsimp only; omega
      | cons a t =>
        cases t with
        | nil => dsimp only; omega
        | cons b t2 => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp only [rcStep, h, isBinary, ite_true]
    split_ifs
    · dsimp only; omega
    · cases g.inputs.filterMap _ with
      | nil => dsimp only; omega
      | cons a t =>
        cases t with
        | nil => dsimp only; omega
        | cons b t2 => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp only [rcStep, h, isBinary, Bool.false_eq_true, ite_false, Nat.add_zero]
    cases g.inputs with
    | nil => dsimp only; exact le_refl _
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) with
      | inl b => dsimp only; exact le_refl _
      | inr w' => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp [rcStep, h, isBinary]
  · simp [rcStep, h, isBinary]

lemma rcFold_binCost_le (nOut : ℕ) (gs : List Gate) (st : List Gate × List (Bool ⊕ ℕ)) :
    binaryCost (gs.foldl (rcStep nOut) st).1 ≤ binaryCost st.1 + binaryCost gs := by
  induction gs generalizing st with
  | nil => simp [binaryCost]
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have h1 := ih (rcStep nOut st g)
    have h2 := rcStep_binCost_le nOut st g
    have h3 : binaryCost (g :: rest) = binaryCost rest + (if isBinary g then 1 else 0) := by
      unfold binaryCost; rw [List.filter_cons]; cases isBinary g <;> simp
    omega

lemma rcFold_eval_inv (nOut : ℕ) (gs : List Gate) (ys : List Bool) (hyl : ys.length = nOut)
    (hM : ∀ g ∈ gs, legal g) (ws : List Bool) (st : List Gate × List (Bool ⊕ ℕ))
    (hlen_ws : ws.length = st.2.length)
    (hinv : ∀ i, match st.2.getD i (Sum.inl false) with
      | Sum.inl b => ws.getD i false = b
      | Sum.inr w' => w' < nOut + st.1.length ∧ ws.getD i false = (st.1.foldl step ys).getD w' false) :
    let ws' := gs.foldl step ws
    let st' := gs.foldl (rcStep nOut) st
    ws'.length = st'.2.length ∧
    ∀ i, match st'.2.getD i (Sum.inl false) with
      | Sum.inl b => ws'.getD i false = b
      | Sum.inr w' => w' < nOut + st'.1.length ∧ ws'.getD i false = (st'.1.foldl step ys).getD w' false := by
  induction gs generalizing ws st with
  | nil => exact ⟨hlen_ws, hinv⟩
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hg := hM g List.mem_cons_self
    rcases st with ⟨out, env⟩
    dsimp only at hlen_ws hinv
    have hws'_len : (step ws g).length = env.length + 1 := by simp [step, hlen_ws]
    have hget_old : ∀ i < env.length, (step ws g).getD i false = ws.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < ws.length)]
    have hget_last : (step ws g).getD env.length false = g.op.eval (g.inputs.map fun i => ws.getD i false) := by
      rw [← hlen_ws, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hget_hi : ∀ i, env.length + 1 ≤ i → (step ws g).getD i false = false := fun i hi =>
      List.getD_eq_default _ _ (by omega)
    have hstep_inv :
        (step ws g).length = (rcStep nOut (out, env) g).2.length ∧
        ∀ i, match (rcStep nOut (out, env) g).2.getD i (Sum.inl false) with
          | Sum.inl b => (step ws g).getD i false = b
          | Sum.inr w' => w' < nOut + (rcStep nOut (out, env) g).1.length ∧
              (step ws g).getD i false = ((rcStep nOut (out, env) g).1.foldl step ys).getD w' false := by
      constructor
      · rw [rcStep_env_len]; exact hws'_len
      · have hfold_app : ∀ (gnew : Gate),
            ((out ++ [gnew]).foldl step ys) = step (out.foldl step ys) gnew := fun gnew => by
          rw [List.foldl_append]; rfl
        have hkeep_old : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : i < env.length),
            match (env ++ [x]).getD i (Sum.inl false) with
            | Sum.inl b => (step ws g).getD i false = b
            | Sum.inr w' => w' < nOut + out.length ∧ (step ws g).getD i false = (out.foldl step ys).getD w' false := by
          intro x i hi
          have h1 : (env ++ [x]).getD i (Sum.inl false) = env.getD i (Sum.inl false) := by
            rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
            simp [List.getElem_append_left hi]
          rw [h1, hget_old i hi]; exact hinv i
        have hkeep_old_app : ∀ (x : Bool ⊕ ℕ) (gnew : Gate) (i : ℕ) (hi : i < env.length),
            match (env ++ [x]).getD i (Sum.inl false) with
            | Sum.inl b => (step ws g).getD i false = b
            | Sum.inr w' => w' < nOut + (out ++ [gnew]).length ∧
                (step ws g).getD i false = ((out ++ [gnew]).foldl step ys).getD w' false := by
          intro x gnew i hi
          have hk := hkeep_old x i hi
          cases hm : (env ++ [x]).getD i (Sum.inl false) with
          | inl b => rw [hm] at hk; exact hk
          | inr w' =>
            rw [hm] at hk; dsimp only at hk
            have hw' : w' < nOut + out.length := hk.1
            refine ⟨by simp; omega, ?_⟩
            rw [hk.2, hfold_app gnew]
            have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
            have hlen_w : (step (out.foldl step ys) gnew).length = nOut + out.length + 1 := by simp [step, hlen_out]
            rw [List.getD_eq_getElem _ _ (by omega : w' < (out.foldl step ys).length),
                List.getD_eq_getElem _ _ (by omega : w' < (step (out.foldl step ys) gnew).length)]
            simp [step, List.getElem_append_left (by omega : w' < (out.foldl step ys).length)]
        have hkeep_hi : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : env.length + 1 ≤ i),
            (env ++ [x]).getD i (Sum.inl false) = Sum.inl false := fun x i hi =>
          List.getD_eq_default _ _ (by simp; omega)
        have hget_env_last : ∀ (x : Bool ⊕ ℕ), (env ++ [x]).getD env.length (Sum.inl false) = x := fun x => by
          rw [List.getD_eq_getElem _ _ (by simp)]; simp
        have hmem_bound : ∀ w' ∈ g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none),
            w' < nOut + out.length := by
          intro w' hw'
          obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hw'
          have hij := hinv j
          cases hm : env.getD j (Sum.inl false) with
          | inl b => rw [hm] at hj; cases hj
          | inr w0 =>
            rw [hm] at hj hij; dsimp only at hij
            cases hj; exact hij.1
        have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg.1
        rcases hop with hop | hop | hop
        ·
          simp only [rcStep, hop]
          split_ifs with hany
          · intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl false) i hi
            · by_cases heq : i = env.length
              · subst heq
                rw [hget_env_last (Sum.inl false), hget_last, hop]
                simp only [GateOp.eval, List.all_eq_false, id_eq]
                rw [List.any_eq_true] at hany
                obtain ⟨j, hj, hjf⟩ := hany
                have hj' := hinv j
                cases hm : env.getD j (Sum.inl false) with
                | inl b =>
                  rw [hm] at hjf hj'; dsimp only at hj'
                  cases b with
                  | false => exact ⟨ws.getD j false, List.mem_map.mpr ⟨j, hj, rfl⟩, by rw [hj']; decide⟩
                  | true => simp at hjf
                | inr w' => rw [hm] at hjf; simp at hjf
              · rw [hkeep_hi (Sum.inl false) i (by omega)]; exact hget_hi i (by omega)
          · have hand_eq : (g.inputs.map fun j => ws.getD j false).all id =
                ((g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                  fun w' => (out.foldl step ys).getD w' false).all id := by
              have hnof : ∀ j ∈ g.inputs, env.getD j (Sum.inl false) ≠ Sum.inl false := by
                intro j hj heqf
                apply hany; rw [List.any_eq_true]; exact ⟨j, hj, by rw [heqf]⟩
              have hlist : ∀ l : List ℕ, (∀ j ∈ l, env.getD j (Sum.inl false) ≠ Sum.inl false) →
                  (l.map fun j => ws.getD j false).all id =
                  ((l.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                    fun w' => (out.foldl step ys).getD w' false).all id := by
                intro l
                induction l with
                | nil => intro _; rfl
                | cons a t iht =>
                  intro hnf
                  have ha := hnf a List.mem_cons_self
                  have hia := hinv a
                  have ht := iht (fun j hj => hnf j (List.mem_cons_of_mem _ hj))
                  cases hm : env.getD a (Sum.inl false) with
                  | inl b =>
                    cases b with
                    | false => exact absurd hm ha
                    | true =>
                      rw [hm] at hia; dsimp only at hia
                      simp only [List.filterMap_cons, hm, List.map_cons, List.all_cons, id_eq, hia, Bool.true_and, ht]
                  | inr w' =>
                    rw [hm] at hia; dsimp only at hia
                    simp only [List.filterMap_cons, hm, List.map_cons, List.all_cons, id_eq, hia.2, ht]
              exact hlist g.inputs hnof
            cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil =>
              rw [hins] at hand_eq
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl true) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl true), hget_last, hop]; simpa [GateOp.eval] using hand_eq
                · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
            | cons a t =>
              cases t with
              | nil =>
                rw [hins] at hand_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old (Sum.inr a) i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr a)]
                    refine ⟨hmem_bound a (by rw [hins]; simp), ?_⟩
                    rw [hget_last, hop]; simpa [GateOp.eval] using hand_eq
                  · rw [hkeep_hi (Sum.inr a) i (by omega)]; exact hget_hi i (by omega)
              | cons b t2 =>
                rw [hins] at hand_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr (nOut + out.length))]
                    refine ⟨by simp, ?_⟩
                    rw [hget_last, hop, hfold_app]
                    have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                    rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                    simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                    simpa [GateOp.eval] using hand_eq
                  · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
        ·
          simp only [rcStep, hop]
          split_ifs with hany
          · intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl true) i hi
            · by_cases heq : i = env.length
              · subst heq
                rw [hget_env_last (Sum.inl true), hget_last, hop]
                simp only [GateOp.eval, List.any_eq_true, id_eq]
                rw [List.any_eq_true] at hany
                obtain ⟨j, hj, hjt⟩ := hany
                have hj' := hinv j
                cases hm : env.getD j (Sum.inl false) with
                | inl b =>
                  rw [hm] at hjt hj'; dsimp only at hj'
                  cases b with
                  | true => exact ⟨ws.getD j false, List.mem_map.mpr ⟨j, hj, rfl⟩, hj'⟩
                  | false => simp at hjt
                | inr w' => rw [hm] at hjt; simp at hjt
              · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
          · have hor_eq : (g.inputs.map fun j => ws.getD j false).any id =
                ((g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                  fun w' => (out.foldl step ys).getD w' false).any id := by
              have hnot : ∀ j ∈ g.inputs, env.getD j (Sum.inl false) ≠ Sum.inl true := by
                intro j hj heqt
                apply hany; rw [List.any_eq_true]; exact ⟨j, hj, by rw [heqt]⟩
              have hlist : ∀ l : List ℕ, (∀ j ∈ l, env.getD j (Sum.inl false) ≠ Sum.inl true) →
                  (l.map fun j => ws.getD j false).any id =
                  ((l.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                    fun w' => (out.foldl step ys).getD w' false).any id := by
                intro l
                induction l with
                | nil => intro _; rfl
                | cons a t iht =>
                  intro hnt
                  have ha := hnt a List.mem_cons_self
                  have hia := hinv a
                  have ht := iht (fun j hj => hnt j (List.mem_cons_of_mem _ hj))
                  cases hm : env.getD a (Sum.inl false) with
                  | inl b =>
                    cases b with
                    | true => exact absurd hm ha
                    | false =>
                      rw [hm] at hia; dsimp only at hia
                      simp only [List.filterMap_cons, hm, List.map_cons, List.any_cons, id_eq, hia, Bool.false_or, ht]
                  | inr w' =>
                    rw [hm] at hia; dsimp only at hia
                    simp only [List.filterMap_cons, hm, List.map_cons, List.any_cons, id_eq, hia.2, ht]
              exact hlist g.inputs hnot
            cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil =>
              rw [hins] at hor_eq
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl false) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl false), hget_last, hop]; simpa [GateOp.eval] using hor_eq
                · rw [hkeep_hi (Sum.inl false) i (by omega)]; exact hget_hi i (by omega)
            | cons a t =>
              cases t with
              | nil =>
                rw [hins] at hor_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old (Sum.inr a) i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr a)]
                    refine ⟨hmem_bound a (by rw [hins]; simp), ?_⟩
                    rw [hget_last, hop]; simpa [GateOp.eval] using hor_eq
                  · rw [hkeep_hi (Sum.inr a) i (by omega)]; exact hget_hi i (by omega)
              | cons b t2 =>
                rw [hins] at hor_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr (nOut + out.length))]
                    refine ⟨by simp, ?_⟩
                    rw [hget_last, hop, hfold_app]
                    have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                    rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                    simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                    simpa [GateOp.eval] using hor_eq
                  · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
        ·
          simp only [rcStep, hop]
          cases hgi : g.inputs with
          | nil =>
            intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl true) i hi
            · by_cases heq : i = env.length
              · subst heq; rw [hget_env_last (Sum.inl true), hget_last, hop, hgi]; rfl
              · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
          | cons j rest_i =>
            dsimp only
            cases hm : env.getD j (Sum.inl false) with
            | inl b =>
              dsimp only
              have hj' := hinv j; rw [hm] at hj'; dsimp only at hj'
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl (!b)) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl (!b)), hget_last, hop, hgi]; simpa [GateOp.eval] using hj'
                · rw [hkeep_hi (Sum.inl (!b)) i (by omega)]; exact hget_hi i (by omega)
            | inr w' =>
              dsimp only
              have hj' := hinv j; rw [hm] at hj'; dsimp only at hj'
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
              · by_cases heq : i = env.length
                · subst heq
                  rw [hget_env_last (Sum.inr (nOut + out.length))]
                  refine ⟨by simp, ?_⟩
                  rw [hget_last, hop, hgi, hfold_app]
                  have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                  rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                  simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                  simpa [GateOp.eval] using hj'.2
                · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
    exact ih (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')) (step ws g) (rcStep nOut (out, env) g)
      hstep_inv.1 hstep_inv.2

lemma rcFold_inr_agree (nOut : ℕ) (gs : List Gate) (hM : ∀ g ∈ gs, legal g)
    (wx wy : List Bool) (st : List Gate × List (Bool ⊕ ℕ))
    (hxlen : wx.length = st.2.length) (hylen : wy.length = st.2.length)
    (heq_cost : binaryCost (gs.foldl (rcStep nOut) st).1 = binaryCost st.1 + binaryCost gs)
    (hagree : ∀ i w', st.2.getD i (Sum.inl false) = Sum.inr w' → wx.getD i false = wy.getD i false) :
    ∀ i w', (gs.foldl (rcStep nOut) st).2.getD i (Sum.inl false) = Sum.inr w' →
      (gs.foldl step wx).getD i false = (gs.foldl step wy).getD i false := by
  induction gs generalizing wx wy st with
  | nil => exact hagree
  | cons g rest ih =>
    simp only [List.foldl_cons] at heq_cost ⊢
    have hg := hM g List.mem_cons_self
    have h1 := rcFold_binCost_le nOut rest (rcStep nOut st g)
    have h2 := rcStep_binCost_le nOut st g
    have h3 : binaryCost (g :: rest) = binaryCost rest + (if isBinary g then 1 else 0) := by
      unfold binaryCost; rw [List.filter_cons]; cases isBinary g <;> simp
    have hstep_cost : binaryCost (rcStep nOut st g).1 = binaryCost st.1 + (if isBinary g then 1 else 0) := by omega
    have hrest_cost : binaryCost (rest.foldl (rcStep nOut) (rcStep nOut st g)).1 =
        binaryCost (rcStep nOut st g).1 + binaryCost rest := by omega
    rcases st with ⟨out, env⟩
    dsimp only at hxlen hylen hagree hstep_cost
    refine ih (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')) (step wx g) (step wy g)
      (rcStep nOut (out, env) g) (by rw [rcStep_env_len]; simp [step, hxlen])
      (by rw [rcStep_env_len]; simp [step, hylen]) hrest_cost ?_
    have hget_old_x : ∀ i < env.length, (step wx g).getD i false = wx.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wx.length)]
    have hget_old_y : ∀ i < env.length, (step wy g).getD i false = wy.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wy.length)]
    have hget_last_x : (step wx g).getD env.length false = g.op.eval (g.inputs.map fun j => wx.getD j false) := by
      rw [← hxlen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hget_last_y : (step wy g).getD env.length false = g.op.eval (g.inputs.map fun j => wy.getD j false) := by
      rw [← hylen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hall_inr_of_len2 :
        (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 →
        ∀ j ∈ g.inputs, ∃ w0, env.getD j (Sum.inl false) = Sum.inr w0 := by
      intro hl2 j hj
      cases hm : env.getD j (Sum.inl false) with
      | inr w0 => exact ⟨w0, rfl⟩
      | inl b =>
        exfalso
        have hlt := list_filterMap_len_lt (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
          g.inputs j hj (by rw [hm])
        have hcap := hg.2
        omega
    have hstep_env_old : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : i < env.length),
        (env ++ [x]).getD i (Sum.inl false) = env.getD i (Sum.inl false) := fun x i hi => by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
      simp [List.getElem_append_left hi]
    have hstep_env_hi : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : env.length + 1 ≤ i),
        (env ++ [x]).getD i (Sum.inl false) = Sum.inl false := fun x i hi =>
      List.getD_eq_default _ _ (by simp; omega)
    have hstep_env_last : ∀ (x : Bool ⊕ ℕ), (env ++ [x]).getD env.length (Sum.inl false) = x := fun x => by
      rw [List.getD_eq_getElem _ _ (by simp)]; simp
    intro i w' hiw'
    by_cases hi : i < env.length
    · have h1 : (rcStep nOut (out, env) g).2.getD i (Sum.inl false) = env.getD i (Sum.inl false) := by
        cases h : g.op
        · simp only [rcStep, h]; split_ifs
          · exact hstep_env_old _ i hi
          · cases g.inputs.filterMap _ with | nil => exact hstep_env_old _ i hi | cons a t => cases t <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; split_ifs
          · exact hstep_env_old _ i hi
          · cases g.inputs.filterMap _ with | nil => exact hstep_env_old _ i hi | cons a t => cases t <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; cases g.inputs with
          | nil => exact hstep_env_old _ i hi
          | cons j _ => dsimp only; cases env.getD j (Sum.inl false) <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; exact hstep_env_old _ i hi
        · simp only [rcStep, h]; exact hstep_env_old _ i hi
      rw [h1] at hiw'
      rw [hget_old_x i hi, hget_old_y i hi]
      exact hagree i w' hiw'
    · by_cases heq : i = env.length
      · subst heq
        rw [hget_last_x, hget_last_y]
        have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg.1
        rcases hop with hop | hop | hop
        · simp only [rcStep, hop, isBinary, ite_true] at hstep_cost
          split_ifs at hstep_cost with hany
          · dsimp only at hstep_cost; omega
          · cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
            | cons a t =>
              cases t with
              | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
              | cons b t2 =>
                have hl2 : (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 := by
                  rw [hins]; simp
                congr 1; apply List.map_congr_left
                intro j hj
                obtain ⟨w0, hw0⟩ := hall_inr_of_len2 hl2 j hj
                exact hagree j w0 hw0
        · simp only [rcStep, hop, isBinary, ite_true] at hstep_cost
          split_ifs at hstep_cost with hany
          · dsimp only at hstep_cost; omega
          · cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
            | cons a t =>
              cases t with
              | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
              | cons b t2 =>
                have hl2 : (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 := by
                  rw [hins]; simp
                congr 1; apply List.map_congr_left
                intro j hj
                obtain ⟨w0, hw0⟩ := hall_inr_of_len2 hl2 j hj
                exact hagree j w0 hw0
        · simp only [rcStep, hop] at hiw'
          cases hgi : g.inputs with
          | nil =>
            rw [hgi] at hiw'; dsimp only at hiw'; rw [hstep_env_last] at hiw'; cases hiw'
          | cons j rest_i =>
            rw [hgi] at hiw'; dsimp only at hiw'
            cases hm : env.getD j (Sum.inl false) with
            | inl b => rw [hm] at hiw'; dsimp only at hiw'; rw [hstep_env_last] at hiw'; cases hiw'
            | inr w0 =>
              rw [hop]
              simp only [GateOp.eval, List.map_cons, List.headD_cons, hagree j w0 hm]
      · exfalso
        have hlen_st : (rcStep nOut (out, env) g).2.length = env.length + 1 := rcStep_env_len nOut (out, env) g
        rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'

lemma rcCircuit_props (nIn nOut : ℕ) (env0 : List (Bool ⊕ ℕ)) (hlen0 : env0.length = nIn)
    (gs : List Gate) (o : ℕ) (hM : ∀ g ∈ gs, legal g) :
    let res := rcCircuit nOut env0 gs o
    (∀ g ∈ res.1, legal g) ∧
    binaryCost res.1 ≤ binaryCost gs ∧
    (∀ (xs ys : List Bool), xs.length = nIn → ys.length = nOut →
      (∀ i < nIn, match env0.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut ∧ xs.getD i false = ys.getD w' false) →
      Circuit.eval ⟨res.1, res.2⟩ ys = Circuit.eval ⟨gs, o⟩ xs) := by
  dsimp only [rcCircuit]
  have hfold_leg := rcFold_legal nOut gs ([], env0) (by intro g h; cases h) hM
  have hfold_bc : binaryCost (gs.foldl (rcStep nOut) ([], env0)).1 ≤ binaryCost gs := by
    have := rcFold_binCost_le nOut gs ([], env0); simpa [binaryCost] using this
  have hcore_eval : ∀ (xs ys : List Bool), xs.length = nIn → ys.length = nOut →
      (∀ i < nIn, match env0.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut ∧ xs.getD i false = ys.getD w' false) →
      ∀ i, match (gs.foldl (rcStep nOut) ([], env0)).2.getD i (Sum.inl false) with
        | Sum.inl b => (gs.foldl step xs).getD i false = b
        | Sum.inr w' => w' < nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length ∧
            (gs.foldl step xs).getD i false = ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).getD w' false := by
    intro xs ys hxl hyl hinit
    have hinit' : ∀ i, match (([] : List Gate), env0).2.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut + (([] : List Gate), env0).1.length ∧ xs.getD i false = ((([] : List Gate), env0).1.foldl step ys).getD w' false := by
      intro i
      by_cases hi : i < nIn
      · simpa using hinit i hi
      · dsimp only
        rw [List.getD_eq_default _ _ (by omega)]
        exact List.getD_eq_default _ _ (by omega)
    exact (rcFold_eval_inv nOut gs ys hyl hM xs ([], env0) (by simp [hlen0, hxl]) hinit').2
  cases hm : (gs.foldl (rcStep nOut) ([], env0)).2.getD o (Sum.inl false) with
  | inr w' =>
    refine ⟨hfold_leg, hfold_bc, ?_⟩
    intro xs ys hxl hyl hinit
    have h := hcore_eval xs ys hxl hyl hinit o
    rw [hm] at h; exact h.2.symm
  | inl b =>
    cases b with
    | false =>
      refine ⟨hfold_leg, hfold_bc, ?_⟩
      intro xs ys hxl hyl hinit
      have h := hcore_eval xs ys hxl hyl hinit o
      rw [hm] at h
      change ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).getD (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false =
        (gs.foldl step xs).getD o false
      rw [h, List.getD_eq_default _ _ (by rw [wfold_len, hyl])]
    | true =>
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with h | rfl
        · exact hfold_leg g h
        · exact ⟨by simp, by decide⟩
      · rw [binaryCost_append_one]; simp [isBinary]; exact hfold_bc
      · intro xs ys hxl hyl hinit
        have h := hcore_eval xs ys hxl hyl hinit o
        rw [hm] at h
        change (((gs.foldl (rcStep nOut) ([], env0)).1 ++ [({ op := GateOp.not, inputs := [] } : Gate)]).foldl step ys).getD
            (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false =
          (gs.foldl step xs).getD o false
        rw [h, List.foldl_append]
        change (step ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys) ({ op := GateOp.not, inputs := [] } : Gate)).getD
            (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false = true
        have hlen : ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).length =
            nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length := by rw [wfold_len, hyl]
        rw [← hlen, List.getD_eq_getElem _ _ (by simp [step])]
        simp [step, GateOp.eval]

lemma rcCircuit_binCost_lt (k : ℕ) (hk : k < 8) (gs : List Gate) (o : ℕ) (hM : ∀ g ∈ gs, legal g)
    (x1 x2 : List Bool) (hx1l : x1.length = 8) (hx2l : x2.length = 8)
    (hagree_xy : ∀ i < 8, i ≠ k → x1.getD i false = x2.getD i false)
    (hdiff_xy : Circuit.eval ⟨gs, o⟩ x1 ≠ Circuit.eval ⟨gs, o⟩ x2)
    (z1 z2 : List Bool) (hz1l : z1.length = 8) (hz2l : z2.length = 8)
    (hz1k : z1.getD k false = false) (hz2k : z2.getD k false = false)
    (hdiff_zz : Circuit.eval ⟨gs, o⟩ z1 ≠ Circuit.eval ⟨gs, o⟩ z2) :
    let env0 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 8 => if i.val = k then Sum.inl false else Sum.inr i.val
    binaryCost (rcCircuit 8 env0 gs o).1 + 1 ≤ binaryCost gs := by
  intro env0
  have hle_fold : binaryCost (gs.foldl (rcStep 8) ([], env0)).1 ≤ binaryCost gs := by
    have := rcFold_binCost_le 8 gs ([], env0); simpa [binaryCost] using this
  have hbc_rc : binaryCost (rcCircuit 8 env0 gs o).1 = binaryCost (gs.foldl (rcStep 8) ([], env0)).1 := by
    dsimp only [rcCircuit]
    cases (gs.foldl (rcStep 8) ([], env0)).2.getD o (Sum.inl false) with
    | inr w' => rfl
    | inl b => cases b with
      | false => rfl
      | true => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  rw [hbc_rc]
  by_contra hlt
  have hzero : binaryCost ([] : List Gate) = 0 := rfl
  have heq_cost : binaryCost (gs.foldl (rcStep 8) ([], env0)).1 = binaryCost ([] : List Gate) + binaryCost gs := by
    rw [hzero, Nat.zero_add]; omega
  cases hm : (gs.foldl (rcStep 8) ([], env0)).2.getD o (Sum.inl false) with
  | inr w' =>
    have hinit : ∀ i w0, (([] : List Gate), env0).2.getD i (Sum.inl false) = Sum.inr w0 → x1.getD i false = x2.getD i false := by
      intro i w0 hiw
      by_cases hi : i < 8
      · dsimp only at hiw
        rw [List.getD_eq_getElem env0 _ (by simp [env0, hi])] at hiw
        change (List.ofFn fun j : Fin 8 => if j.val = k then Sum.inl false else Sum.inr j.val)[i]'(by simp [hi]) = Sum.inr w0 at hiw
        rw [List.getElem_ofFn] at hiw
        by_cases hik : i = k
        · simp [hik] at hiw
        · exact hagree_xy i hi hik
      · dsimp only at hiw
        rw [List.getD_eq_default env0 _ (by simp [env0]; omega)] at hiw; cases hiw
    have hsame := rcFold_inr_agree 8 gs hM x1 x2 ([], env0) (by simp [env0, hx1l]) (by simp [env0, hx2l])
      heq_cost hinit o w' hm
    exact hdiff_xy hsame
  | inl b =>
    have hinit_z : ∀ (z : List Bool), z.length = 8 → z.getD k false = false →
        ∀ i, match (([] : List Gate), env0).2.getD i (Sum.inl false) with
          | Sum.inl b0 => z.getD i false = b0
          | Sum.inr w' => w' < 8 + ([] : List Gate).length ∧ z.getD i false = (([] : List Gate).foldl step z).getD w' false := by
      intro z hzl hzk i
      by_cases hi : i < 8
      · dsimp only
        rw [List.getD_eq_getElem env0 _ (by simp [env0, hi])]
        change match (List.ofFn fun j : Fin 8 => if j.val = k then Sum.inl false else Sum.inr j.val)[i]'(by simp [hi]) with
          | Sum.inl b0 => z.getD i false = b0
          | Sum.inr w' => w' < 8 + 0 ∧ z.getD i false = z.getD w' false
        rw [List.getElem_ofFn]
        by_cases hik : i = k
        · subst hik; simp only [ite_true]; exact hzk
        · simp [hik, hi]
      · dsimp only
        rw [List.getD_eq_default env0 _ (by simp [env0]; omega)]
        exact List.getD_eq_default z false (by omega)
    have hz1 := (rcFold_eval_inv 8 gs z1 hz1l hM z1 ([], env0) (by simp [env0, hz1l]) (hinit_z z1 hz1l hz1k)).2 o
    have hz2 := (rcFold_eval_inv 8 gs z2 hz2l hM z2 ([], env0) (by simp [env0, hz2l]) (hinit_z z2 hz2l hz2k)).2 o
    rw [hm] at hz1 hz2
    dsimp only at hz1 hz2
    exact hdiff_zz (hz1.trans hz2.symm)

def graphF (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

def witness : List Gate := [
  ⟨.and, [0, 3]⟩,
  ⟨.or, [1, 7]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.and, [9, 10]⟩,
  ⟨.or, [0, 3]⟩,
  ⟨.or, [5, 6]⟩,
  ⟨.or, [13, 7]⟩,
  ⟨.and, [12, 14]⟩,
  ⟨.or, [2, 7]⟩,
  ⟨.and, [16, 6]⟩,
  ⟨.or, [8, 11]⟩,
  ⟨.or, [18, 15]⟩,
  ⟨.or, [19, 17]⟩]

theorem witness_basis : ∀ g ∈ witness, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨witness, 20⟩ (List.ofFn x) = graphF x := by decide +kernel

def embed (y : Fin 7 → Bool) : Fin 8 → Bool
  | ⟨0, _⟩ => y 3
  | ⟨1, _⟩ => y 4
  | ⟨2, _⟩ => false
  | ⟨3, _⟩ => y 5
  | ⟨4, _⟩ => y 2
  | ⟨5, _⟩ => y 0
  | ⟨6, _⟩ => y 1
  | ⟨7, _⟩ => y 6

set_option maxRecDepth 16000 in
theorem embed_value : ∀ y : Fin 7 → Bool, graphF (embed y) = edgeValue y := by decide +kernel

end PEqualNP.Outside.L_meta_30272

open PEqualNP.Outside.L_meta_30272 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_30272 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o legalG _ computes
  change ∀ x, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = graphF x at computes
  by_cases hasNot : ∃ g ∈ gates, g.op = GateOp.not
  · obtain ⟨g, hg, hnot⟩ := hasNot
    have hbc_lt : binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, hg, by simp [isBinary, hnot]⟩
    have hleg' : ∀ g ∈ gates, legal g := legalG
    let env1 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 8 => if i.val = 2 then Sum.inl false else Sum.inr i.val
    let C1 := rcCircuit 8 env1 gates o
    have h1_props := rcCircuit_props 8 8 env1 (by simp [env1]) gates o hleg'
    have h1_eval : ∀ x : Fin 8 → Bool, x 2 = false → Circuit.eval ⟨C1.1, C1.2⟩ (List.ofFn x) = graphF x := by
      intro x hx1
      rw [h1_props.2.2 (List.ofFn x) (List.ofFn x) (by simp) (by simp) ?_, computes x]
      intro i hi
      rw [List.getD_eq_getElem env1 _ (by simp [env1, hi])]
      change match (List.ofFn fun j : Fin 8 => if j.val = 2 then Sum.inl false else Sum.inr j.val)[i]'(by simp [hi]) with
        | Sum.inl b => (List.ofFn x).getD i false = b
        | Sum.inr w' => w' < 8 ∧ (List.ofFn x).getD i false = (List.ofFn x).getD w' false
      rw [List.getElem_ofFn]
      by_cases hi1 : i = 2
      · subst hi1; simp only [ite_true]; rw [List.getD_eq_getElem _ _ (by simp)]; simpa using hx1
      · simp [hi1, hi]
    have h1_lt : binaryCost C1.1 + 1 ≤ binaryCost gates := by
      let fx1 : Fin 8 → Bool := fun i => decide (i.val = 2 ∨ i.val = 6)
      let fx2 : Fin 8 → Bool := fun i => decide (i.val = 6)
      let fz1 : Fin 8 → Bool := fun _ => false
      let fz2 : Fin 8 → Bool := fun i => decide (i.val = 0 ∨ i.val = 3)
      exact rcCircuit_binCost_lt 2 (by decide) gates o hleg'
        (List.ofFn fx1) (List.ofFn fx2) (by simp) (by simp) (by decide)
        (by rw [computes fx1, computes fx2]; decide)
        (List.ofFn fz1) (List.ofFn fz2) (by simp) (by simp) (by decide) (by decide)
        (by rw [computes fz1, computes fz2]; decide)
    let env7 : List (Bool ⊕ ℕ) := [Sum.inr 3, Sum.inr 4, Sum.inl false, Sum.inr 5, Sum.inr 2, Sum.inr 0, Sum.inr 1, Sum.inr 6]

    let D := rcCircuit 7 env7 C1.1 C1.2
    have hd := rcCircuit_props 8 7 env7 (by decide) C1.1 C1.2 h1_props.1
    have sim : ∀ y : Fin 7 → Bool, Circuit.eval ⟨D.1, D.2⟩ (List.ofFn y) = edgeValue y := by
      intro y
      rw [hd.2.2 (List.ofFn (embed y)) (List.ofFn y) (by simp) (by simp) ?_,
        h1_eval (embed y) rfl, embed_value y]
      intro i hi
      interval_cases i
      · exact ⟨by decide, by simp [embed]⟩
      · exact ⟨by decide, by simp [embed]⟩
      · simp [env7, embed]
      · exact ⟨by decide, by simp [embed]⟩
      · exact ⟨by decide, by simp [embed]⟩
      · exact ⟨by decide, by simp [embed]⟩
      · exact ⟨by decide, by simp [embed]⟩
      · exact ⟨by decide, by simp [embed]⟩

    have lower := cost_bound D.1 D.2 hd.1 sim
    have weak : binaryCost D.1 ≤ binaryCost C1.1 := hd.2.1
    exact ⟨witness, 20, witness_basis, by change 13 ≤ gates.length; omega, witness_eval⟩
  · exact ⟨gates, o, fun g hg => ⟨(legalG g hg).1.imp_right (fun h => h.resolve_right
      (fun e => hasNot ⟨g, hg, e⟩)), (legalG g hg).2⟩, le_rfl, computes⟩
