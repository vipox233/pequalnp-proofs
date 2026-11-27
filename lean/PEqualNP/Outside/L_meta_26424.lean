import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26424_aux

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

end SearchP

section Compile256

abbrev W256 := BitVec 256

def bit256 (k : Fin 256) (z : W256) : Bool := z[k.val]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem read_bit256 (w : List W256) (i : ℕ) (k : Fin 256) :
    (w.map (bit256 k)).getD i false = bit256 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit256]

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W256) (g : Gate) : W256 := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W256) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit256 k)) g = (w ++ [action w g]).map (bit256 k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W256)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_bit256, List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit256, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def binaryCost (gs : List Gate) : ℕ := (gs.filter isBinary).length

theorem available_read {av : Finset W256} {w : List W256} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W256) (av : Finset W256) (hw : ∀ u ∈ w, holds av u)
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
    show ∀ x : W256, x ||| (0 : W256) = x from fun x => BitVec.or_zero,
    show ∀ x : W256, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (target : W256) (hnt0 : target ≠ 0) (hnt1 : target ≠ ~~~0)
    (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W256) (av : Finset W256) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit256 k))).getD out false = bit256 k target) :
    ∃ t, (t = target ∨ t = ~~~target) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = target := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit256, bit256] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim (hnt0 zero)
    · exact False.elim (hnt1 ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun u : W256 => ~~~u) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit256 k))).getD out false = bit256 k target := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W256) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
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

end Compile256

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


def v0 : W256 := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa#256
def v1 : W256 := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc#256
def v2 : W256 := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0#256
def v3 : W256 := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00#256
def v4 : W256 := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000#256
def v5 : W256 := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000#256
def v6 : W256 := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000#256
def v7 : W256 := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000#256

def roots8 : List W256 := [v0, v1, v2, v3, v4, v5, v6, v7]
def roots7 : List W256 := [v0, v1, v3, v4, v5, v6, v7]
def roots6 (b : Bool) : List W256 :=
  if b then [v0, v1, v3, v4, v6, v7] else [v0, v3, v4, v5, v6, v7]
def roots5 (b : Bool) : List W256 :=
  if b then [v0, v3, v4, v6, v7] else [v0, v4, v5, v6, v7]

def target8 : W256 :=
  (v0 &&& v4) ||| (v1 &&& v4) ||| (v0 &&& v5) ||| (v2 &&& v5) |||
  (v0 &&& v6) ||| (v3 &&& v6) ||| (v4 &&& v6) ||| (v1 &&& v7) |||
  (v3 &&& v7) ||| (v4 &&& v7) ||| (v6 &&& v7)

def fixBit (i : Fin 8) (val : Bool) (k : Fin 256) : Fin 256 :=
  let bit := 1 <<< i.val
  let m := if val then k.val ||| bit else k.val &&& (255 - bit)
  ⟨m % 256, Nat.mod_lt _ (by decide)⟩

def restrict (i : Fin 8) (val : Bool) : W256 → W256 := selectRows (fixBit i val)
def removeFirst (b : Bool) : Fin 8 := if b then 5 else 1
def firstVar (b : Bool) : W256 := if b then v5 else v1
def removeSecond (b : Bool) : Fin 8 := if b then 1 else 3
def secondVar (b : Bool) : W256 := if b then v1 else v3

def target7 (b : Bool) : W256 := restrict 2 b target8
def target6 (b : Bool) : W256 := restrict (removeFirst b) false (target7 b)
def target5 (b : Bool) : W256 := restrict (removeSecond b) false (target6 b)

def sep7a (b : Bool) : Fin 256 := if b then 0 else 16
def sep7b (b : Bool) : Fin 256 := if b then 32 else 18
def sep6a (b : Bool) : Fin 256 := if b then 16 else 64
def sep6b (b : Bool) : Fin 256 := if b then 18 else 72

def coreRows (b : Bool) : Array ℕ :=
  if b then #[17, 17, 17, 17, 65, 65, 65, 65, 72, 72, 72, 72, 80, 80, 80, 80, 136, 136, 136, 136, 144, 144, 144, 144, 192, 192, 192, 192, 17, 17, 17, 17, 17, 25, 25, 25, 25, 25, 25, 25, 25, 25, 65, 65, 65, 65, 65, 72, 72, 72, 72, 72, 73, 73, 73, 73, 73, 73, 73, 73, 73, 80, 80, 80, 9, 24, 64, 129, 9, 24, 64, 129, 9, 24, 64, 129, 9, 24, 64, 129, 9, 24, 64, 129, 9, 24, 64, 129, 9, 24, 64, 129, 0, 1, 8, 16, 128, 0, 1, 8, 9, 16, 24, 64, 128, 129, 0, 1, 8, 16, 128, 0, 1, 8, 16, 128, 0, 1, 8, 9, 16, 24, 64, 128, 129, 0, 1, 8]
  else #[17, 17, 17, 17, 33, 33, 33, 33, 65, 65, 65, 65, 80, 80, 80, 80, 144, 144, 144, 144, 192, 192, 192, 192, 17, 17, 17, 17, 17, 17, 33, 33, 33, 33, 33, 33, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 65, 65, 65, 65, 65, 65, 80, 80, 80, 80, 80, 80, 81, 81, 81, 81, 81, 81, 48, 96, 129, 160, 48, 96, 129, 160, 48, 96, 129, 160, 48, 96, 129, 160, 48, 96, 129, 160, 48, 96, 129, 160, 0, 1, 16, 32, 64, 128, 0, 1, 16, 32, 64, 128, 0, 1, 16, 32, 48, 64, 96, 128, 129, 160, 0, 1, 16, 32, 64, 128, 0, 1, 16, 32, 64, 128, 0, 1, 16, 32, 48, 64]

def coreMap (b : Bool) (k : Fin (64 + 64)) : Fin 256 :=
  ⟨(coreRows b)[k.val]! % 256, Nat.mod_lt _ (by decide)⟩

def rows5 (b : Bool) : List (WP 64) :=
  if b then [0x50a10a14299999991ff07ffff00000ff#128, 0x82c21058433333331fff83fe000f0f00#128, 0x0304206082222222e00003fff0f0f00f#128, 0x0400008004444444fffffc000f00fff0#128, 0x1808430108888888000000000fff0000#128]
  else [0x0820902082444444fc0fffffff000fff#128, 0x5041014104111111fff03ff03f0ff00f#128, 0x6082258208bbbbbb00003fffc00000f0#128, 0x8104060410222222ffffc00000f0ff00#128, 0x0208380820cccccc0000000000ff0000#128]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem nonconstants :
    (target8 ≠ 0 ∧ target8 ≠ ~~~0) ∧
    ∀ b, (target7 b ≠ 0 ∧ target7 b ≠ ~~~0) ∧
      (target6 b ≠ 0 ∧ target6 b ≠ ~~~0) ∧
      (target5 b ≠ 0 ∧ target5 b ≠ ~~~0) := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem core_projection : ∀ b, selectRows (coreMap b) (target5 b) = ~~~goalP 64 := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem core_supply (b : Bool) : ∀ w ∈ roots5 b,
    holds (rows5 b).toFinset (selectRows (coreMap b) w) := by
  apply map_holds_list
  cases b <;> decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem reject_false : searchP 64 6 (rows5 false) = false := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem reject_true : searchP 64 6 (rows5 true) = false := by
  decide +kernel

theorem core_no6 (b : Bool) (built : SignedBuild 6 (roots5 b).toFinset (target5 b)) : False := by
  have hnc := (nonconstants.2 b).2.2
  obtain ⟨t, ht, run⟩ := unwrap_sb hnc.1 hnc.2 built
  obtain ⟨s, hs, hl⟩ := compress run
  have hm := ops_map_of (selectRows_land (coreMap b))
    (selectRows_lor (coreMap b)) (selectRows_neg (coreMap b))
  have mapped := live_transport hm hl (fun w hw =>
    core_supply b w (List.mem_toFinset.mp (hs hw)))
  have heq : selectRows (coreMap b) t = ~~~goalP 64 ∨
      selectRows (coreMap b) t = goalP 64 := by
    rcases ht with rfl | rfl
    · exact .inl (core_projection b)
    · exact .inr (by rw [selectRows_neg, core_projection, BitVec.not_not])
  have hcore : goalP 64 ≠ 0 ∧ goalP 64 ≠ ~~~0 ∧ ~~~goalP 64 ≠ 0 ∧ ~~~goalP 64 ≠ ~~~0 := by decide
  have hnon : selectRows (coreMap b) t ≠ 0 ∧ selectRows (coreMap b) t ≠ ~~~0 := by
    rcases heq with h | h <;> rw [h]
    · exact ⟨hcore.2.2.1, hcore.2.2.2⟩
    · exact ⟨hcore.1, hcore.2.1⟩
  obtain ⟨z, hz, hrun⟩ := unwrap_sb hnon.1 hnon.2 mapped
  have hz' : z = goalP 64 ∨ z = ~~~goalP 64 := by
    rcases heq with h | h <;> rcases hz with rfl | rfl <;> rw [h]
    · exact .inr rfl
    · exact .inl BitVec.not_not
    · exact .inl rfl
    · exact .inr rfl
  have hnd : (rows5 b).Nodup := by cases b <;> decide
  have hrej : searchP 64 6 (rows5 b) = false := by
    cases b
    · exact reject_false
    · exact reject_true
  exact Bool.noConfusion (hrej.symm.trans (searchP_complete hz' 6 (rows5 b) hnd hrun))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem cofactor_no8 (b : Bool)
    (built : SignedBuild 8 roots7.toFinset (target7 b)) : False := by
  have h7 := (nonconstants.2 b).1
  have h6 := (nonconstants.2 b).2.1
  have h5 := (nonconstants.2 b).2.2
  have first : SignedBuild 7 (roots6 b).toFinset (target6 b) :=
    cut_signed (target7 b) (target6 b) roots7 (roots6 b) (firstVar b)
      (sep7a b) (sep7b b) (restrict (removeFirst b) false)
      (ops_map_of (selectRows_land (fixBit (removeFirst b) false))
        (selectRows_lor (fixBit (removeFirst b) false))
        (selectRows_neg (fixBit (removeFirst b) false)))
      (selectRows_neg (fixBit (removeFirst b) false)) h7 h6
      (by cases b <;> unfold bitDiff <;> decide +kernel)
      (sep_of_all _ _ _ _ (by cases b <;> decide +kernel))
      (.inl (by cases b <;> decide +kernel)) rfl
      (map_holds_list _ _ _ (by cases b <;> decide +kernel)) built
  have second : SignedBuild 6 (roots5 b).toFinset (target5 b) :=
    cut_signed (target6 b) (target5 b) (roots6 b) (roots5 b) (secondVar b)
      (sep6a b) (sep6b b) (restrict (removeSecond b) false)
      (ops_map_of (selectRows_land (fixBit (removeSecond b) false))
        (selectRows_lor (fixBit (removeSecond b) false))
        (selectRows_neg (fixBit (removeSecond b) false)))
      (selectRows_neg (fixBit (removeSecond b) false)) h6 h5
      (by cases b <;> unfold bitDiff <;> decide +kernel)
      (sep_of_all _ _ _ _ (by cases b <;> decide +kernel))
      (.inl (by cases b <;> decide +kernel)) rfl
      (map_holds_list _ _ _ (by cases b <;> decide +kernel)) first
  exact core_no6 b second

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem no_ten (t : W256) (ht : t = target8 ∨ t = ~~~target8)
    (built : build basicOps t 10 roots8.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress built
  have sep : bitDiff (32 : Fin 256) (36 : Fin 256) target8 := by
    unfold bitDiff
    decide +kernel
  have hd : bitDiff (32 : Fin 256) (36 : Fin 256) t := by
    rcases ht with rfl | rfl
    · exact sep
    · exact bitDiff_not sep
  have present : v2 ∈ s := live_has_unique_sep hs hl 32 36 hd
    (sep_of_all 32 36 roots8 v2 (by decide +kernel))
  have hm := fun c => ops_map_of (selectRows_land (fixBit 2 c))
    (selectRows_lor (fixBit 2 c)) (selectRows_neg (fixBit 2 c))
  have hn : ∀ c, restrict 2 c t ≠ 0 ∧ restrict 2 c t ≠ ~~~0 := by
    intro c
    rcases ht with rfl | rfl
    · exact (nonconstants.2 c).1
    · rw [restrict, selectRows_neg]
      exact not_const_of_neg (nonconstants.2 c).1
  have can := absorbing v2 (restrict 2)
    (fun c => selectRows_land (fixBit 2 c))
    (fun c => selectRows_lor (fixBit 2 c))
    (fun c => selectRows_neg (fixBit 2 c))
    (by decide +kernel) (by decide +kernel)
  have ne : v2 ≠ t := by rcases ht with rfl | rfl <;> decide +kernel
  have supply : ∀ c w, w ∈ s → holds roots7.toFinset (restrict 2 c w) := by
    intro c w hw
    exact map_holds_list (restrict 2 c) roots8 roots7
      (by cases c <;> decide +kernel) w (List.mem_toFinset.mp (hs hw))
  obtain ⟨c, _, result⟩ := double_cut v2 t (restrict 2) hm hn can ne
    10 s (fun _ => roots7.toFinset) hl present supply
  have result' : SignedBuild 8 roots7.toFinset (target7 c) := by
    rcases ht with rfl | rfl
    · exact result
    · change SignedBuild 8 roots7.toFinset (selectRows (fixBit 2 c) (~~~target8)) at result
      rw [selectRows_neg] at result
      simpa only [target7, restrict, BitVec.not_not] using sb_not result
  exact cofactor_no8 c result'

def edges : List ℕ := [0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 3, 7, 4, 7, 6, 7]
def edgeValue (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edges.length / 2,
    (List.ofFn x).getD (edges.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edges.getD (2 * i + 1) 0) false = true)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem sample8 : ∀ k : Fin 256,
    edgeValue (fun i => (roots8.getD i.val 0)[k.val]) = target8[k.val] := by
  decide +kernel

theorem cost_bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = edgeValue x) :
    10 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ roots8, holds roots8.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (roots8.map (bit256 k))).getD o false = bit256 k target8 := by
    let x (i : Fin 8) : Bool := bit256 k (roots8.getD i.val 0)
    have width : roots8.length = 8 := rfl
    have same : List.ofFn x = roots8.map (bit256 k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < roots8.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (roots8.map (bit256 k)) = bit256 k target8
    rw [← same, he]
    exact sample8 k
  obtain ⟨t, ht, run⟩ := compile target8 nonconstants.1.1 nonconstants.1.2
    gs o hg roots8 roots8.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a roots8.toFinset) :
      build basicOps t b roots8.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact no_ten t ht (lift low run)

def witnessGates : List Gate :=
  [⟨.or, [3, 4]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [1, 6]⟩,
   ⟨.and, [8, 10]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [0, 2]⟩,
   ⟨.or, [0, 11]⟩, ⟨.and, [5, 13]⟩, ⟨.and, [7, 12]⟩,
   ⟨.and, [9, 14]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [17, 18]⟩]

theorem witness_basis : ∀ g ∈ witnessGates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witnessGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨witnessGates, 19⟩ (List.ofFn x) = edgeValue x := by
  decide +kernel

end PEqualNP.Outside.L_meta_26424_aux

theorem PEqualNP.Outside.L_meta_26424 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o legal _oneNot computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, hmem, hop⟩ := hasNot
    have hlt : PEqualNP.Outside.L_meta_26424_aux.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists
        (p := PEqualNP.Outside.L_meta_26424_aux.isBinary)).mpr
        ⟨g, hmem, by simp [PEqualNP.Outside.L_meta_26424_aux.isBinary, hop]⟩
    have hbd := PEqualNP.Outside.L_meta_26424_aux.cost_bound gates o legal computes
    have hlen : PEqualNP.Outside.L_meta_26424_aux.witnessGates.length = 12 := rfl
    exact ⟨PEqualNP.Outside.L_meta_26424_aux.witnessGates, 19,
      PEqualNP.Outside.L_meta_26424_aux.witness_basis, by omega,
      PEqualNP.Outside.L_meta_26424_aux.witness_eval⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨hop, hcap⟩ := legal g hg
    refine ⟨?_, hcap⟩
    rcases hop with h | h | h
    · exact .inl h
    · exact .inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
