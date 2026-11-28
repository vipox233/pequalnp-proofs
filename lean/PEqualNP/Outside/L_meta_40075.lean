import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40075

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

theorem canalize_ops {n m : ℕ} {f0 f1 : BitVec n → BitVec m}
    (hAnd0 : ∀ a b, f0 (a &&& b) = (f0 a &&& f0 b))
    (_hOr0 : ∀ a b, f0 (a ||| b) = (f0 a ||| f0 b))
    (hNot0 : ∀ a, f0 (~~~a) = ~~~(f0 a))
    (hAnd1 : ∀ a b, f1 (a &&& b) = (f1 a &&& f1 b))
    (hOr1 : ∀ a b, f1 (a ||| b) = (f1 a ||| f1 b))
    (hNot1 : ∀ a, f1 (~~~a) = ~~~(f1 a))
    {a b p z : BitVec n} (htouch : p = a ∨ p = b)
    (hp0 : f0 p = 0) (hp1 : f1 p = ~~~0) (hz : z ∈ basicOps a b) :
    (f0 z = 0 ∨ f0 z = ~~~0) ∨ (f1 z = 0 ∨ f1 z = ~~~0) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases htouch with rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl
  · left; left; rw [hAnd0, hp0, bv_zero_and]
  · right; right; rw [hOr1, hp1, bv_not_zero_or]
  · left; left; rw [hAnd0, hNot0, hp0, bv_zero_and]
  · right; left; rw [hAnd1, hNot1, hp1, BitVec.not_not, bv_and_zero]
  · left; left; rw [hAnd0, hp0, bv_and_zero]
  · right; right; rw [hOr1, hp1, bv_or_not_zero]
  · right; left; rw [hAnd1, hNot1, hp1, BitVec.not_not, bv_and_zero]
  · left; left; rw [hAnd0, hNot0, hp0, bv_zero_and]

theorem live_transport_save2 {n m : ℕ} {f0 f1 : BitVec n → BitVec m}
    (hAnd0 : ∀ a b, f0 (a &&& b) = (f0 a &&& f0 b))
    (hOr0 : ∀ a b, f0 (a ||| b) = (f0 a ||| f0 b))
    (hNot0 : ∀ a, f0 (~~~a) = ~~~(f0 a))
    (hAnd1 : ∀ a b, f1 (a &&& b) = (f1 a &&& f1 b))
    (hOr1 : ∀ a b, f1 (a ||| b) = (f1 a ||| f1 b))
    (hNot1 : ∀ a, f1 (~~~a) = ~~~(f1 a))
    {g p : BitVec n} {k : ℕ} {s : Finset (BitVec n)} {av0 av1 : Finset (BitVec m)}
    (run : live basicOps g k s)
    (hp : p ∈ s) (hp0 : f0 p = 0) (hp1 : f1 p = ~~~0)
    (hng0 : f0 g ≠ 0 ∧ f0 g ≠ ~~~0) (hng1 : f1 g ≠ 0 ∧ f1 g ≠ ~~~0)
    (hav0 : ∀ w ∈ s, holds av0 (f0 w))
    (hav1 : ∀ w ∈ s, holds av1 (f1 w)) :
    2 ≤ k ∧ (SignedBuild (k - 2) av0 (f0 g) ∨ SignedBuild (k - 2) av1 (f1 g)) := by
  have hm0 := ops_map_of hAnd0 hOr0 hNot0
  have hm1 := ops_map_of hAnd1 hOr1 hNot1
  induction k generalizing s av0 av1 with
  | zero =>
    change s = {g} at run
    have hpg : p = g := by simpa [run] using hp
    subst hpg
    exact (hng0.1 hp0).elim
  | succ k ih =>
    rcases run with skip | ⟨a, ha, b, hb, hn, z, hz, hout, r, he, tail⟩
    · obtain ⟨hk, hsb⟩ := ih skip hp hav0 hav1
      refine ⟨by omega, hsb.imp (sb_le (by omega)) (sb_le (by omega))⟩
    · have inOld0 : ∀ u ∈ r, holds av0 (f0 u) := fun u hu => hav0 u (by simp [he, hu])
      have inOld1 : ∀ u ∈ r, holds av1 (f1 u) := fun u hu => hav1 u (by simp [he, hu])
      by_cases touches : p = a ∨ p = b
      · have hcan := canalize_ops hAnd0 hOr0 hNot0 hAnd1 hOr1 hNot1 touches hp0 hp1 hz
        rcases hcan with hcz0 | hcz1
        · have hz0 : holds av0 (f0 z) := hcz0.elim .inl (fun h => .inr (.inl h))
          obtain ⟨hk, hsb⟩ := live_transport_save_const hm0 tail (Finset.mem_insert_self z r)
            hcz0 hng0 (fun u hu => by
              rcases Finset.mem_insert.mp hu with rfl | hr
              · exact hz0
              · exact inOld0 u hr)
          exact ⟨by omega, .inl (sb_le (by omega) hsb)⟩
        · have hz1 : holds av1 (f1 z) := hcz1.elim .inl (fun h => .inr (.inl h))
          obtain ⟨hk, hsb⟩ := live_transport_save_const hm1 tail (Finset.mem_insert_self z r)
            hcz1 hng1 (fun u hu => by
              rcases Finset.mem_insert.mp hu with rfl | hr
              · exact hz1
              · exact inOld1 u hr)
          exact ⟨by omega, .inr (sb_le (by omega) hsb)⟩
      · have pr : p ∈ r := by
          rw [he] at hp
          simpa [Finset.mem_insert, not_or.mp touches |>.1, not_or.mp touches |>.2] using hp
        have pt : p ∈ insert z r := Finset.mem_insert_of_mem pr
        have hr0 := mem_ops_reach (hav0 a ha) (hav0 b hb) (hm0 a b z hz)
        have hr1 := mem_ops_reach (hav1 a ha) (hav1 b hb) (hm1 a b z hz)
        rcases hr0 with hok0 | ⟨x0, hx0, y0, hy0, hxy0, w0, hw0, hok0⟩
        · rcases hr1 with hok1 | ⟨x1, hx1, y1, hy1, hxy1, w1, hw1, hok1⟩
          · obtain ⟨hk, hsb⟩ := ih tail pt
              (fun u hu => by rcases Finset.mem_insert.mp hu with rfl | hr; exact hok0; exact inOld0 u hr)
              (fun u hu => by rcases Finset.mem_insert.mp hu with rfl | hr; exact hok1; exact inOld1 u hr)
            exact ⟨by omega, hsb.imp (sb_le (by omega)) (sb_le (by omega))⟩
          · obtain ⟨hk, hsb⟩ := ih tail pt
              (fun u hu => by rcases Finset.mem_insert.mp hu with rfl | hr; exact hok0; exact inOld0 u hr)
              (av1 := insert w1 av1)
              (fun u hu => by rcases Finset.mem_insert.mp hu with rfl | hr; exact hok1; exact holds_insert (inOld1 u hr))
            refine ⟨by omega, ?_⟩
            rcases hsb with h0 | h1
            · exact .inl (sb_le (by omega) h0)
            · exact .inr (sb_le (by omega) (sb_step hx1 hy1 hxy1 hw1 h1))
        · rcases hr1 with hok1 | ⟨x1, hx1, y1, hy1, hxy1, w1, hw1, hok1⟩
          · obtain ⟨hk, hsb⟩ := ih tail pt
              (av0 := insert w0 av0)
              (fun u hu => by rcases Finset.mem_insert.mp hu with rfl | hr; exact hok0; exact holds_insert (inOld0 u hr))
              (fun u hu => by rcases Finset.mem_insert.mp hu with rfl | hr; exact hok1; exact inOld1 u hr)
            refine ⟨by omega, ?_⟩
            rcases hsb with h0 | h1
            · exact .inl (sb_le (by omega) (sb_step hx0 hy0 hxy0 hw0 h0))
            · exact .inr (sb_le (by omega) h1)
          · obtain ⟨hk, hsb⟩ := ih tail pt
              (av0 := insert w0 av0)
              (fun u hu => by rcases Finset.mem_insert.mp hu with rfl | hr; exact hok0; exact holds_insert (inOld0 u hr))
              (av1 := insert w1 av1)
              (fun u hu => by rcases Finset.mem_insert.mp hu with rfl | hr; exact hok1; exact holds_insert (inOld1 u hr))
            refine ⟨by omega, ?_⟩
            rcases hsb with h0 | h1
            · exact .inl (sb_le (by omega) (sb_step hx0 hy0 hxy0 hw0 h0))
            · exact .inr (sb_le (by omega) (sb_step hx1 hy1 hxy1 hw1 h1))

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

theorem live_has_unique_sep {n : ℕ} {g p : BitVec n} {k : ℕ}
    {s : Finset (BitVec n)} {ls : List (BitVec n)}
    (hs : s ⊆ ls.toFinset) (hl : live basicOps g k s)
    (a b : Fin n) (hd : bitDiff a b g)
    (huniq : ∀ w ∈ ls, bitDiff a b w → w = p) : p ∈ s := by
  obtain ⟨w, hw, hdw⟩ := live_separates (bitDiff a b) hd (ops_bitDiff a b) hl
  have hwp : w = p := huniq w (List.mem_toFinset.mp (hs hw)) hdw
  exact hwp ▸ hw

end FreeNot


section Search50

abbrev W50 := BitVec 50
def sep50 (x : W50) : BitVec 25 := ((x >>> 25) ^^^ x).setWidth 25
def cuts50 (ws : List W50) : BitVec 25 := ws.foldr (fun w v => sep50 w ||| v) 0
def goal50 : W50 := (-1 : BitVec 25) ++ (0 : BitVec 25)

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

def differs50 (i : Fin 25) (w : W50) : Prop :=
  w.getLsbD (25 + i.val) ≠ w.getLsbD i.val

theorem ops_differs50 (i : Fin 25) (a b z : W50) (hz : z ∈ basicOps a b)
    (hd : differs50 i z) : differs50 i a ∨ differs50 i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differs50 at ha hb
  simp only [not_not] at ha hb
  have hi : 25 + i.val < 50 := by omega
  have hi' : i.val < 50 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts50_spec (ws : List W50) (i : Fin 25) :
    (cuts50 ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs50 i w := by
  induction ws with
  | nil => simp [cuts50]
  | cons a rest ih =>
    change (sep50 a ||| cuts50 rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep50, i.isLt, differs50, Nat.add_comm, bx]

theorem cuts50_full {g : W50} (hg : g = goal50 ∨ g = ~~~goal50) {k : ℕ} {ws : List W50}
    (h : live basicOps g k ws.toFinset) : cuts50 ws = -1 := by
  have hd : ∀ i, differs50 i g := by rcases hg with rfl | rfl <;> unfold differs50 <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs50 ⟨j, hj⟩) (hd ⟨j, hj⟩) (ops_differs50 ⟨j, hj⟩) h
  have hbit := (cuts50_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts50 ws)[j] = (BitVec.allOnes 25)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

def keepChoices (a b : W50) (r : List W50) : List (List W50) :=
  [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W50} {a b : W50} {needed : Finset W50}
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

theorem singleton_list {goal : W50} {ws : List W50} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) :
    ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatchOp (extra : ℕ) (next : ℕ → List W50 → Bool) (a b w : W50) (r : List W50) : Bool :=
  let v := sep50 w ||| cuts50 r
  ((v == -1) && next extra (w :: r)) ||
  ((extra != 0) && (((v ||| sep50 a == -1) && next (extra - 1) (w :: a :: r)) ||
                     ((v ||| sep50 b == -1) && next (extra - 1) (w :: b :: r)))) ||
  ((extra ≥ 2) && (v ||| sep50 a ||| sep50 b == -1) && next (extra - 2) (w :: a :: b :: r))

def dispatch (extra : ℕ) (next : ℕ → List W50 → Bool) (a b : W50) (r : List W50) : Bool :=
  (ops a b).any fun w => dispatchOp extra next a b w r

theorem dispatch_of_ops {extra : ℕ} {next : ℕ → List W50 → Bool} {a b : W50} {r : List W50}
    (h0 : dispatchOp extra next a b (a &&& b) r = false)
    (h1 : dispatchOp extra next a b (a ||| b) r = false)
    (h2 : dispatchOp extra next a b (a &&& ~~~b) r = false)
    (h3 : dispatchOp extra next a b (b &&& ~~~a) r = false) :
    dispatch extra next a b r = false := by
  simp [dispatch, ops, h0, h1, h2, h3]

def optimized : ℕ → ℕ → List W50 → Bool
  | 0, _, ws => (ws == [goal50] || ws == [~~~goal50])
  | k + 1, extra, ws => (ws == [goal50] || ws == [~~~goal50]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W50} {r kept : List W50}
    (next : ℕ → List W50 → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts50 (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [dispatchOp, cuts50, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W50} (hg : g = goal50 ∨ g = ~~~goal50) (n : ℕ) (ws : List W50)
    (extra : ℕ) (hn : ws.Nodup) (room : extra + ws.length = n + 1)
    (h : live basicOps g n ws.toFinset) : optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W50} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
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
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega)
          (by omega) (cuts50_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap,
          go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search50 (n : ℕ) (inputs : List W50) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n + 1) && (cuts50 ws == -1) && optimized n (n + 1 - ws.length) ws

theorem search50_complete {g : W50} (hg : g = goal50 ∨ g = ~~~goal50) (n : ℕ) (inputs : List W50)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search50 n inputs = true := by
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
    by simp [sz, cuts50_full hg hl',
      optimized_complete hg n ws _ hnd (by omega : n + 1 - ws.length + ws.length = n + 1) hl']⟩

theorem signed_reject50 {k : ℕ} {ws : List W50} (hn : ws.Nodup) (hf : search50 k ws = false)
    {t : W50} (ht : t = goal50 ∨ t = ~~~goal50) (h : SignedBuild k ws.toFinset t) : False := by
  have nt : goal50 ≠ 0 ∧ goal50 ≠ ~~~0 ∧ ~~~goal50 ≠ 0 ∧ ~~~goal50 ≠ ~~~0 := by decide
  rcases ht with rfl | rfl
  all_goals
    rcases h with h | h | h | h
    · first | exact nt.1 h | exact nt.2.2.1 h
    · first | exact nt.2.1 h | exact nt.2.2.2 h
    · exact Bool.noConfusion (hf.symm.trans (search50_complete (by simp) k ws hn h))
    · exact Bool.noConfusion (hf.symm.trans (search50_complete (by simp) k ws hn h))


end Search50


section Compile64

abbrev W64 := BitVec 64

def bit64 (k : Fin 64) (z : W64) : Bool := z[k.val]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem read_bit64 (w : List W64) (i : ℕ) (k : Fin 64) :
    (w.map (bit64 k)).getD i false = bit64 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit64]

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W64) (g : Gate) : W64 := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W64) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit64 k)) g = (w ++ [action w g]).map (bit64 k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W64)[k.val] = false := by change (BitVec.ofNat 64 0)[k.val] = false; simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_bit64, List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit64, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def binaryCost (gs : List Gate) : ℕ := (gs.filter isBinary).length

theorem available_read {av : Finset W64} {w : List W64} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W64) (av : Finset W64) (hw : ∀ u ∈ w, holds av u)
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
    show ∀ x : W64, x ||| (0 : W64) = x from fun x => BitVec.or_zero,
    show ∀ x : W64, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (target : W64) (hnt0 : target ≠ 0) (hnt1 : target ≠ ~~~0)
    (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W64) (av : Finset W64) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit64 k))).getD out false = bit64 k target) :
    ∃ t, (t = target ∨ t = ~~~target) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = target := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit64, bit64] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim (hnt0 zero)
    · exact False.elim (hnt1 ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun u : W64 => ~~~u) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit64 k))).getD out false = bit64 k target := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W64) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
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

end Compile64


section Lower

def idx6 (x : Fin 6 → Bool) : ℕ :=
  (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
  (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0)

theorem sum_eq (x : Fin 6 → Bool) :
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = idx6 x := by
  simp [Fin.sum_univ_six, idx6]

def fVal (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276808392 * 2 ^ 32 + 4205505024) (idx6 x)

def v0 : W64 := 0xaaaaaaaaaaaaaaaa
def v1 : W64 := 0xcccccccccccccccc
def v2 : W64 := 0xf0f0f0f0f0f0f0f0
def v3 : W64 := 0xff00ff00ff00ff00
def v4 : W64 := 0xffff0000ffff0000
def v5 : W64 := 0xffffffff00000000

def rows6 : List W64 := [v0, v1, v2, v3, v4, v5]
def rows5 : List W64 := [v0, v1, v3, v4, v5]

def target6 : W64 := 0xfeeaeac8faaaea00

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem sample6 : ∀ k : Fin 64,
    fVal (fun i => (rows6.getD i.val 0)[k.val]) = target6[k.val] := by
  decide +kernel

def fixBit (i : Fin 6) (val : Bool) (k : Fin 64) : Fin 64 :=
  let bit := 1 <<< i.val
  let m := if val then k.val ||| bit else k.val &&& (63 - bit)
  ⟨m % 64, Nat.mod_lt _ (by decide)⟩

def restrict (i : Fin 6) (val : Bool) : W64 → W64 := selectRows (fixBit i val)

theorem t6_nc : target6 ≠ 0 ∧ target6 ≠ ~~~0 := by decide

theorem sep_of_all {n : ℕ} (a b : Fin n) (ls : List (BitVec n)) (p : BitVec n)
    (h : ls.all (fun w => !(w[a.val] != w[b.val]) || w == p) = true) :
    ∀ w ∈ ls, bitDiff a b w → w = p := by
  intro w hw hdiff
  have h1 := List.all_eq_true.mp h w hw
  simp only [Bool.or_eq_true, Bool.not_eq_true', bne_eq_false_iff_eq, beq_iff_eq] at h1
  exact h1.resolve_left hdiff

theorem sep6 : bitDiff ⟨10, by decide⟩ ⟨14, by decide⟩ target6 ∧
    ∀ w ∈ rows6, bitDiff ⟨10, by decide⟩ ⟨14, by decide⟩ w → w = v2 :=
  ⟨by unfold bitDiff; decide +kernel,
   sep_of_all ⟨10, by decide⟩ ⟨14, by decide⟩ rows6 v2 (by decide +kernel)⟩

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

theorem bitDiff_not {n : ℕ} {a b : Fin n} {w : BitVec n} (h : bitDiff a b w) :
    bitDiff a b (~~~w) := by
  intro heq
  apply h
  simp only [BitVec.getElem_not] at heq
  cases ha : w[a.val] <;> cases hb : w[b.val] <;> simp_all

theorem not_const_of_neg {n : ℕ} {w : BitVec n} (h : w ≠ 0 ∧ w ≠ ~~~0) :
    ~~~w ≠ 0 ∧ ~~~w ≠ ~~~0 := by
  refine ⟨fun heq => h.2 ?_, fun heq => h.1 ?_⟩
  · simpa only [BitVec.not_not] using congrArg (fun u : BitVec n => ~~~u) heq
  · simpa only [BitVec.not_not] using congrArg (fun u : BitVec n => ~~~u) heq

theorem img_sign {n m : ℕ} {f : BitVec n → BitVec m} (hNot : ∀ a, f (~~~a) = ~~~(f a))
    {T t : BitVec n} {T' : BitVec m} (hT : f T = T') (ht : t = T ∨ t = ~~~T) :
    f t = T' ∨ f t = ~~~T' := by
  rcases ht with rfl | rfl
  · exact .inl hT
  · exact .inr (by rw [hNot, hT])

theorem sign_nc {n : ℕ} {T x : BitVec n} (hx : x = T ∨ x = ~~~T) (hT : T ≠ 0 ∧ T ≠ ~~~0) :
    x ≠ 0 ∧ x ≠ ~~~0 := by
  rcases hx with rfl | rfl
  · exact hT
  · exact not_const_of_neg hT

theorem sb_out {n k : ℕ} {av : Finset (BitVec n)} {T x : BitVec n} (hx : x = T ∨ x = ~~~T)
    (hT : T ≠ 0 ∧ T ≠ ~~~0) (h : SignedBuild k av x) :
    ∃ t, (t = T ∨ t = ~~~T) ∧ build basicOps t k av := by
  obtain ⟨t, ht, hb⟩ := unwrap_sb (sign_nc hx hT).1 (sign_nc hx hT).2 h
  refine ⟨t, ?_, hb⟩
  rcases hx with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [BitVec.not_not]

theorem elim_one {n m : ℕ} (f : BitVec n → BitVec m)
    (hAnd : ∀ a b, f (a &&& b) = (f a &&& f b)) (hOr : ∀ a b, f (a ||| b) = (f a ||| f b))
    (hNot : ∀ a, f (~~~a) = ~~~(f a))
    {rows : List (BitVec n)} {rows' : List (BitVec m)} {T p : BitVec n} {T' : BitVec m}
    {i j : Fin n} (hsep : bitDiff i j T ∧ ∀ w ∈ rows, bitDiff i j w → w = p)
    (hp : f p = 0 ∨ f p = ~~~0) (hT : f T = T') (hT' : T' ≠ 0 ∧ T' ≠ ~~~0)
    (hrows : ∀ w ∈ rows, holds rows'.toFinset (f w))
    {k : ℕ} {t : BitVec n} (ht : t = T ∨ t = ~~~T) (hb : build basicOps t k rows.toFinset) :
    ∃ t', (t' = T' ∨ t' = ~~~T') ∧ build basicOps t' (k - 1) rows'.toFinset := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have hd : bitDiff i j t := by
    rcases ht with rfl | rfl
    · exact hsep.1
    · exact bitDiff_not hsep.1
  have hft := img_sign hNot hT ht
  obtain ⟨_, hsb⟩ := live_transport_save_const (ops_map_of hAnd hOr hNot) hl
    (live_has_unique_sep hs hl i j hd hsep.2) hp (sign_nc hft hT')
    (fun w hw => hrows w (List.mem_toFinset.mp (hs hw)))
  exact sb_out hft hT' hsb

theorem elim_two {n m : ℕ} (f0 f1 : BitVec n → BitVec m)
    (hAnd0 : ∀ a b, f0 (a &&& b) = (f0 a &&& f0 b)) (hOr0 : ∀ a b, f0 (a ||| b) = (f0 a ||| f0 b))
    (hNot0 : ∀ a, f0 (~~~a) = ~~~(f0 a))
    (hAnd1 : ∀ a b, f1 (a &&& b) = (f1 a &&& f1 b)) (hOr1 : ∀ a b, f1 (a ||| b) = (f1 a ||| f1 b))
    (hNot1 : ∀ a, f1 (~~~a) = ~~~(f1 a))
    {rows : List (BitVec n)} {rows0 rows1 : List (BitVec m)} {T p : BitVec n} {T0 T1 : BitVec m}
    {i j : Fin n} (hsep : bitDiff i j T ∧ ∀ w ∈ rows, bitDiff i j w → w = p)
    (hp0 : f0 p = 0) (hp1 : f1 p = ~~~0) (hT0 : f0 T = T0) (hT1 : f1 T = T1)
    (hT0' : T0 ≠ 0 ∧ T0 ≠ ~~~0) (hT1' : T1 ≠ 0 ∧ T1 ≠ ~~~0)
    (hrows0 : ∀ w ∈ rows, holds rows0.toFinset (f0 w))
    (hrows1 : ∀ w ∈ rows, holds rows1.toFinset (f1 w))
    {k : ℕ} {t : BitVec n} (ht : t = T ∨ t = ~~~T) (hb : build basicOps t k rows.toFinset) :
    (∃ t', (t' = T0 ∨ t' = ~~~T0) ∧ build basicOps t' (k - 2) rows0.toFinset) ∨
    (∃ t', (t' = T1 ∨ t' = ~~~T1) ∧ build basicOps t' (k - 2) rows1.toFinset) := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have hd : bitDiff i j t := by
    rcases ht with rfl | rfl
    · exact hsep.1
    · exact bitDiff_not hsep.1
  have hft0 := img_sign hNot0 hT0 ht
  have hft1 := img_sign hNot1 hT1 ht
  obtain ⟨_, hbr⟩ := live_transport_save2 hAnd0 hOr0 hNot0 hAnd1 hOr1 hNot1 hl
    (live_has_unique_sep hs hl i j hd hsep.2) hp0 hp1 (sign_nc hft0 hT0') (sign_nc hft1 hT1')
    (fun w hw => hrows0 w (List.mem_toFinset.mp (hs hw)))
    (fun w hw => hrows1 w (List.mem_toFinset.mp (hs hw)))
  exact hbr.imp (sb_out hft0 hT0') (sb_out hft1 hT1')

def target5_0 : W64 := 0xeeaaaa88aaaaaa00
def f_0 : W64 → W64 := restrict 2 false
theorem t5_0_nc : target5_0 ≠ 0 ∧ target5_0 ≠ ~~~0 := by decide
theorem f_0_t6 : f_0 target6 = target5_0 := by decide +kernel
theorem f_0_vp : f_0 v2 = 0 := by decide +kernel
theorem hold_rows5_0 : ∀ w ∈ rows6, holds rows5.toFinset (f_0 w) :=
  map_holds_list f_0 rows6 rows5 (by decide +kernel)

def mapList_0 : List ℕ :=
  [1, 1, 3, 3, 3, 8, 10, 16, 18, 24, 26, 26, 33, 33, 33, 34, 40, 42, 42, 48, 50, 50, 56, 56, 1, 9, 17, 11, 19, 35, 9, 11, 17, 19, 25, 27, 58, 35, 41, 49, 35, 41, 43, 58, 49, 51, 58, 57, 58, 9]

def rowMap_0 (k : Fin 50) : Fin 64 :=
  ⟨mapList_0.getD k.val 0 % 64, Nat.mod_lt _ (by decide)⟩

def proj_0 : W64 → W50 := selectRows rowMap_0

def inputs_0 : List W50 := [0x2b7efff00701f, 0x16d3ab8368d5c, 0x3ce5ccac70e60, 0x1f89f14f80f80, 0x1fff020fff000]

theorem inputs_0_nodup : inputs_0.Nodup := by decide
theorem proj_0_t5 : proj_0 target5_0 = goal50 := by decide +kernel
theorem hold_proj_0 : ∀ w ∈ rows5, holds inputs_0.toFinset (proj_0 w) :=
  map_holds_list proj_0 rows5 inputs_0 (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem branch_0_no : search50 6 inputs_0 = false := by
  decide +kernel

theorem branch_0_false (t : W64) (ht : t = target5_0 ∨ t = ~~~target5_0)
    (hb : build basicOps t 6 rows5.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have hm := ops_map_of (selectRows_land rowMap_0) (selectRows_lor rowMap_0) (selectRows_neg rowMap_0)
  have hsb : SignedBuild 6 inputs_0.toFinset (proj_0 t) :=
    live_transport hm hl (fun w hw => hold_proj_0 w (List.mem_toFinset.mp (hs hw)))
  have htg : proj_0 t = goal50 ∨ proj_0 t = ~~~goal50 := by
    rcases ht with rfl | rfl
    · exact .inl proj_0_t5
    · right
      change selectRows rowMap_0 (~~~target5_0) = ~~~goal50
      rw [selectRows_neg]
      exact congrArg (fun u : W50 => ~~~u) proj_0_t5
  exact signed_reject50 inputs_0_nodup branch_0_no htg hsb

def target5_1 : W64 := 0xffeeeeccffaaee00
def f_1 : W64 → W64 := restrict 2 true
theorem t5_1_nc : target5_1 ≠ 0 ∧ target5_1 ≠ ~~~0 := by decide
theorem f_1_t6 : f_1 target6 = target5_1 := by decide +kernel
theorem f_1_vp : f_1 v2 = ~~~0 := by decide +kernel
theorem hold_rows5_1 : ∀ w ∈ rows6, holds rows5.toFinset (f_1 w) :=
  map_holds_list f_1 rows6 rows5 (by decide +kernel)

def mapList_1 : List ℕ :=
  [1, 1, 2, 2, 3, 3, 3, 8, 8, 8, 16, 16, 18, 18, 18, 32, 33, 33, 33, 40, 40, 40, 48, 48, 48, 9, 17, 10, 34, 11, 19, 35, 9, 10, 24, 17, 24, 19, 26, 50, 34, 35, 41, 49, 41, 42, 56, 49, 50, 56]

def rowMap_1 (k : Fin 50) : Fin 64 :=
  ⟨mapList_1.getD k.val 0 % 64, Nat.mod_lt _ (by decide)⟩

def proj_1 : W64 → W50 := selectRows rowMap_1

def inputs_1 : List W50 := [0x9e29e6070073, 0x123e2f800707c, 0x274572a380380, 0x3c8fc45c07c00, 0x3ff8091ff8000]

theorem inputs_1_nodup : inputs_1.Nodup := by decide
theorem proj_1_t5 : proj_1 target5_1 = goal50 := by decide +kernel
theorem hold_proj_1 : ∀ w ∈ rows5, holds inputs_1.toFinset (proj_1 w) :=
  map_holds_list proj_1 rows5 inputs_1 (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem branch_1_no : search50 6 inputs_1 = false := by
  decide +kernel

theorem branch_1_false (t : W64) (ht : t = target5_1 ∨ t = ~~~target5_1)
    (hb : build basicOps t 6 rows5.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have hm := ops_map_of (selectRows_land rowMap_1) (selectRows_lor rowMap_1) (selectRows_neg rowMap_1)
  have hsb : SignedBuild 6 inputs_1.toFinset (proj_1 t) :=
    live_transport hm hl (fun w hw => hold_proj_1 w (List.mem_toFinset.mp (hs hw)))
  have htg : proj_1 t = goal50 ∨ proj_1 t = ~~~goal50 := by
    rcases ht with rfl | rfl
    · exact .inl proj_1_t5
    · right
      change selectRows rowMap_1 (~~~target5_1) = ~~~goal50
      rw [selectRows_neg]
      exact congrArg (fun u : W50 => ~~~u) proj_1_t5
  exact signed_reject50 inputs_1_nodup branch_1_no htg hsb


theorem no_B_binary (t : W64) (ht : t = target6 ∨ t = ~~~target6)
    (hb : build basicOps t 8 rows6.toFinset) : False := by
  rcases elim_two f_0 f_1 (selectRows_land (fixBit 2 false)) (selectRows_lor (fixBit 2 false))
    (selectRows_neg (fixBit 2 false)) (selectRows_land (fixBit 2 true))
    (selectRows_lor (fixBit 2 true)) (selectRows_neg (fixBit 2 true))
    sep6 f_0_vp f_1_vp f_0_t6 f_1_t6 t5_0_nc t5_1_nc hold_rows5_0 hold_rows5_1 ht hb with
    ⟨t5, ht5, hb5⟩ | ⟨t5, ht5, hb5⟩
  · exact branch_0_false t5 ht5 hb5
  · exact branch_1_false t5 ht5 hb5

theorem cost_bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = fVal x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ rows6, holds rows6.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (rows6.map (bit64 k))).getD o false = bit64 k target6 := by
    let x (i : Fin 6) : Bool := bit64 k (rows6.getD i.val 0)
    have width : rows6.length = 6 := rfl
    have same : List.ofFn x = rows6.map (bit64 k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < rows6.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (rows6.map (bit64 k)) = bit64 k target6
    rw [← same, he]
    exact sample6 k
  obtain ⟨t, ht, run⟩ := compile target6 t6_nc.1 t6_nc.2 gs o hg rows6 rows6.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a rows6.toFinset) :
      build basicOps t b rows6.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact no_B_binary t ht (lift low run)

def witnessGates : List Gate :=
  [⟨.and, [1, 2]⟩,
   ⟨.or, [6, 0]⟩,
   ⟨.and, [5, 1]⟩,
   ⟨.or, [8, 3]⟩,
   ⟨.and, [9, 7]⟩,
   ⟨.or, [2, 8]⟩,
   ⟨.and, [11, 3]⟩,
   ⟨.or, [12, 0]⟩,
   ⟨.and, [13, 4]⟩,
   ⟨.or, [14, 10]⟩]

theorem witness_mono : PEqualNP.MetaComplexity.Monotone2 ⟨witnessGates, 15⟩ := by
  intro g hg
  simp only [witnessGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : Fin 6 → Bool,
    Circuit.eval ⟨witnessGates, 15⟩ (List.ofFn x) = fVal x := by
  decide +kernel

end Lower

end PEqualNP.Outside.L_meta_40075

theorem PEqualNP.Outside.L_meta_40075 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4205505024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4205505024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  obtain ⟨C, hfit, hsz, hev⟩ := h
  have hev' : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_40075.fVal x := by
    intro x
    simpa only [PEqualNP.Outside.L_meta_40075.sum_eq, PEqualNP.Outside.L_meta_40075.fVal] using hev x
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, hmem, hop⟩ := hasNot
    have hlt : PEqualNP.Outside.L_meta_40075.binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists
        (p := PEqualNP.Outside.L_meta_40075.isBinary)).mpr
        ⟨g, hmem, by simp [PEqualNP.Outside.L_meta_40075.isBinary, hop]⟩
    have hlegal : ∀ g ∈ C.gates, PEqualNP.Outside.L_meta_40075.legal g := by
      intro g hg
      obtain ⟨hop', hcap⟩ := hfit g hg
      refine ⟨?_, hcap⟩
      simpa using hop'
    have hbd := PEqualNP.Outside.L_meta_40075.cost_bound C.gates C.output hlegal hev'
    have hlen : (⟨PEqualNP.Outside.L_meta_40075.witnessGates, 15⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = 10 := rfl
    have hcsz : C.gates.length ≤ s := hsz
    refine ⟨⟨PEqualNP.Outside.L_meta_40075.witnessGates, 15⟩,
      PEqualNP.Outside.L_meta_40075.witness_mono, by omega, ?_⟩
    intro x
    simpa only [PEqualNP.Outside.L_meta_40075.sum_eq, PEqualNP.Outside.L_meta_40075.fVal] using
      PEqualNP.Outside.L_meta_40075.witness_eval x
  · refine ⟨C, ?_, hsz, hev⟩
    intro g hg
    obtain ⟨hop, hcap⟩ := hfit g hg
    refine ⟨?_, hcap⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with h | h | h
    · exact .inl h
    · exact .inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
