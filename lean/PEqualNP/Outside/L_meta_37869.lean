import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37869

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

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
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

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
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

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4277074664 * 2 ^ 32 + 4276157088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x0010c10b21841551#64 ++ 0x880043042c861055#64 ++ 0x80b1c71f238c3ff7#64 ++ 0xf602c71c7c8e30ff#64 : BitVec 256),
   (0x411624652cb33301#64 ++ 0x1104589194b2cccc#64 ++ 0x435e24e73cf3332e#64 ++ 0xed0d78939cf3cccc#64 : BitVec 256),
   (0x046008b0405942a2#64 ++ 0x20118022c101650a#64 ++ 0xbc6038f8c0ffc3ff#64 ++ 0xdef180e3e303ff0f#64 : BitVec 256),
   (0x0b8036009602a804#64 ++ 0x402e00d802580aa0#64 ++ 0xbf803f00ff03fc3d#64 ++ 0xbefe00fc03fc0ff0#64 : BitVec 256),
   (0x1efb4000fbec0007#64 ++ 0x807bed0003efb000#64 ++ 0x5fffc000fffc001c#64 ++ 0x7d7fff0003fff000#64 : BitVec 256),
   (0x2fedbfde00000038#64 ++ 0x00bfb6ff78000000#64 ++ 0x6fffffff00000003#64 ++ 0xfdbffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [8, 2]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [9, 5]⟩, ⟨.or, [13, 11]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x80b1c71f238c3ff7 0xf602c71c7c8e30ff

def z1 : W := mkw 0x04600890404840a2 0x2011802241012102 0x3c001800c000c000 0x00f0006003000300

def z2 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc6038f8c0ffc3ff 0xdef180e3e303ff0f

def z3 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbf803f00ff03fc3d 0xbefe00fc03fc0ff0

def z4 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fffc000fffc001c 0x7d7fff0003fff000

def z5 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fffffff00000003 0xfdbffffffc000000

def z6 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e24e73cf3332e 0xed0d78939cf3cccc

def z7 : W := mkw 0x2fed3ed400000028 0x00bfb4fb50000000 0x6f4e38e000000000 0x09bd38e380000000

def z8 : W := mkw 0x2ffdffdf21841579 0x88bff7ff7c861055 0xefffffff238c3ff7 0xffbffffffc8e30ff

def z9 : W := mkw 0x0fe03eb0d65beaa6 0x603f80fac3596faa 0xbfe03ff8ffffffff 0xfeff80ffe3ffffff

def z10 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x407fc0ff00000002 0x4101ff03fc000000

def z11 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0x6fffffff3f003c03 0xfdbffffffcfc00f0

def z12 : W := mkw 0x0460089000000020 0x0011802240000000 0x2c6038f800000003 0xdcb180e3e0000000

def z13 : W := mkw 0x2fedbffe405942ba 0x20bfb6fff901650a 0xffffffffc0ffc3ff 0xffffffffff03ff0f

def z14 : W := mkw 0x2104bfde00000038 0x008412ff78000000 0x20003fff00000003 0x808000fffc000000

def z15 : W := mkw 0x0012000028a00001 0x0000480000a28000 0x435e00003cf0000c 0x6d0d780000f3c000

def z16 : W := mkw 0x000000009602a804 0x4000000002580aa0 0x10000000dc03c008 0x0040000003700f00

def z17 : W := mkw 0x10124000fbec0007 0x8040490003efb000 0x10000000fffc001c 0x0040000003fff000

def z18 : W := mkw 0x1efb48b0fbfd42a7 0xa07bed22c3eff50a 0xfffff8f8ffffc3ff 0xffffffe3e3ffff0f

def z19 : W := mkw 0x0000000000000000 0x0000000000000000 0x80200018008c03f7 0xd60080006002300f

def z20 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0xc3de27e73ff33f3f 0xff0f789f9cffccfc

def z21 : W := mkw 0x0010400121841541 0x8800410004861055 0x80000000238c3ff4 0x02000000008e30ff

def z22 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x431e24e73c033322 0xa10c78939cf00ccc

def z23 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0xffffffffff03fc3f 0xfffffffffffc0ff0

def z24 : W := mkw 0x04600890404840a2 0x2011802241012102 0xbc201818c00cc0d1 0x12f0806063003303

def z25 : W := mkw 0x2b8db74e00000018 0x00ae36dd38000000 0x43dfe7e700000002 0xed0f7f9f9c000000

def z26 : W := mkw 0x0012000028a00001 0x0000480000a28000 0x405e000000f00000 0x410178000003c000

def z27 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0x2c6038f800fc03c3 0xdcb180e3e003f00f

def z28 : W := mkw 0x7fffffffffff333f 0x91fffffffffffccc 0x7fffffffffff333f 0xfdfffffffffffccc

def z29 : W := mkw 0x45762cf56cfb73a3 0x3115d8b3d5b3edce 0x437e24ff3cff33ee 0xed0df893fcf3fccf

def z30 : W := mkw 0x411624452ca23101 0x1104589114b288c4 0x431e04073c003000 0x210c78101cf000c0

def z31 : W := mkw 0x010036000402a800 0x400400d800100aa0 0xa0003f000003fc21 0x828000fc00000ff0

def z32 : W := mkw 0x0a80000092000004 0x002a000002480000 0x1f800000ff00001c 0x3c7e000003fc0000

def z33 : W := mkw 0x0010400021840001 0x8000410000861000 0x80b1c700238c3c35 0xf602c71c008e30f0

def z34 : W := mkw 0x14694000414c0002 0x8051a50001053000 0x0021c000000c0000 0x0000870000003000

def z35 : W := mkw 0x4b963665beb3bb05 0x512e58d996faceec 0x43de27e73ff33f2e 0xed0f789f9cffccfc

def z36 : W := mkw 0x1eeb0000da680006 0x007bac000369a000 0x5f4e0000dc700008 0x097d38000371c000

def z37 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c000000c000001c 0x1c70000003000000

def z38 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0xffffffffc003c03f 0xffffffffff000f00

def z39 : W := mkw 0x0b90f70bb786bd55 0xc82e43dc2ede1af5 0x83b1c71f3f8c3ff7 0xf60ec71c7cfe30ff

def z40 : W := mkw 0x1efb4890fbec0027 0x807bed2243efb000 0x7ffff8f8fffc001f 0xfdffffe3e3fff000

def z41 : W := mkw 0x401200012ca23101 0x1100480004b288c4 0x000000003c003000 0x0000000000f000c0

def z42 : W := mkw 0x4104246504133300 0x1104109194104ccc 0x435e24e700033322 0xed0d78939c000ccc

def z43 : W := mkw 0x2114ffdf21841579 0x888453ff7c861055 0xa0b1ffff238c3ff7 0xf682c7fffc8e30ff

def z44 : W := mkw 0x1ee94000d34c0006 0x807ba500034d3000 0x1ca1c000c30c0010 0x10728700030c3000

def z45 : W := mkw 0x5fff6465ffff3307 0x917ffd9197fffccc 0x5fffe4e7ffff333e 0xfd7fff939ffffccc

def z46 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0x7fffffffdc03c00b 0xfdffffffff700f00

def z47 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0x038007003f003c00 0x200e001c00fc00f0

def z48 : W := mkw 0x0000002040594282 0x200000008101650a 0x90000000c0ffc3fc 0x024000000303ff0f

def z49 : W := mkw 0x6fffbfff6cfb73bb 0x31bffefffdb3edce 0xfffffffffcfff3ff 0xfffffffffff3ffcf

def z50 : W := mkw 0x0010400121841541 0x8800410004861055 0x00000000008c03c0 0x000000000002300f

def z51 : W := mkw 0x0000810a00000010 0x0000020428000000 0x00b1c71f00000003 0xf402c71c7c000000

def z52 : W := mkw 0x1a9b4000bba40005 0x806a6d0002ee9000 0x439fc0003f000000 0x210e7f0000fc0000

def z53 : W := mkw 0x0000c10a01040450 0x8800030428041011 0x80a1c318038c0ff7 0xd602870c600e303f

def z54 : W := mkw 0x3fffffdeffeea83f 0xc0ffffff7bffbaa0 0xfffffffffffffc3f 0xfffffffffffffff0

def z55 : W := mkw 0x0a80120092008804 0x402a004802480220 0xbc801b00c300cc11 0x12f2006c030c0330

def z56 : W := mkw 0x0fe03e90d64ae8a6 0x603f80fa43592ba2 0xbfa03f18ff0ffcfd 0xbefe80fc63fc3ff3

def z57 : W := mkw 0x3fffffdffbec157f 0x88ffffff7fefb055 0xfffffffffffc3fff 0xfffffffffffff0ff

def z58 : W := mkw 0x0470c10b61cc1553 0x8811c3042d873055 0x9cf1c71fe3fc3fff 0xfe73c71c7f8ff0ff

def z59 : W := mkw 0x0010400121841541 0x8800410004861055 0x80200018238c3ff7 0xd6008000608e30ff

def z60 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0x006000f800fc03c2 0x40018003e003f00f

def z61 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x6c7ff8ff00000003 0xddb1ffe3fc000000

def z62 : W := mkw 0x0ee9089000000020 0x003ba42240000000 0x6ffff8f800000003 0xfdbfffe3e0000000

def z63 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbf801f00ff00fc11 0x32fe007c03fc03f0

def z64 : W := mkw 0x0fe936009602a804 0x403fa4d802580aa0 0xffffff00ff03fc3d 0xfffffffc03fc0ff0

def z65 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0xc37e24ff3cff33ff 0xff0df893fcf3fccf

def z66 : W := mkw 0x0a904000b3840005 0x802a410002ce1000 0x1fb1c000ff8c001c 0x7c7ec70003fe3000

def z67 : W := mkw 0x147b400069ec0003 0x8051ed0001a7b000 0x40ffc00023fc0014 0x7503ff00008ff000

def z68 : W := mkw 0x0104244400000000 0x0004109110000000 0x434e20e000000000 0x090d388380000000

def z69 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x80b1c71f230c3cd1 0x3202c71c7c8c30f3

def z70 : W := mkw 0x2b8db74e9602a81c 0x40ae36dd3a580aa0 0x439fc7073f003c00 0x210e7f1c1cfc00f0

def z71 : W := mkw 0x0100240004022000 0x0004009000100880 0x030024003c03302c 0xac0c009000f00cc0

def z72 : W := mkw 0x2eed9bde00000038 0x00bbb66f78000000 0x6cffdbff00000003 0x51b3ff6ffc000000

def z73 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x2ca1ffff00000003 0x90b287fffc000000

def z74 : W := mkw 0x0000000000000000 0x0000000000000000 0xbc003800c003c03d 0x9ef000e003000f00

def z75 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e04e73cf03302 0x610d78139cf3c0cc

def z76 : W := mkw 0x1ffb7600ffeea807 0xc07fedd803ffbaa0 0x5fffc700fffc3c1c 0x7d7fff1c03fff0f0

def z77 : W := mkw 0x2104b74e00000018 0x008412dd38000000 0x0000070700000000 0x0000001c1c000000

def z78 : W := mkw 0x10004000d34c0006 0x80400100034d3000 0x10000000c30c0010 0x00400000030c3000

def z79 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbf003800dc03c03d 0x9efc00e003700f00

def z80 : W := mkw 0x00104001b786bd45 0xc800410006de1af5 0x90000000ff8ffffc 0x0240000003fe3fff

def z81 : W := mkw 0x0ee008b0d25942a6 0x203b8022c349650a 0xbfe038f8ffffc3ff 0xfeff80e3e3ffff0f

def z82 : W := mkw 0x0104244400000000 0x0004109110000000 0x000024e700000002 0x800000939c000000

def z83 : W := mkw 0x647f89ff28b11339 0x1191fe27fca2c44c 0x407fc0ff00f00302 0x4101ff03fc03c00c

def z84 : W := mkw 0x6104bfff04133338 0x118412fffc104ccc 0x20003fff00033323 0x808000fffc000ccc

def z85 : W := mkw 0x6fffbfff2cb33339 0x11bffefffcb2cccc 0x6fffffff3cf3332f 0xfdbffffffcf3cccc

def z86 : W := mkw 0x0470c9bb61dd57f3 0xa811c326ed87755f 0xbcf1ffffe3ffffff 0xfef3c7ffff8fffff

def z87 : W := mkw 0x1efbc10bfbec1557 0x887bef042fefb055 0xdfffc71ffffc3fff 0xff7fff1c7ffff0ff

def z88 : W := mkw 0x4116e56f2db73751 0x99045b95bcb6dcdd 0xc3ffe7ff3fff3fff 0xff0fff9ffcfffcff

def z89 : W := mkw 0x2fed3ed400000028 0x00bfb4fb50000000 0x6ffff8e000000000 0x7dbfffe380000000

def z90 : W := mkw 0x4116a56f2cb33751 0x19045a95bcb2ccdd 0xc35e27ff3cf33fef 0xef0d789ffcf3ccff

def z91 : W := mkw 0x1ffb7600fbec0007 0x807fedd803efb000 0x7fffff00fffc001d 0xfdfffffc03fff000

def z92 : W := mkw 0x2fedbffe001142b8 0x20bfb6fff800450a 0xefffffff0003c3e3 0xffbffffffc000f0f

def z93 : W := mkw 0x147b400069ec0003 0x8051ed0001a7b000 0x407fc00000fc0000 0x4101ff000003f000

def z94 : W := mkw 0x0460000040480002 0x0011800001012000 0xbc603800c0ffc03d 0xdef180e00303ff00

def z95 : W := mkw 0x4104246504133300 0x1104109194104ccc 0x000024e700033322 0x800000939c000ccc

def z96 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc201818c0ffc3fd 0x12f080606303ff0f

def z97 : W := mkw 0x0104244400000000 0x0004109110000000 0x435e24e700000002 0xed0d78939c000000

def z98 : W := mkw 0x2ee99b9a00000038 0x00bba66e68000000 0x2ca1db1800000001 0x10b2876c60000000

def z99 : W := mkw 0x0000000000000000 0x0000000000000000 0x80200018000c00d1 0x1200800060003003

def z100 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0xefffffff23003c37 0xffbffffffc8c00f0

def z101 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0x3f003800dc03c008 0x08fc00e003700f00

def z102 : W := mkw 0x4016006528b11301 0x1100580194a2c44c 0x405e20e700f3032e 0xcd0178839c03cc0c

def z103 : W := mkw 0x0ee9000040480002 0x003ba40001012000 0x5fffc000c0fc001c 0x7d7fff000303f000

def z104 : W := mkw 0x4104246504133300 0x1104109194104ccc 0x030024e73c03332e 0xac0c00939cf00ccc

def z105 : W := mkw 0x1ffb6400ffee2007 0x807fed9003ffb880 0x5fffe400ffff303c 0xfd7fff9003fffcc0

def z106 : W := mkw 0x0b90f70bb786bd55 0xc82e43dc2ede1af5 0xbfb1ff1fff8fffff 0xfefec7fc7ffe3fff

def z107 : W := mkw 0x0460000040480002 0x0011800001012000 0x1c600000c0fc001c 0x5c7180000303f000

def z108 : W := mkw 0x2b8dbfde00000038 0x00ae36ff78000000 0x639fffff00000003 0xa18e7ffffc000000

def z109 : W := mkw 0x2eed89de00000038 0x00bbb62778000000 0x4fffc0ff00000002 0x7d3fff03fc000000

def z110 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080070023003c00 0x2002001c008c00f0

def z111 : W := mkw 0x1eeb4000db6c0006 0x807bad00036db000 0x5fefc000df7c0018 0x197fbf00037df000

def z112 : W := mkw 0x0104a54e00000010 0x0004129538000000 0x43ffe7ff00000003 0xfd0fff9ffc000000

def z113 : W := mkw 0x1ffb7eb0ffffeaa7 0xe07fedfac3ffffaa 0xfffffff8ffffffff 0xffffffffe3ffffff

def z114 : W := mkw 0x0000002000110200 0x0000000080004408 0x000020e000030322 0x8000008380000c0c

def z115 : W := mkw 0x2104bffe001142b8 0x208412fff800450a 0xa0003fff0003c3e3 0x828000fffc000f0f

def z116 : W := mkw 0x1efb5200fbec8807 0xc07bed4803efb220 0xffffdb00fffccc1d 0x7fffff6c03fff330

def z117 : W := mkw 0x0000810a00000010 0x0000020428000000 0x0031c01f00000002 0x4000c7007c000000

def z118 : W := mkw 0x0100240004022000 0x0004009000100880 0x838027003f033c3d 0xbe0e009c00fc0cf0

def z119 : W := mkw 0x4b963665beb3bb05 0x512e58d996faceec 0xffde3fe7fff3ff3f 0xffff78ff9fffcffc

def z120 : W := mkw 0x0000002040594282 0x200000008101650a 0xbc003800c0ffc3fd 0x9ef000e00303ff0f

def z121 : W := mkw 0x0010400121841541 0x8800410004861055 0x0000000023003c00 0x00000000008c00f0

def z122 : W := mkw 0x0000089000000020 0x0000002240000000 0x200038f800000003 0x808000e3e0000000

def z123 : W := mkw 0x4016006528b11301 0x1100580194a2c44c 0x435e00e73cf0030e 0x6d0d78039cf3c00c

def z124 : W := mkw 0x45662cf44c7b62a2 0x311598b3d131ed8a 0xff6e38f8dcffc3ff 0xdffdb8e3e373ff0f

def z125 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x00b1c71f238c3fc2 0x6002c71c7c8e30ff

def z126 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x8091c70723003c35 0xb602471c1c8c00f0

def z127 : W := mkw 0x4016006528b11301 0x1100580194a2c44c 0x405e00e700f00302 0x410178039c03c00c

def z128 : W := mkw 0x1a9b4000bba40005 0x806a6d0002ee9000 0x43bfc0003f8c0014 0x750eff0000fe3000

def z129 : W := mkw 0x0110240124823101 0x00044090049208c4 0x031024073c83332e 0xec0c40901cf20ccc

def z130 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0xfffff800ffffc03d 0xffffffe003ffff00

def z131 : W := mkw 0x0000002000110200 0x0000000080004408 0x004000e000f00302 0x400100038003c00c

def z132 : W := mkw 0x2fedbfde04022038 0x00bfb6ff78100880 0x6fffffff3c03302f 0xfdbffffffcf00cc0

def z133 : W := mkw 0x2104bfde00000038 0x008412ff78000000 0x635e3fff00000003 0xed8d78fffc000000

def z134 : W := mkw 0x1efbc9bbfbfd57f7 0xa87bef26efeff55f 0xffffffffffffffff 0xffffffffffffffff

def z135 : W := mkw 0x1efb4001fbec1547 0x887bed0007efb055 0xdfffc000fffc3ffc 0x7f7fff0003fff0ff

def z136 : W := mkw 0x0a80000000000000 0x002a000000000000 0x0f80000000000000 0x3c3e000000000000

def z137 : W := mkw 0x0b84364400000000 0x002e10d910000000 0x6fde3fe700000003 0xfdbf78ff9c000000

def z138 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbc803f00c303fc31 0x92f200fc030c0ff0

def z139 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc4038e0c073c03d 0x9ef100e38301cf00

def z140 : W := mkw 0x0010400021840001 0x8000410000861000 0x00b1c000238c0014 0x7402c700008e3000

def z141 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x405e24e700f33322 0xc10178939c03cccc

def z142 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0x004000e000700000 0x000100038001c000

def z143 : W := mkw 0x000008b0001142a0 0x20000022c000450a 0xa02038f8008fc3f7 0xd68080e3e0023f0f

def z144 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc6038f8c07fc0d9 0x1af180e3e301ff03

def z145 : W := mkw 0x401200212cb33301 0x1100480084b2cccc 0x000000003cf3332c 0x0000000000f3cccc

def z146 : W := mkw 0x1ee94000d34c0006 0x807ba500034d3000 0x1fa1c000ff0c001c 0x3c7e870003fc3000

def z147 : W := mkw 0x3fff7ed4fbec002f 0x80fffdfb53efb000 0x7ffff8e0fffc001c 0x7dffffe383fff000

def z148 : W := mkw 0x0b80360000000000 0x002e00d800000000 0xbf803f00c003c03d 0xbefe00fc03000f00

def z149 : W := mkw 0x4b9636652cb33301 0x112e58d994b2cccc 0x6fde3fe73cf3332f 0xfdbf78ff9cf3cccc

def z150 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000000000035 0x9600000000000000

def z151 : W := mkw 0x0000000000000000 0x0000000000000000 0x00200018008c03c2 0x400080006002300f

def z152 : W := mkw 0x0000000000000000 0x0000000000000000 0x8080070023003c35 0xb602001c008c00f0

def z153 : W := mkw 0x0a80120000000000 0x002a004800000000 0x2c801b0000000001 0x10b2006c00000000

def z154 : W := mkw 0x0116244428a00001 0x0004589110a28000 0x435e24e73cf0000e 0xed0d78939cf3c000

def z155 : W := mkw 0x0fe03eb0d65beaa6 0x603f80fac3596faa 0xbf6038f8dcffc3ff 0xdefd80e3e373ff0f

def z156 : W := mkw 0x0010000120801101 0x0000400004820044 0x0010040720803326 0xe40040101c8200cc

def z157 : W := mkw 0x147b48b069fd42a3 0xa051ed22c1a7f50a 0xfc7ff8f8c0ffc3ff 0xdff1ffe3e303ff0f

def z158 : W := mkw 0x0004004400000000 0x0000100110000000 0x405e00e700000002 0x410178039c000000

def z159 : W := mkw 0x2564bffe405942ba 0x209592fff901650a 0xbc603fffc0ffc3ff 0xdef180ffff03ff0f

def z160 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000040020003024 0xa4000010008000c0

def z161 : W := mkw 0x0460089000000020 0x0011802240000000 0xac6038f8008c03f7 0xdeb180e3e002300f

def z162 : W := mkw 0x0000002000110200 0x0000000080004408 0x806020f800ff03ff 0xde018083e003fc0f

def z163 : W := mkw 0x2fe9bf9a00000038 0x00bfa6fe68000000 0x2fa1ff1800000001 0xbcbe87fc60000000

def z164 : W := mkw 0x0ee9000000000000 0x003ba40000000000 0x4fffc00000000000 0x7d3fff0000000000

def z165 : W := mkw 0x1fe97600d74ea806 0xc07fa5d8035d3aa0 0xbfa1ff00ff0ffc3d 0xbefe87fc03fc3ff0

def z166 : W := mkw 0x4114e56f25973751 0x99045395bc965cdd 0x80b1e7ff238f3ff7 0xf602c79ffc8e3cff

def z167 : W := mkw 0x410624440c222000 0x1104189110308880 0x430e00001c000000 0x010c380000700000

def z168 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x0031c01f008c03c2 0x4000c7007c02300f

def z169 : W := mkw 0x2fed3ed400000028 0x00bfb4fb50000000 0x6fce3fe000000001 0xbdbf38ff80000000

def z170 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x434e20e03cf3332c 0x090d388380f3cccc

def z171 : W := mkw 0x400200200c332200 0x110008008030cc88 0x000000001c730008 0x000000000071cc00

def z172 : W := mkw 0x000008b0001142a0 0x20000022c000450a 0xa00038f80003c3e3 0x828000e3e0000f0f

def z173 : W := mkw 0x2b8db74e00000018 0x00ae36dd38000000 0x439fc70700000000 0x210e7f1c1c000000

def z174 : W := mkw 0x1efb4890fbec40a7 0xa07bed2243efb102 0xffffd818fffcc0dd 0x7fffff6063fff303

def z175 : W := mkw 0x0104244404022000 0x0004109110100880 0x435e24e73c03302e 0xed0d78939cf00cc0

def z176 : W := mkw 0x2fed3ed49602a82c 0x40bfb4fb52580aa0 0xffce3fe0ff03fc3d 0xbfff38ff83fc0ff0

def z177 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x8031c01f008c03f7 0xd600c7007c02300f

def z178 : W := mkw 0x1b9b7600bfa6a805 0xc06e6dd802fe9aa0 0xff9fff00ff03fc3d 0xbffe7ffc03fc0ff0

def z179 : W := mkw 0x1a9b4000bba40005 0x806a6d0002ee9000 0x43dfc0003ff0000c 0x6d0f7f0000ffc000

def z180 : W := mkw 0x1ffb7600ffeea807 0xc07fedd803ffbaa0 0xffffff00fffffc3d 0xfffffffc03fffff0

def z181 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0x3c6038f8c0ffc3ca 0x48f180e3e303ff0f

def z182 : W := mkw 0x0b907601b786bd45 0xc82e41d806de1af5 0xbf803f00ff8ffffd 0xbefe00fc03fe3fff

def z183 : W := mkw 0x457624656cfb3303 0x1115d89195b3eccc 0x5f7e24e7fcff333e 0xfd7df8939ff3fccc

def z184 : W := mkw 0x41162cf52cb373a1 0x310458b3d4b2cdce 0xe35e3cff3cf3f3ef 0xef8d78f3fcf3cfcf

def z185 : W := mkw 0x3fffffdefbec003f 0x80ffffff7befb000 0x7ffffffffffc001f 0xfdfffffffffff000

def z186 : W := mkw 0x0fe03eb0d65beaa6 0x603f80fac3596faa 0xbfc03fe0ff73fc3d 0xbeff00ff83fdcff0

def z187 : W := mkw 0x6fffffff2db73779 0x99bffffffcb6dcdd 0xefffffff3fff3fff 0xffbffffffcfffcff

def z188 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x0091c70723803f26 0xe402471c1c8e00fc

def z189 : W := mkw 0x3effc9defbec003f 0x80fbff277befb000 0x5fffc0fffffc001e 0x7d7fff03fffff000

def z190 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x0031c41f208c33e6 0xe400c7107c8230cf

def z191 : W := mkw 0x2ee99b9a00000038 0x00bba66e68000000 0x2ce1fbf800000003 0xdcb387efe0000000

def z192 : W := mkw 0x0b80360000000000 0x002e00d800000000 0x2f803f0000000001 0xbcbe00fc00000000

def z193 : W := mkw 0x0012000028a00001 0x0000480000a28000 0x000000003cf0000c 0x0000000000f3c000

def z194 : W := mkw 0x0ee9000000000000 0x003ba40000000000 0x4f4e000000000000 0x093d380000000000

def z195 : W := mkw 0x1eeb0000da680006 0x007bac000369a000 0x5f6e0000dcfc001c 0x5d7db8000373f000

def z196 : W := mkw 0x410624640c332200 0x110418919030cc88 0x434e20e01c730008 0x090d38838071cc00

def z197 : W := mkw 0x0a80000092000004 0x002a000002480000 0x038000003f000000 0x200e000000fc0000

def z198 : W := mkw 0x0000000040484082 0x2000000001012102 0x90000000c00cc0d0 0x0240000003003303

def z199 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x000024e73cf3332e 0x800000939cf3cccc

def z200 : W := mkw 0x000000009602a804 0x4000000002580aa0 0x90000000ff03fc3c 0x0240000003fc0ff0

def z201 : W := mkw 0x1efbc10bfbec1557 0x887bef042fefb055 0x5fffc01ffffc03de 0x7d7fff007ffff00f

def z202 : W := mkw 0x246d89fe405942ba 0x2091b627f901650a 0x407fc0ff00fc03c2 0x4101ff03fc03f00f

def z203 : W := mkw 0x256dbfde00000038 0x0095b6ff78000000 0x607fffff00000003 0xc181fffffc000000

def z204 : W := mkw 0x0469000000000000 0x0011a40000000000 0x407fc00000000000 0x4101ff0000000000

def z205 : W := mkw 0x4000002104133300 0x1100000084104ccc 0x0000000000033320 0x0000000000000ccc

def z206 : W := mkw 0x2104bfde00000038 0x008412ff78000000 0x20b1ffff00000003 0xf482c7fffc000000

def z207 : W := mkw 0x4104244504023100 0x11041091141008c4 0x0000040700003000 0x000000101c0000c0

def z208 : W := mkw 0x0000810a00000010 0x0000020428000000 0x0091c70700000000 0x2002471c1c000000

def z209 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6f7ff8ff00000002 0x49bdffe3fc000000

def z210 : W := mkw 0x0a89000000000000 0x002a240000000000 0x439fc00000000000 0x210e7f0000000000

def z211 : W := mkw 0x5b9f6465bfb73305 0x916e7d9196fedccc 0x43dfe4e73ff3332e 0xed0f7f939cffcccc

def z212 : W := mkw 0x246d08d400000028 0x0091b42350000000 0x404e00e000000000 0x0101380380000000

def z213 : W := mkw 0x4104a56f04133750 0x19041295bc104cdd 0x800027ff00033fe3 0x8200009ffc000cff

def z214 : W := mkw 0x41042cf5041373a0 0x310410b3d4104dce 0xa0003cff0003f3e3 0x828000f3fc000fcf

def z215 : W := mkw 0x046008b000110220 0x00118022c0004408 0x2c6038f800f3032f 0xdcb180e3e003cc0c

def z216 : W := mkw 0x0010000120801101 0x0000400004820044 0x0010040720003000 0x200040101c8000c0

def z217 : W := mkw 0x0000810a00000010 0x0000020428000000 0x80b1c71f23003c37 0xf602c71c7c8c00f0

def z218 : W := mkw 0x4b963665beb3bb05 0x512e58d996faceec 0x7f5e3ce7fcf3f32e 0xedfd78f39ff3cfcc

def z219 : W := mkw 0x147bc10b69ec1553 0x8851ef042da7b055 0x407fc01f00fc03c2 0x4101ff007c03f00f

def z220 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0x3f803800ff03c01c 0x3cfe00e003fc0f00

def z221 : W := mkw 0x00000020d65bea86 0x6000000083596faa 0x90000000fffffffc 0x0240000003ffffff

def z222 : W := mkw 0x1efb48b0fbfd42a7 0xa07bed22c3eff50a 0x7ffff8e0ffffc01c 0x7dffffe383ffff00

def z223 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x0091c70723003c00 0x2002471c1c8c00f0

def z224 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0x3c4038e0c073c008 0x08f100e38301cf00

def z225 : W := mkw 0x2ffdffde21840039 0x80bff7ff78861000 0x6fffffff238c0017 0xfdbffffffc8e3000

def z226 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0x3f803f00dc03c009 0xbcfe00fc03700f00

def z227 : W := mkw 0x3fedffded34c003e 0x80ffb7ff7b4d3000 0x7fffffffc30c0013 0xfdffffffff0c3000

def z228 : W := mkw 0x0000810b00001550 0x080002042c000055 0x0000001f000003c2 0x000000007c00000f

def z229 : W := mkw 0x010036000402a800 0x400400d800100aa0 0xbc003f00c003fc3d 0x9ef000fc03000ff0

def z230 : W := mkw 0x04600890404840a2 0x2011802241012102 0xbc203818c00fc0fd 0x9ef080e063003f03

def z231 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fdfffe700000000 0x29bf7fff9c000000

def z232 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e24e73c733008 0x290d78939cf1ccc0

def z233 : W := mkw 0x04600890404840a2 0x2011802241012102 0x00200018000c00c0 0x0000800060003003

def z234 : W := mkw 0x010036000402a800 0x400400d800100aa0 0x0000070000003c00 0x0000001c000000f0

def z235 : W := mkw 0x046089bb405957f2 0x28118226ed01655f 0xbc603fffc0ffffff 0xdef180ffff03ffff

def z236 : W := mkw 0x0000002040594282 0x200000008101650a 0x904020e0c0ffc3fe 0xce4100838303ff0f

def z237 : W := mkw 0x0b80f70a9706ac54 0xc82e03dc2a5c1ab1 0xbfa1ff18ff0ffcfd 0xbefe87fc63fc3ff3

def z238 : W := mkw 0x0100240004022000 0x0004009000100880 0x030020001c030008 0x080c008000700c00

def z239 : W := mkw 0x0000810b00001550 0x080002042c000055 0x8000071f00003fe3 0x8200001c7c0000ff

def z240 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x8091c707238c3ff4 0x2202471c1c8e30ff

def z241 : W := mkw 0x5fffe56fffff3757 0x997fff95bffffcdd 0xdfffe7ffffff3fff 0xff7fff9ffffffcff

def z242 : W := mkw 0x1fff6444fbec0007 0x807ffd9113efb000 0x5fffe4e7fffc001e 0xfd7fff939ffff000

def z243 : W := mkw 0x4116246528b11301 0x1104589194a2c44c 0x435e24e700f00302 0xed0d78939c03c00c

def z244 : W := mkw 0x247dc9df21841579 0x8891f7277c861055 0x407fc0ff008c03c2 0x4101ff03fc02300f

def z245 : W := mkw 0x0000000000000000 0x0000000000000000 0xbc001800c000c011 0x12f0006003000300

def z246 : W := mkw 0x01003eb00413eaa0 0x600400fac0104faa 0xa0003ff80003ffe3 0x828000ffe0000fff

def z247 : W := mkw 0x0fe03600d64aa806 0x403f80d803592aa0 0xbfe03f00fffffc3d 0xfeff80fc03fffff0

def z248 : W := mkw 0x0010002120911301 0x000040008482444c 0x005024e720f3332e 0xec0140939c83cccc

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000070000003c21 0x8200001c000000f0

def z250 : W := mkw 0x3ffff74efbec001f 0x80ffffdd3befb000 0x5fffc707fffc001c 0x7d7fff1c1ffff000

def z251 : W := mkw 0x3ee9db9ad34c003e 0x80fba76e6b4d3000 0x3ca1db18c30c0011 0x10f2876c630c3000

def z252 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0xdfffc018fffc03ff 0xff7fff0063fff00f

def z253 : W := mkw 0x0000400001040000 0x8000010000041000 0x00a1c000030c0010 0x10028700000c3000

def z254 : W := mkw 0x2fed3ed400000028 0x00bfb4fb50000000 0x6f5e3ce700000002 0xedbd78f39c000000

def z255 : W := mkw 0x147b400069ec0003 0x8051ed0001a7b000 0x437fc0003cfc000c 0x6d0dff0000f3f000

def z256 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000000008c03f4 0x020000000002300f

def z257 : W := mkw 0x0000000000000000 0x0000000000000000 0x000020000003002c 0x8c00008000000c00

def z258 : W := mkw 0x3ffffffefbfd42bf 0xa0fffffffbeff50a 0xffffffffffffc3ff 0xffffffffffffff0f

def z259 : W := mkw 0x1a9b4000fbec0007 0x806a6d0003efb000 0x539fc000fffc001c 0x214e7f0003fff000

def z260 : W := mkw 0x0010c10bb786bd55 0xc80043042ede1af5 0x90b1c71fff8fffff 0xf642c71c7ffe3fff

def z261 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0x3f003c00fc03f02c 0xacfc00f003f00fc0

def z262 : W := mkw 0x1efbc10afbec0457 0x887bef042befb011 0xdfffc318fffc0cdd 0x7f7fff0c63fff033

def z263 : W := mkw 0x0000002000110200 0x0000000080004408 0x004020e000f3032e 0xcc0100838003cc0c

def z264 : W := mkw 0x45762cf56cfb73a3 0x3115d8b3d5b3edce 0xff7e3cfffcfff3ff 0xfffdf8f3fff3ffcf

def z265 : W := mkw 0x05642cf4405942a2 0x201590b3d101650a 0xff7e3cffc0ffc3ff 0xfffdf8f3ff03ff0f

def z266 : W := mkw 0x410624650c333300 0x110418919430cccc 0x434e24e71c73332a 0x890d38939c71cccc

def z267 : W := mkw 0x447608f568f953a3 0x3111d823d5a3e54e 0x407e00ff00fc03c2 0x4101f803fc03f00f

def z268 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x8031c71f008c3fe3 0xc200c71c7c0230ff

def z269 : W := mkw 0x246d89fe405942ba 0x2091b627f901650a 0xfc7ff8ffc0ffc3ff 0xdff1ffe3ff03ff0f

def z270 : W := mkw 0x1a9bc10bbba41555 0x886a6f042eee9055 0x439fc7073f003c00 0x210e7f1c1cfc00f0

def z271 : W := mkw 0x0fe03e909602a824 0x403f80fa42580aa0 0xbfe03ff8ff03fc3f 0xfeff80ffe3fc0ff0

def z272 : W := mkw 0x0ee9000092000004 0x003ba40002480000 0x5fffc000ff00001c 0x7d7fff0003fc0000

def z273 : W := mkw 0x0000c10a01040450 0x8800030428041011 0x80a1c718230c3cf5 0xb602871c608c30f3

def z274 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5f7fc000dcfc0008 0x497dff000373f000

def z275 : W := mkw 0x0a90c10bb3841555 0x882a43042ece1055 0x9fb1c71fff8c3fff 0xfe7ec71c7ffe30ff

def z276 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040000000f0000c 0x4c0100000003c000

def z277 : W := mkw 0x0460089000000020 0x0011802240000000 0x006000f800000002 0x40018003e0000000

def z278 : W := mkw 0x547f406569fd1303 0x9151fd0195a7f44c 0x407fc0e700fc0302 0x4101ff039c03f00c

def z279 : W := mkw 0x45642cf5445b73a2 0x311590b3d5116dce 0xbc603cffc0fff3ff 0xdef180f3ff03ffcf

def z280 : W := mkw 0x0000000000000000 0x0000000000000000 0xbc803f00e303fc3d 0xbef200fc038c0ff0

def z281 : W := mkw 0x4b8436659613bb04 0x512e10d996584eec 0xbf803fe7ff03ff3f 0xbefe00ff9ffc0ffc

def z282 : W := mkw 0x1ee94000d34c0006 0x807ba500034d3000 0x5fffc000c30c0010 0x7d7fff00030c3000

def z283 : W := mkw 0x0012400029a40001 0x8000490000a69000 0x43ffc0003ffc001c 0x7d0fff0000fff000

def z284 : W := mkw 0x0fed244400000000 0x003fb49110000000 0x4fffe4e700000002 0xfd3fff939c000000

def z285 : W := mkw 0x2b8d364400000008 0x00ae34d910000000 0x430e000000000000 0x010c380000000000

def z286 : W := mkw 0x0010c10a21840011 0x8000430428861000 0x00b1c71f238c0017 0xf402c71c7c8e3000

def z287 : W := mkw 0x0a80000092000004 0x002a000002480000 0xbf803800ff03c03d 0xbefe00e003fc0f00

def z288 : W := mkw 0x1feb3600de6aa806 0x407facd80379aaa0 0x7f4e3800dc73c008 0x09fd38e00371cf00

def z289 : W := mkw 0x0000002000110200 0x0000000080004408 0xbc4038e0c0f3c33f 0xdef100e38303cf0c

def z290 : W := mkw 0x0000c10a01040450 0x8800030428041011 0x80a1c318030c0cd1 0x1202870c600c3033

def z291 : W := mkw 0x2fedb74e00000018 0x00bfb6dd38000000 0x4fffc70700000000 0x7d3fff1c1c000000

def z292 : W := mkw 0x0460089040480022 0x0011802241012000 0x3c6038f8c0fc001f 0xdcf180e3e303f000

def z293 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e20e71cf3030a 0x490d78839c73cc0c

def z294 : W := mkw 0x0ee01ab0d259caa6 0x603b806ac349672a 0xbce03bf8c3ffcfff 0xdef380efe30fff3f

def z295 : W := mkw 0x0010400121841101 0x8000410004861044 0x00b1c407238c3336 0xf402c7101c8e30cc

def z296 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000023003c34 0x02000000008c00f0

def z297 : W := mkw 0x5fff6cf5ffff73a7 0xb17ffdb3d7fffdce 0xfffffcfffffff3ff 0xfffffff3ffffffcf

def z298 : W := mkw 0x0ee9000000000000 0x003ba40000000000 0x0ca1c00000000000 0x1032870000000000

def z299 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fdfc000ff700008 0x297f7f0003fdc000

def z300 : W := mkw 0x0000000000000000 0x0000000000000000 0xbc203818c08fc3ff 0xdef080e063023f0f

def z301 : W := mkw 0x0010400021840001 0x8000410000861000 0x80b1c018238c03f7 0xf602c700608e300f

def z302 : W := mkw 0x0a80120092008804 0x402a004802480220 0xbf801b00ff00cc1d 0x3efe006c03fc0330

def z303 : W := mkw 0x1eeb0000da680006 0x007bac000369a000 0x5fffc000dc700008 0x7d7fff000371c000

def z304 : W := mkw 0x0012000028a00001 0x0000480000a28000 0x431e00003c000000 0x210c780000f00000

def z305 : W := mkw 0x1ffb7600ffeea807 0xc07fedd803ffbaa0 0x7ffff800ffffc01c 0x7dffffe003ffff00

def z306 : W := mkw 0x047008b160d953a3 0x2011c022c583654e 0xbc703cffe0fff3ff 0xfef1c0f3ff83ffcf

def z307 : W := mkw 0x0100240000000000 0x0004009000000000 0x0300240000000000 0xac0c009000000000

def z308 : W := mkw 0x256dadde00000038 0x0095b6b778000000 0x437fe4ff00000002 0xed0dff93fc000000

def z309 : W := mkw 0x6b9fb74f2ca23119 0x11ae7edd3cb288c4 0x439fc7073c003000 0x210e7f1c1cf000c0

def z310 : W := mkw 0x411624642cb32201 0x1104589190b2cc88 0x435e20e03cf3000c 0x6d0d788380f3cc00

def z311 : W := mkw 0x1a89400093040004 0x806a2500024c1000 0x0081c00003000000 0x00020700000c0000

def z312 : W := mkw 0x1b927600ffeea807 0xc06e49d803ffbaa0 0xbf803f00fffffc3d 0xbefe00fc03fffff0

def z313 : W := mkw 0x5efb4021ffff3307 0x917bed0087fffccc 0x5fffc000ffff333c 0x7d7fff0003fffccc

def z314 : W := mkw 0x0010c10b21841551 0x880043042c861055 0xbcb1ff1fe38fffff 0xfef2c7fc7f8e3fff

def z315 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z316 : W := mkw 0x1efb4001fbec1107 0x807bed0007efb044 0x5fffc407fffc333e 0xfd7fff101ffff0cc

def z317 : W := mkw 0x147b48b069fd42a3 0xa051ed22c1a7f50a 0x407fc0f800fc03c2 0x4101ff03e003f00f

def z318 : W := mkw 0x1efbc10bfbec1557 0x887bef042fefb055 0x5fffc707fffc3c1c 0x7d7fff1c1ffff0f0

def z319 : W := mkw 0x4016004528a01101 0x1100580114a28044 0x401e000700000000 0x010078001c000000

def z320 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0x806000f800fc03f7 0xd6018003e003f00f

def z321 : W := mkw 0x1b9b7600bfa6a805 0xc06e6dd802fe9aa0 0x439fc7003f003c00 0x210e7f1c00fc00f0

def z322 : W := mkw 0x2fedbfde9200883c 0x40bfb6ff7a480220 0xffffffffc300cc13 0xffffffffff0c0330

def z323 : W := mkw 0x0000c10a01040450 0x8800030428041011 0x0081c30003000c00 0x0002070c000c0030

def z324 : W := mkw 0x0000c10a01040450 0x8800030428041011 0x0021c018000c00c0 0x0000870060003003

def z325 : W := mkw 0x047048b061dd42a3 0xa011c122c187750a 0xbcf1f8f8e3ffc3ff 0xfef3c7e3e38fff0f

def z326 : W := mkw 0x4116e54f2da63551 0x99045b953cb698d5 0x439fc7073f003c00 0x210e7f1c1cfc00f0

def z327 : W := mkw 0x1a9b4000bba40005 0x806a6d0002ee9000 0x5f9fc000ff00001c 0x3d7e7f0003fc0000

def z328 : W := mkw 0x1a924000fbec0007 0x806a490003efb000 0x1f800000fffc001c 0x3c7e000003fff000

def z329 : W := mkw 0x4006006408310200 0x110018019020c408 0x404e00e000700000 0x010138038001c000

def z330 : W := mkw 0x0ef9400021840001 0x803be50000861000 0x4fffc000238c0014 0x7d3fff00008e3000

def z331 : W := mkw 0x2fed3ef4405942aa 0x20bfb4fbd101650a 0xff6e38f8c0ffc3ff 0xdffdb8e3e303ff0f

def z332 : W := mkw 0x1eeb08b0da7942a6 0x207bac22c369e50a 0x7f4e38e0dc73c008 0x09fd38e38371cf00

def z333 : W := mkw 0x0a80000092000004 0x002a000002480000 0x1c800000c3000010 0x10720000030c0000

def z334 : W := mkw 0x0010400021840001 0x8000410000861000 0x0091c00023000000 0x20024700008c0000

def z335 : W := mkw 0x0000000000000000 0x0000000000000000 0x3c003800c003c008 0x08f000e003000f00

def z336 : W := mkw 0x147bc10b69ec1553 0x8851ef042da7b055 0xc0ffc71f23fc3ff7 0xf703ff1c7c8ff0ff

def z337 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0x3f803f00ff03fc08 0x28fe00fc03fc0ff0

def z338 : W := mkw 0x0a80120092008804 0x402a004802480220 0xbc803b00c303cc3d 0x9ef200ec030c0f30

def z339 : W := mkw 0x0012c10b29a41551 0x88004b042ca69055 0xc3ffc71f3ffc3fff 0xff0fff1c7cfff0ff

def z340 : W := mkw 0x0b8436449602a804 0x402e10d912580aa0 0xffde3fe7ff03fc3f 0xffff78ff9ffc0ff0

def z341 : W := mkw 0x0000c10a01040450 0x8800030428041011 0x80b1c71f030c0cd3 0xf602c71c7c0c3033

def z342 : W := mkw 0x0010400021840001 0x8000410000861000 0x0031c000008c0000 0x4000c70000023000

def z343 : W := mkw 0x1ee90000d2480006 0x007ba40003492000 0x1c000000c0000000 0x0070000003000000

def z344 : W := mkw 0x0000002040594282 0x200000008101650a 0x90200018c0ffc3ff 0xd64080006303ff0f

def z345 : W := mkw 0x0100360000000000 0x000400d800000000 0x20003f0000000001 0x808000fc00000000

def z346 : W := mkw 0x4012002128b11301 0x1100480084a2c44c 0x0000000000f00300 0x000000000003c00c

def z347 : W := mkw 0x2fedbfde404840ba 0x20bfb6ff79012102 0xffffffffc00cc0d3 0xffffffffff003303

def z348 : W := mkw 0x0fe03eb0405942a2 0x203f80fac101650a 0xbfe03ff8c0ffc3ff 0xfeff80ffe303ff0f

def z349 : W := mkw 0x2fffbfde28a00039 0x00bffeff78a28000 0x6fffffff3cf0000f 0xfdbffffffcf3c000

def z350 : W := mkw 0x2ffdffff61dd57fb 0xa8bff7fffd87755f 0xffffffffe3ffffff 0xffffffffff8fffff

def z351 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0x3c4038e0c0f3c32e 0xccf100e38303cf0c

def z352 : W := mkw 0x4114246524933301 0x1104509194924ccc 0x001024e720833326 0xe40040939c820ccc

def z353 : W := mkw 0x0000000004022000 0x0000000000100880 0x000000003c03302c 0x0000000000f00cc0

def z354 : W := mkw 0x247dc9df21841579 0x8891f7277c861055 0xc0ffc7ff238c3ff7 0xf703ff1ffc8e30ff

def z355 : W := mkw 0x2fedffde01040478 0x88bfb7ff78041011 0xefffffff030c0cd3 0xffbffffffc0c3033

def z356 : W := mkw 0x0000c10b01041550 0x880003042c041055 0x80a1c71f030c3ff3 0x9202871c7c0c30ff

def z357 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x43ffc7ff00000002 0x610fff1ffc000000

def z358 : W := mkw 0x05642cd400000020 0x001590b350000000 0x6f7e3cff00000003 0xfdbdf8f3fc000000

def z359 : W := mkw 0x2fe9bf9a9602a83c 0x40bfa6fe6a580aa0 0xbfa1ff18ff03fc3d 0xbefe87fc63fc0ff0

def z360 : W := mkw 0x0b80360092008804 0x402e00d802480220 0xbf803f00c300cc11 0xbefe00fc030c0330

def z361 : W := mkw 0x0460000000000000 0x0011800000000000 0x0c60000000000000 0x5c31800000000000

def z362 : W := mkw 0x411624452ca23101 0x1104589114b288c4 0x435e04073cf0300c 0x6d0d78101cf3c0c0

def z363 : W := mkw 0x0b90f70bb786bd55 0xc82e43dc2ede1af5 0xbf91ff07ff03fc3d 0xbefe47fc1ffc0ff0

def z364 : W := mkw 0x0010400021840001 0x8000410000861000 0x00000000238c0014 0x00000000008e3000

def z365 : W := mkw 0x0470c99b21841571 0x8811c3266c861055 0xacf1ffff238c3ff7 0xfeb3c7fffc8e30ff

def z366 : W := mkw 0x45762cf56cfb73a3 0x3115d8b3d5b3edce 0x7f5e3ce7fcf3f32e 0xedfd78f39ff3cfcc

def z367 : W := mkw 0x2ffdbfdf20801139 0x00bff6ff7c820044 0x6fffffff20803327 0xfdbffffffc8200cc

def z368 : W := mkw 0x1a9bc10bbba41555 0x886a6f042eee9055 0xc3bfc71f3f8c3ff7 0xf70eff1c7cfe30ff

def z369 : W := mkw 0x45662cf44c7b62a2 0x311598b3d131ed8a 0x7f4e38e0dc73c008 0x09fd38e38371cf00

def z370 : W := mkw 0x200489de00000038 0x0080122778000000 0x000000ff00000002 0x00000003fc000000

def z371 : W := mkw 0x0470c9bb61dd57f3 0xa811c326ed87755f 0x80f1c7ff23fc3ff7 0xf603c71ffc8ff0ff

def z372 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc6018f8c0fcc3d3 0x52f18063e303f30f

def z373 : W := mkw 0x0a90d30bb3849d55 0xc82a434c2ece1275 0xbcb1df1fe38cfff7 0xf6f2c77c7f8e33ff

def z374 : W := mkw 0x6fffbfff28b11339 0x11bffefffca2c44c 0x6fffffff00f00303 0xfdbffffffc03c00c

def z375 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0xdfffc700fffc3c3d 0xff7fff1c03fff0f0

def z376 : W := mkw 0x40120021beb3bb05 0x5100480086faceec 0x90000000fff3ff3c 0x0240000003ffcffc

def z377 : W := mkw 0x0000002040594282 0x200000008101650a 0x10000000c073c008 0x004000000301cf00

def z378 : W := mkw 0x410624640c332200 0x110418919030cc88 0x435e24e71c73000a 0xed0d78939c71cc00

def z379 : W := mkw 0x0012002028b10201 0x0000480080a2c408 0x435e20e03cf3032e 0xed0d788380f3cc0c

def z380 : W := mkw 0x000008b0001142a0 0x20000022c000450a 0x200038e00003c000 0x008000e380000f00

def z381 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbfa03f18ff8fffff 0xfefe80fc63fe3fff

def z382 : W := mkw 0x41162465beb3bb05 0x5104589196faceec 0xd35e24e7fff3ff3e 0xef4d78939fffcffc

def z383 : W := mkw 0x4012c12b2db73751 0x99004b04acb6dcdd 0x80b1c71f3fff3fff 0xf602c71c7cfffcff

def z384 : W := mkw 0x0100b70b0402bd50 0x480402dc2c100af5 0xa0003f1f0003ffe3 0x828000fc7c000fff

def z385 : W := mkw 0x0010c12b21951751 0x88004304ac86545d 0x80f1e7ff23ff3fff 0xfe03c79ffc8ffcff

def z386 : W := mkw 0x1ee95200d34c8806 0xc07ba548034d3220 0xbca1db00c30ccc11 0x12f2876c030c3330

def z387 : W := mkw 0x046008b0001142a0 0x20118022c000450a 0xac6038f80003c3e3 0xdeb180e3e0000f0f

def z388 : W := mkw 0x20009b9a00000038 0x0080026e68000000 0x20001b1800000001 0x0080006c60000000

def z389 : W := mkw 0x0460000040480002 0x0011800001012000 0x9c600018c0fc03ff 0xde7180006303f00f

def z390 : W := mkw 0x1feb3600de6aa806 0x407facd80379aaa0 0xffce3f00ff73fc3d 0xbfff38fc03fdcff0

def z391 : W := mkw 0x2469899a00000038 0x0091a62668000000 0x0021c01800000000 0x0000870060000000

def z392 : W := mkw 0x0000002000110200 0x0000000080004408 0x004020e000730008 0x080100838001cc00

def z393 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0xff5e3ce7fcf3f33f 0xfffd78f39ff3cfcc

def z394 : W := mkw 0x0100240004022000 0x0004009000100880 0xbf003c00fc03f03d 0xbefc00f003f00fc0

def z395 : W := mkw 0x4b963645bea2b905 0x512e58d916fa8ae4 0x439e07073f003c00 0x210e781c1cfc00f0

def z396 : W := mkw 0x4116a56f2cb33311 0x11045a95bcb2cccc 0x43ffe7ff3cf3332f 0xfd0fff9ffcf3cccc

def z397 : W := mkw 0x0ee00000d2480006 0x003b800003492000 0x1fe00000fffc001c 0x7c7f800003fff000

def z398 : W := mkw 0x0100240004022000 0x0004009000100880 0x030004003c003000 0x200c001000f000c0

def z399 : W := mkw 0x2564bfde00000038 0x009592ff78000000 0x2c603fff00000003 0xdcb180fffc000000

def z400 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x0011c00700000000 0x000047001c000000

def z401 : W := mkw 0x4b8636649e33aa04 0x512e18d99278cea8 0x7f4e38e0dc73c008 0x09fd38e38371cf00

def z402 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00038000003c021 0x828000e000000f00

def z403 : W := mkw 0x0b80b70b9602bd54 0x482e02dc2e580af5 0xbf803f1fff03ffff 0xbefe00fc7ffc0fff

def z404 : W := mkw 0x447608f568f953a3 0x3111d823d5a3e54e 0xfc7e38ffc0ffc3ff 0xdff1f8e3ff03ff0f

def z405 : W := mkw 0x010024009602a804 0x4004009002580aa0 0x93002400ff03fc3c 0xae4c009003fc0ff0

def z406 : W := mkw 0x1ee94890d34c40a6 0xa07ba522434d3102 0xbca1d818c30cc0d1 0x12f28760630c3303

def z407 : W := mkw 0x0472000068e80003 0x0011c80001a3a000 0x5f7e0000fcfc001c 0x7d7df80003f3f000

def z408 : W := mkw 0x0b80360004022000 0x002e00d800100880 0x2f803f003c03302d 0xbcbe00fc00f00cc0

def z409 : W := mkw 0x0010402161dd57c3 0xa80041008587755f 0x90000000e3fffffc 0x02400000038fffff

def z410 : W := mkw 0x401240212db73741 0x9900490084b6dcdd 0x800000003fff3ffc 0x0200000000fffcff

def z411 : W := mkw 0x2fed3ef4405942aa 0x20bfb4fbd101650a 0x7f4e38e0c073c008 0x09fd38e38301cf00

def z412 : W := mkw 0x0110f70b2586bd51 0xc80443dc2c961af5 0xa0b1ff1f238ffff7 0xf682c7fc7c8e3fff

def z413 : W := mkw 0x200d814e00000018 0x0080360538000000 0x401fc00700000000 0x01007f001c000000

def z414 : W := mkw 0x000008b0405942a2 0x20000022c101650a 0xb00038f8c0ffc3ff 0x82c000e3e303ff0f

def z415 : W := mkw 0x0b923600bea2a805 0x402e48d802fa8aa0 0xffde3f00fff3fc3d 0xffff78fc03ffcff0

def z416 : W := mkw 0x0010810b20801111 0x000042042c820044 0x00b1c71f20803327 0xf402c71c7c8200cc

def z417 : W := mkw 0x411664652db73741 0x9904599194b6dcdd 0xc35e24e73fff3ffe 0xef0d78939cfffcff

def z418 : W := mkw 0x0ff0ffbbf7dffff7 0xe83fc3feefdf7fff 0xbff1ffffffffffff 0xfeffc7ffffffffff

def z419 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fbfc000ff0c0010 0x317eff0003fc3000

def z420 : W := mkw 0x2b9df74f21841559 0x88ae77dd3c861055 0xc3bfc71f238c3ff7 0xf70eff1c7c8e30ff

def z421 : W := mkw 0x1012400069ec0003 0x8040490001a7b000 0x0000000000fc0000 0x000000000003f000

def z422 : W := mkw 0x6fedbfff04133338 0x11bfb6fffc104ccc 0x6fffffff00033323 0xfdbffffffc000ccc

def z423 : W := mkw 0x1ffbf70bffeebd57 0xc87fefdc2fffbaf5 0xffffff1fffffffff 0xfffffffc7fffffff

def z424 : W := mkw 0x1efb48b0fbfd42a7 0xa07bed22c3eff50a 0x5fffc0f8fffc03de 0x7d7fff03e3fff00f

def z425 : W := mkw 0x046008b0d65beaa6 0x60118022c3596faa 0xbc6038f8ffffffff 0xdef180e3e3ffffff

def z426 : W := mkw 0x410436650413bb00 0x510410d994104eec 0xa0003fe70003ff23 0x828000ff9c000ffc

def z427 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbf003800ff03fc3c 0x0afc00e003fc0ff0

def z428 : W := mkw 0x6fff3ef52cb33329 0x11bffcfbd4b2cccc 0x6f5e3ce73cf3332e 0xedbd78f39cf3cccc

def z429 : W := mkw 0x0010c9bb219557f1 0xa8004326ec86555f 0xa0b1ffff238ffff7 0xf682c7fffc8e3fff

def z430 : W := mkw 0x0460089000000020 0x0011802240000000 0xbc6038f8c003c03f 0xdef180e3e3000f00

def z431 : W := mkw 0x0010400121841541 0x8800410004861055 0x80800700238c3ff5 0xb602001c008e30ff

def z432 : W := mkw 0x147248b0fbfd42a7 0xa051c922c3eff50a 0xbc6038f8ffffc3ff 0xdef180e3e3ffff0f

def z433 : W := mkw 0x6fef3ef40c332228 0x11bfbcfbd030cc88 0x6f4e38e01c730008 0x09bd38e38071cc00

def z434 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010040700000002 0xe40040101c000000

def z435 : W := mkw 0x0460c9ba415d46f2 0xa8118326e905751b 0xbce1fbf8c3ffcfff 0xdef387efe30fff3f

def z436 : W := mkw 0x04600890404840a2 0x2011802241012102 0xbc201818c08cc3f7 0xd6f080606302330f

def z437 : W := mkw 0x000008b0001142a0 0x20000022c000450a 0x000000f8000003c2 0x00000003e000000f

def z438 : W := mkw 0x0104244400000000 0x0004109110000000 0x431e040700000000 0x210c78101c000000

def z439 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbf003f00dc03fc29 0x8afc00fc03700ff0

def z440 : W := mkw 0x0000810a00000010 0x0000020428000000 0x0000071f00000003 0x8000001c7c000000

def z441 : W := mkw 0x5fff6464ffff2207 0x917ffd9193fffc88 0x5fffe0e0ffff001c 0x7d7fff8383fffc00

def z442 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x8091c71f23003fe3 0xa202471c7c8c00ff

def z443 : W := mkw 0x411624656cfb7383 0x3104589195b3edce 0xd35e24e7fcfff3fe 0xef4d78939ff3ffcf

def z444 : W := mkw 0x05602cb0445b62a2 0x201580b2c1116d8a 0xbf603cf8fcfff3ff 0xfefd80f3e3f3ffcf

def z445 : W := mkw 0x0114e54f21841551 0x880453953c861055 0xc3ffe7ff238c3ff7 0xff0fff9ffc8e30ff

def z446 : W := mkw 0x2ffdffdfb786bd7d 0xc8bff7ff7ede1af5 0xffffffffff8fffff 0xfffffffffffe3fff

def z447 : W := mkw 0x1eeb08b0da7942a6 0x207bac22c369e50a 0xff6e38f8dcffc3ff 0xdffdb8e3e373ff0f

def z448 : W := mkw 0x147b400069ec0003 0x8051ed0001a7b000 0x5c7fc000c0fc001c 0x5d71ff000303f000

def z449 : W := mkw 0x2fedbfde9200003c 0x00bfb6ff7a480000 0x7fffffffff00001f 0xfdfffffffffc0000

def z450 : W := mkw 0x010036009602a804 0x400400d802580aa0 0xb0003f00ff03fc3d 0x82c000fc03fc0ff0

def z451 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0x3c6038e0c0ffc01c 0x5cf180e38303ff00

def z452 : W := mkw 0x101b400029a40001 0x80406d0000a69000 0x401fc00000000000 0x01007f0000000000

def z453 : W := mkw 0x2fedbffe00110238 0x00bfb6fff8004408 0x6fffffff00f3032f 0xfdbffffffc03cc0c

def z454 : W := mkw 0x0000000100001100 0x0000000004000044 0x0000040700003322 0x800000101c0000cc

def z455 : W := mkw 0x2fedbfde0402a838 0x40bfb6ff78100aa0 0xefffffff0003fc23 0xffbffffffc000ff0

def z456 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000018000003e3 0x820000006000000f

def z457 : W := mkw 0x10124020fbfd4287 0xa040490083eff50a 0x90000000ffffc3fc 0x0240000003ffff0f

def z458 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x43ffc0003ffc0000 0x610fff0000fff000

def z459 : W := mkw 0x4b962465beb33305 0x112e589196facccc 0x5fde24e7fff3333e 0xfd7f78939fffcccc

def z460 : W := mkw 0x010036000402a800 0x400400d800100aa0 0xa3003f003c03fc2d 0xae8c00fc00f00ff0

def z461 : W := mkw 0x0010400121841541 0x8800410004861055 0x80100407238c3ff6 0xe60040101c8e30ff

def z462 : W := mkw 0x04600890404840a2 0x2011802241012102 0xbc6038f8c00cc0d3 0xdef180e3e3003303

def z463 : W := mkw 0x411624452ca23101 0x1104589114b288c4 0x431e24073c03302c 0xad0c78901cf00cc0

def z464 : W := mkw 0x000000009602a804 0x4000000002580aa0 0x000000003f003c00 0x0000000000fc00f0

def z465 : W := mkw 0x2b84bfde00000038 0x00ae12ff78000000 0x2f803fff00000003 0xbcbe00fffc000000

def z466 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x8000071f238c3ff7 0x8200001c7c8e30ff

def z467 : W := mkw 0x0000810b00001550 0x080002042c000055 0x80b1c71f00003fe3 0xf602c71c7c0000ff

def z468 : W := mkw 0x0100242004132200 0x0004009080104c88 0x034024e03cf3332e 0xec0d009380f3cccc

def z469 : W := mkw 0x2b84bfde9602a83c 0x40ae12ff7a580aa0 0xbf803fffff03fc3f 0xbefe00fffffc0ff0

def z470 : W := mkw 0x0a80000092000004 0x002a000002480000 0x9f800700ff003c3d 0xbe7e001c03fc00f0

def z471 : W := mkw 0x0460c99a414c44f2 0xa811832669053113 0xbca1db18c30cccd1 0x12f2876c630c3333

def z472 : W := mkw 0x410624640c332200 0x110418919030cc88 0x434e24e03c73302c 0xad0d389380f1ccc0

def z473 : W := mkw 0x5eff4065fbfd1307 0x917bfd0197eff44c 0x5fffc0e7fffc031e 0x7d7fff039ffff00c

def z474 : W := mkw 0x000089bb001157f0 0x28000226ec00455f 0xa0003fff0003ffe3 0x828000fffc000fff

def z475 : W := mkw 0x0010000020800001 0x0000400000820000 0x0010000020800004 0x6400400000820000

def z476 : W := mkw 0x0ee01a90d248c8a6 0x603b806a43492322 0xbca01b18c30cccd1 0x12f2806c630c3333

def z477 : W := mkw 0x0a8012009602a804 0x402a004802580aa0 0xbc801b00ff03fc3d 0x12f2006c03fc0ff0

def z478 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x40ffc7ff00000003 0xf503ff1ffc000000

def z479 : W := mkw 0x2ee91a9000000028 0x00bba46a40000000 0x2c00180000000000 0x00b0006000000000

def z480 : W := mkw 0x1ef94000f3cc0007 0x807be50003cf3000 0x1cb1c000e38c0014 0x7472c700038e3000

def z481 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0x006020f800ff03ee 0xcc018083e003fc0f

def z482 : W := mkw 0x5fff2465fefb3307 0x117ffc9197fbeccc 0x5f5e24e7fcf3332e 0xed7d78939ff3cccc

def z483 : W := mkw 0x0b803620d65bea86 0x602e00d883596faa 0xbf803f00fffffffd 0xbefe00fc03ffffff

def z484 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0x038027003f033c2c 0xac0e009c00fc0cf0

def z485 : W := mkw 0x1ee94000d34c0006 0x807ba500034d3000 0x1ce1c000c3fc001c 0x5c738700030ff000

def z486 : W := mkw 0x05603eb0445beaa2 0x601580fac1116faa 0xbc603ff8c0ffffff 0xdef180ffe303ffff

def z487 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x8031c01f238c3ff6 0x4200c7007c8e30ff

def z488 : W := mkw 0x411224212cb33301 0x1104489084b2cccc 0x030024003cf3332c 0xac0c009000f3cccc

def z489 : W := mkw 0x411664652db73301 0x9104599194b6dccc 0x43ffe4e73fff333e 0xfd0fff939cfffccc

def z490 : W := mkw 0x0010000120801101 0x0000400004820044 0x0000000020803324 0x00000000008200cc

def z491 : W := mkw 0x50124021ffff3307 0x9140490087fffccc 0x10000000ffff333c 0x0040000003fffccc

def z492 : W := mkw 0x0ee9810a00000010 0x003ba60428000000 0x4fffc71f00000003 0xfd3fff1c7c000000

def z493 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0x3c6038f8c073c00b 0xdcf180e3e301cf00

def z494 : W := mkw 0x0000810b00001550 0x080002042c000055 0x8020071f008c3ff7 0xd600801c7c0230ff

def z495 : W := mkw 0x401200216cfb7383 0x3100480085b3edce 0x90000000fcfff3fc 0x0240000003f3ffcf

def z496 : W := mkw 0x2b9df74f21841559 0x88ae77dd3c861055 0x439fc70723003c00 0x210e7f1c1c8c00f0

def z497 : W := mkw 0x0b803eb09613eaa4 0x602e00fac2584faa 0xbf803ff8ff03ffff 0xbefe00ffe3fc0fff

def z498 : W := mkw 0x0efb000028a00001 0x003bec0000a28000 0x4fffc0003cf0000c 0x7d3fff0000f3c000

def z499 : W := mkw 0x10020000da680006 0x004008000369a000 0x10000000dc700008 0x004000000371c000

def z500 : W := mkw 0x0470c9bb61dd57f3 0xa811c326ed87755f 0x0071c0ff00fc03c2 0x4001c703fc03f00f

def z501 : W := mkw 0x2b8db74e00000018 0x00ae36dd38000000 0x6f9fff0700000001 0xbdbe7ffc1c000000

def z502 : W := mkw 0x0104246400110200 0x0004109190004408 0x435e24e700f3032e 0xed0d78939c03cc0c

def z503 : W := mkw 0x0010000120801101 0x0000400004820044 0x8090070723803f37 0xf602401c1c8e00fc

def z504 : W := mkw 0x1ef9c10bf3cc1557 0x887be7042fcf3055 0x9cb1c71fe38c3ff7 0xf672c71c7f8e30ff

def z505 : W := mkw 0x010036000402a800 0x400400d800100aa0 0xa0803f002303fc35 0xb68200fc008c0ff0

def z506 : W := mkw 0x0460089000000020 0x0011802240000000 0x2c4038e000000000 0x08b100e380000000

def z507 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080070000000001 0xb402001c00000000

def z508 : W := mkw 0x3fefbfdeda68003e 0x00ffbeff7b69a000 0x7fffffffdc70000b 0xfdffffffff71c000

def z509 : W := mkw 0x0b907600b786a805 0xc02e41d802de1aa0 0xbfb1ff00ff8ffc3d 0xfefec7fc03fe3ff0

def z510 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5f4e0000fffc001c 0x097d380003fff000

def z511 : W := mkw 0x0a80120092008804 0x402a004802480220 0x3c001800c000c000 0x00f0006003000300

def z512 : W := mkw 0x2fedbffed65beabe 0x60bfb6fffb596faa 0xffffffffffffffff 0xffffffffffffffff

def z513 : W := mkw 0x147b4000fbec0007 0x8051ed0003efb000 0x507fc000fffc001c 0x4141ff0003fff000

def z514 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x00b1c71f008c03c3 0xf402c71c7c02300f

def z515 : W := mkw 0x4016c16f29b51751 0x99005b05bca6d45d 0xc0ffc7ff23fc3ff7 0xf703ff1ffc8ff0ff

def z516 : W := mkw 0x411636652cb3bb01 0x510458d994b2ceec 0xe35e3fe73cf3ff2f 0xef8d78ff9cf3cffc

def z517 : W := mkw 0x3b9ff74ebba4001d 0x80ee7fdd3aee9000 0x439fc7073f000000 0x210e7f1c1cfc0000

def z518 : W := mkw 0x10124000fbec0007 0x8040490003efb000 0x535e0000fffc001c 0x6d4d780003fff000

def z519 : W := mkw 0x000000009602a804 0x4000000002580aa0 0x90800700ff03fc3d 0xb642001c03fc0ff0

def z520 : W := mkw 0x2fedbfde4048003a 0x00bfb6ff79012000 0x7fffffffc0fc001f 0xfdffffffff03f000

def z521 : W := mkw 0x1efb400069ec0003 0x807bed0001a7b000 0x4fffc00000fc0000 0x7d3fff000003f000

def z522 : W := mkw 0x0460002040594282 0x201180008101650a 0x9c600000c0ffc3fc 0x5e7180000303ff0f

def z523 : W := mkw 0x401200212cb33301 0x1100480084b2cccc 0x435e00003cf3332c 0x6d0d780000f3cccc

def z524 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0x030000001c000000 0x000c000000700000

def z525 : W := mkw 0x0b80360000000000 0x002e00d800000000 0xaf803f0023003c35 0xbebe00fc008c00f0

def z526 : W := mkw 0x0ef9c10b21841551 0x883be7042c861055 0xcfffc71f238c3ff7 0xff3fff1c7c8e30ff

def z527 : W := mkw 0x0000000000000000 0x0000000000000000 0x00b1c00000000000 0x7402c70000000000

def z528 : W := mkw 0x0000810a00000010 0x0000020428000000 0x00a1c31800000001 0x1002870c60000000

def z529 : W := mkw 0x0114244520801101 0x0004509114820044 0x435e24e720803326 0xed0d78939c8200cc

def z530 : W := mkw 0x4b8636649e33aa04 0x512e18d99278cea8 0xffce3fe0ff73fc3d 0xbfff38ff83fdcff0

def z531 : W := mkw 0x2ee99b9a00000038 0x00bba66e68000000 0x6fffdb1800000001 0x7dbfff6c60000000

def z532 : W := mkw 0x2fed3ed400000028 0x00bfb4fb50000000 0x6f6e38f800000003 0xddbdb8e3e0000000

def z533 : W := mkw 0x10124001fbec1547 0x8840490007efb055 0x90000000fffc3ffc 0x0240000003fff0ff

def z534 : W := mkw 0x3fffffdebba4003d 0x80ffffff7aee9000 0x6fffffff3f000003 0xfdbffffffcfc0000

def z535 : W := mkw 0x6fffbfdf2ca23139 0x11bffeff7cb288c4 0x6fffffff3c003003 0xfdbffffffcf000c0

def z536 : W := mkw 0x411624452ca23101 0x1104589114b288c4 0x431e04073c803326 0xe50c78101cf200cc

def z537 : W := mkw 0x046089ba405942b2 0x20118226e901650a 0xbcf1ffffc0ffc3ff 0xfef3c7ffff03ff0f

def z538 : W := mkw 0x401200212cb33301 0x1100480084b2cccc 0x001004073cf3332e 0xe40040101cf3cccc

def z539 : W := mkw 0x000008b0001142a0 0x20000022c000450a 0xbc0038f8c003c3ff 0x9ef000e3e3000f0f

def z540 : W := mkw 0x2ee99b9a9200883c 0x40bba66e6a480220 0xbca1db18c300cc11 0x12f2876c630c0330

def z541 : W := mkw 0x0ee908b0405942a2 0x203ba422c101650a 0xfffff8f8c0ffc3ff 0xffffffe3e303ff0f

def z542 : W := mkw 0x0002000008200000 0x0000080000208000 0x434e00001c700008 0x090d38000071c000

def z543 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x00b1c707238c3c14 0x7402c71c1c8e30f0

def z544 : W := mkw 0x0b80b70a00000010 0x002e02dc28000000 0x2fb1ff1f00000003 0xfcbec7fc7c000000

def z545 : W := mkw 0x6fffbfffbeb3bb3d 0x51bffefffefaceec 0xfffffffffff3ff3f 0xffffffffffffcffc

def z546 : W := mkw 0x4b923621beb3bb05 0x512e48d886faceec 0xbf803f00fff3ff3d 0xbefe00fc03ffcffc

def z547 : W := mkw 0x0b80240096022004 0x002e009002580880 0x1f802400ff03303c 0xbc7e009003fc0cc0

def z548 : W := mkw 0x0010c10a21840451 0x8800430428861011 0x80b1c318238c0cd5 0x7602c70c608e3033

def z549 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080000023000014 0x34020000008c0000

def z550 : W := mkw 0x4116e56f2db73751 0x99045b95bcb6dcdd 0x437fe4ff3cff33ee 0xed0dff93fcf3fccf

def z551 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbf803b00df03cc19 0x1afe00ec037c0f30

def z552 : W := mkw 0x1efb0000fae80007 0x007bec0003eba000 0x5f5e0000fcf0000c 0x6d7d780003f3c000

def z553 : W := mkw 0x0a80120092008804 0x402a004802480220 0xbc801f00e300fc35 0xb6f2007c038c03f0

def z554 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0x906000f8c0ffc3fe 0x42418003e303ff0f

def z555 : W := mkw 0x0000000000000000 0x0000000000000000 0x00200000008c0014 0x5400800000023000

def z556 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c00380000000001 0x9cb000e000000000

def z557 : W := mkw 0x0010400121841541 0x8800410004861055 0x80b1c000238c3ff4 0x7602c700008e30ff

def z558 : W := mkw 0x0010810b20801551 0x080042042c820055 0x8010071f20803fe7 0xe600401c7c8200ff

def z559 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0x1f800700ff003c1c 0x3c7e001c03fc00f0

def z560 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x80a1c318238c3ff5 0x1202870c608e30ff

def z561 : W := mkw 0x2ffdffdf21841579 0x88bff7ff7c861055 0x6fffffff008c03c3 0xfdbffffffc02300f

def z562 : W := mkw 0x1efb4020fbfd0207 0x807bed0083eff408 0x5fffe0e0ffff033e 0xfd7fff8383fffc0c

def z563 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0x838007003f003c35 0xb60e001c00fc00f0

def z564 : W := mkw 0x0fe03e9000000020 0x003f80fa40000000 0x2fe03ff800000003 0xfcbf80ffe0000000

def z565 : W := mkw 0x2104bfdf00001578 0x088412ff7c000055 0xa0003fff00003fe3 0x828000fffc0000ff

def z566 : W := mkw 0x000000009602a804 0x4000000002580aa0 0xbc003800ff03fc3d 0x9ef000e003fc0ff0

def z567 : W := mkw 0x0470c9bb61dd57f3 0xa811c326ed87755f 0xbc71f8ffc0ffc3ff 0xdef1c7e3ff03ff0f

def z568 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0x2f803f003f003c01 0xbcbe00fc00fc00f0

def z569 : W := mkw 0x0a8000009602a804 0x402a000002580aa0 0x9f800000ff03fc3c 0x3e7e000003fc0ff0

def z570 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbce03ff8e3ffffff 0xfef380ffe38fffff

def z571 : W := mkw 0x5fff6445ffee3107 0x917ffd9117ffb8c4 0x5fffc407fffc301c 0x7d7fff101ffff0c0

def z572 : W := mkw 0x3fef3ed4da68002e 0x00ffbcfb5369a000 0x7f4e38e0dc700008 0x09fd38e38371c000

def z573 : W := mkw 0x0000400001040440 0x8800010000041011 0x80000000030c0cd0 0x02000000000c3033

def z574 : W := mkw 0x51166465ffff3307 0x9144599197fffccc 0x535e24e7ffff333e 0xed4d78939ffffccc

def z575 : W := mkw 0x0a80000092000004 0x002a000002480000 0x1f000000dc000008 0x087c000003700000

def z576 : W := mkw 0x010036000402a800 0x400400d800100aa0 0x200038000003c000 0x008000e000000f00

def z577 : W := mkw 0x2ee99b9a404840ba 0x20bba66e69012102 0xbca1db18c00cc0d1 0x12f2876c63003303

def z578 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0xefffffff008c03f7 0xffbffffffc02300f

def z579 : W := mkw 0x0460000040480002 0x0011800001012000 0x1c200000c00c0010 0x1070800003003000

def z580 : W := mkw 0x2a89930a00000018 0x00aa264c28000000 0x0081c30000000000 0x0002070c00000000

def z581 : W := mkw 0x401200212cb33301 0x1100480084b2cccc 0x004020e03cf3332e 0xcc01008380f3cccc

def z582 : W := mkw 0x0000000000000000 0x0000000000000000 0x90000000c003c03c 0x0240000003000f00

def z583 : W := mkw 0x0b90f70b21841551 0x882e43dc2c861055 0xafb1ff1f238c3ff7 0xfebec7fc7c8e30ff

def z584 : W := mkw 0x0000000000000000 0x0000000000000000 0x80a00718238c3ff7 0xf602801c608e30ff

def z585 : W := mkw 0x000000000402a800 0x4000000000100aa0 0x800000000003fc20 0x0200000000000ff0

def z586 : W := mkw 0x557f64656dff3303 0x9155fd9195b7fccc 0x437fe4e73cff332e 0xed0dff939cf3fccc

def z587 : W := mkw 0x447208b16cfb73a3 0x3111c822c5b3edce 0xbc6038f8fcfff3ff 0xdef180e3e3f3ffcf

def z588 : W := mkw 0x0000002000110200 0x0000000080004408 0x0000000000f3032c 0x000000000003cc0c

def z589 : W := mkw 0x4116e54f2da63551 0x99045b953cb698d5 0xc3bfc71f3f8c3ff7 0xf70eff1c7cfe30ff

def z590 : W := mkw 0x2fed3ed49602a82c 0x40bfb4fb52580aa0 0x7f4e38e0dc03c008 0x09fd38e383700f00

def z591 : W := mkw 0x45762cf52cb33321 0x1115d8b3d4b2cccc 0x6f7e3cff3cf3332f 0xfdbdf8f3fcf3cccc

def z592 : W := mkw 0x2ef9db9b21841579 0x88bbe76e6c861055 0xacb1df1f238c3ff7 0xf6b2c77c7c8e30ff

def z593 : W := mkw 0x0fe9360000000000 0x003fa4d800000000 0x6fffff0000000001 0xfdbffffc00000000

def z594 : W := mkw 0x0100240004022000 0x0004009000100880 0x0000240000033020 0x8000009000000cc0

def z595 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc2038f8c00fc3f3 0x92f080e3e3003f0f

def z596 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x431e04073cf3332c 0x210c78101cf3cccc

def z597 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x1ca1c000fffc001c 0x1072870003fff000

def z598 : W := mkw 0x4576edff6dff77f3 0xb915dbb7fdb7fddf 0xffffffffffffffff 0xffffffffffffffff

def z599 : W := mkw 0x0012000128a01101 0x0000480004a28044 0x435e04073cf0332e 0xed0d78101cf3c0cc

def z600 : W := mkw 0x0b8036209613aa04 0x402e00d882584ea8 0xbfc03fe0fff3ff3f 0xfeff00ff83ffcffc

def z601 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6feffbf800000001 0x19bfbfefe0000000

def z602 : W := mkw 0x347fc9de69ec003b 0x80d1ff2779a7b000 0x407fc0ff00fc0002 0x4101ff03fc03f000

def z603 : W := mkw 0x0010c12b61dd57d3 0xa8004304ad87755f 0x90b1c71fe3ffffff 0xf642c71c7f8fffff

def z604 : W := mkw 0x2ffdffdf21841579 0x88bff7ff7c861055 0x6fffffff23003c03 0xfdbffffffc8c00f0

def z605 : W := mkw 0x10124000fbec0007 0x8040490003efb000 0x10b1c000fffc001c 0x7442c70003fff000

def z606 : W := mkw 0x0460000040480002 0x0011800001012000 0x0060000000fc0000 0x400180000003f000

def z607 : W := mkw 0x0000000040480002 0x0000000001012000 0x10000000c0fc001c 0x004000000303f000

def z608 : W := mkw 0x0460089000000020 0x0011802240000000 0x2c20181800000001 0x10b0806060000000

def z609 : W := mkw 0x0000000092000004 0x0000000002480000 0x10000000ff00001c 0x0040000003fc0000

def z610 : W := mkw 0x0000000000000000 0x0000000000000000 0x8080030003000c11 0x1202000c000c0030

def z611 : W := mkw 0x011224002ca22001 0x0004489000b28880 0x435e24003cf3302c 0xed0d789000f3ccc0

def z612 : W := mkw 0x0a920000baa00005 0x002a480002ea8000 0x5fde0000fff0001c 0x7d7f780003ffc000

def z613 : W := mkw 0x0460899a00000030 0x0011822668000000 0x2cf1ffff00000003 0xfcb3c7fffc000000

def z614 : W := mkw 0x21043ed400000028 0x008410fb50000000 0x200038e000000000 0x008000e380000000

def z615 : W := mkw 0x4016c16f29b51751 0x99005b05bca6d45d 0x407fc0ff00fc03c2 0x4101ff03fc03f00f

def z616 : W := mkw 0x657fadff2cb33339 0x1195feb7fcb2cccc 0x437fe4ff3cf3332e 0xed0dff93fcf3cccc

def z617 : W := mkw 0x04600890404840a2 0x2011802241012102 0xbc601818c0fcc0dd 0x5ef180606303f303

def z618 : W := mkw 0x1efb4020fbfd4287 0xa07bed0083eff50a 0xdfffc000ffffc3fc 0x7f7fff0003ffff0f

def z619 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x80b1c31f038c0fd3 0x5202c70c7c0e303f

def z620 : W := mkw 0x4fff24652cb33301 0x113ffc9194b2cccc 0x4fffe4e73cf3332e 0xfd3fff939cf3cccc

def z621 : W := mkw 0x2ee99bba405942ba 0x20bba66ee901650a 0xbce1fbf8c0ffc3ff 0xdef387efe303ff0f

def z622 : W := mkw 0x3efbdb9afbec003f 0x80fbef6e6befb000 0x7fffdb18fffc001d 0x7dffff6c63fff000

def z623 : W := mkw 0x0470400061cc0003 0x8011c10001873000 0x1cf1c000e3fc001c 0x7c73c700038ff000

def z624 : W := mkw 0x4104246404132200 0x1104109190104c88 0x000020e000030000 0x0000008380000c00

def z625 : W := mkw 0x6fefbffe0c332238 0x11bfbefff830cc88 0x6fffffff1c73000b 0xfdbffffffc71cc00

def z626 : W := mkw 0x4b96f76fbfb7bf55 0xd92e5bddbefedefd 0xffffffffffffffff 0xffffffffffffffff

def z627 : W := mkw 0x1efbc10afbec0017 0x807bef042befb000 0x5fffc71ffffc001f 0xfd7fff1c7ffff000

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0x004020e000000002 0xcc01008380000000

def z629 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fbfdf1f00000001 0x31beff7c7c000000

def z630 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xa06038f800ffc3e3 0xc28180e3e003ff0f

def z631 : W := mkw 0x5fef2464de7b2206 0x117fbc919379ec88 0x5f4e20e0dc730008 0x097d38838371cc00

def z632 : W := mkw 0x2ee9db9a01040478 0x88bba76e68041011 0xaca1db18030c0cd1 0x12b2876c600c3033

def z633 : W := mkw 0x1efb4000bba40005 0x807bed0002ee9000 0x4fffc0003f000000 0x7d3fff0000fc0000

def z634 : W := mkw 0x146b000048680002 0x0051ac000121a000 0x404e000000700000 0x010138000001c000

def z635 : W := mkw 0x0000810b00001550 0x080002042c000055 0x8080071f23003ff7 0xb602001c7c8c00ff

def z636 : W := mkw 0x6116bfff2cb33339 0x11845afffcb2cccc 0x635e3fff3cf3332f 0xed8d78fffcf3cccc

def z637 : W := mkw 0x1012c10bfbec1557 0x88404b042fefb055 0x90b1c71ffffc3fff 0xf642c71c7ffff0ff

def z638 : W := mkw 0x0b8036000402a800 0x402e00d800100aa0 0xaf803f000003fc21 0xbebe00fc00000ff0

def z639 : W := mkw 0x5b9f6445bfa63105 0x916e7d9116fe98c4 0x439fc4073f003000 0x210e7f101cfc00c0

def z640 : W := mkw 0x0b80360000000000 0x002e00d800000000 0x2f00380000000000 0x08bc00e000000000

def z641 : W := mkw 0x0000002000114280 0x200000008000450a 0x800000000003c3e0 0x0200000000000f0f

def z642 : W := mkw 0x2fedbfdf00001578 0x08bfb6ff7c000055 0xefffffff00003fe3 0xffbffffffc0000ff

def z643 : W := mkw 0x2fedbffe405942ba 0x20bfb6fff901650a 0x6fffffff00fc03c3 0xfdbffffffc03f00f

def z644 : W := mkw 0x0000810a00000010 0x0000020428000000 0x80b1c71f008c03f7 0xf602c71c7c02300f

def z645 : W := mkw 0x4004006500111300 0x110010019400444c 0x000000e700000302 0x000000039c00000c

def z646 : W := mkw 0x410624640c332200 0x110418919030cc88 0x434e20e01cf3032e 0xcd0d38838073cc0c

def z647 : W := mkw 0x1ee9c10ad34c0456 0x887ba7042b4d3011 0x9ca1c318c30c0cd1 0x1272870c630c3033

def z648 : W := mkw 0x0460002040590202 0x0011800081016408 0x1c6020e0c0ff033e 0xdc7180838303fc0c

def z649 : W := mkw 0x047048b161dd57e3 0xa811c122c587755f 0xbc6038f8e3ffffff 0xdef180e3e38fffff

def z650 : W := mkw 0x00000890000040a0 0x2000002240000102 0xa00018180000c0c1 0x0280006060000303

def z651 : W := mkw 0x0010000120801101 0x0000400004820044 0x8030041f208c33f7 0xf600c0107c8230cf

def z652 : W := mkw 0x0b90f70bb786bd55 0xc82e43dc2ede1af5 0x0391c7073f003c00 0x200e471c1cfc00f0

def z653 : W := mkw 0x2b8db74e9602a81c 0x40ae36dd3a580aa0 0xff9fff07ff03fc3d 0xbffe7ffc1ffc0ff0

def z654 : W := mkw 0x0b903601b682b905 0x402e40d806da0ae4 0xbf903f07ff83ff3f 0xfefe40fc1ffe0ffc

def z655 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0x93800700ff03fc3c 0x224e001c03fc0ff0

def z656 : W := mkw 0x14724000fbec0007 0x8051c90003efb000 0x1c600000fffc001c 0x5c71800003fff000

def z657 : W := mkw 0x10124000bba40005 0x8040490002ee9000 0x000000003f000000 0x0000000000fc0000

def z658 : W := mkw 0x411624452ca23101 0x1104589114b288c4 0x435e24e73c003002 0xed0d78939cf000c0

def z659 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0x1c6000f8c0fc03de 0x5c718003e303f00f

def z660 : W := mkw 0x0000120000008800 0x4000004800000220 0xa0001b000000cc01 0x0280006c00000330

def z661 : W := mkw 0x4ff63ef5fefbfba7 0x713fd8fbd7fbefee 0xfffe3fffffffffff 0xfffff8ffffffffff

def z662 : W := mkw 0x2b8db74e00000018 0x00ae36dd38000000 0x43bfc71f00000003 0xf50eff1c7c000000

def z663 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc4038e0c0ffc3fc 0x0af100e38303ff0f

def z664 : W := mkw 0x1a8b00009a200004 0x006a2c0002688000 0x430e00001c000000 0x010c380000700000

def z665 : W := mkw 0x0000002040594282 0x200000008101650a 0x0000000000fc03c0 0x000000000003f00f

def z666 : W := mkw 0x6b9fb76f2cb33319 0x11ae7eddbcb2cccc 0x43dfe7e73cf3332e 0xed0f7f9f9cf3cccc

def z667 : W := mkw 0x5fff7665ffffbb07 0xd17ffdd997fffeec 0xffffffe7ffffff3f 0xffffffff9ffffffc

def z668 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000800326 0xc40000000002000c

def z669 : W := mkw 0x4016006528b11301 0x1100580194a2c44c 0x405e04e720f03326 0xe50178139c83c0cc

def z670 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xa3803f003f03fc21 0xa28e00fc00fc0ff0

def z671 : W := mkw 0x4104246504133300 0x1104109194104ccc 0x004024e700f3332e 0xcc0100939c03cccc

def z672 : W := mkw 0x4b963645bea2b905 0x512e58d916fa8ae4 0xff9e3f07ff03fc3d 0xbffe78fc1ffc0ff0

def z673 : W := mkw 0x0000810b00001550 0x080002042c000055 0x0000070700003c00 0x0000001c1c0000f0

def z674 : W := mkw 0x0000810a00000450 0x0800020428000011 0x8000031800000cc1 0x0200000c60000033

def z675 : W := mkw 0x2ee99b9a00000038 0x00bba66e68000000 0x2cb1df1f00000003 0xf4b2c77c7c000000

def z676 : W := mkw 0x2104bfde0402a838 0x408412ff78100aa0 0xa0003fff0003fc23 0x828000fffc000ff0

def z677 : W := mkw 0x000008b0001142a0 0x20000022c000450a 0xa04038f800f3c3ef 0xce8100e3e003cf0f

def z678 : W := mkw 0x4116e56f2db73751 0x99045b95bcb6dcdd 0x43dfe7e73ff33f2e 0xed0f7f9f9cffccfc

def z679 : W := mkw 0x0000000100001540 0x0800000004000055 0x8000000000003fe0 0x02000000000000ff

def z680 : W := mkw 0x1efb4000ffeea807 0xc07bed0003ffbaa0 0xdfffc000fffffc3c 0x7f7fff0003fffff0

def z681 : W := mkw 0x0000000092008804 0x4000000002480220 0x90000000c300cc10 0x02400000030c0330

def z682 : W := mkw 0x0110e50b25863551 0x880443942c9618d5 0x83b1e71f3f8f3fff 0xfe0ec79c7cfe3cff

def z683 : W := mkw 0x1ee948b0d35d42a6 0xa07ba522c34d750a 0xbce1f8f8c3ffc3ff 0xdef387e3e30fff0f

def z684 : W := mkw 0x1eeb0000da680006 0x007bac000369a000 0x5fce0000ff70001c 0x3d7f380003fdc000

def z685 : W := mkw 0x0460000040480002 0x0011800001012000 0x1c400000c0700008 0x087100000301c000

def z686 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5cffc000c3fc0010 0x5173ff00030ff000

def z687 : W := mkw 0x0b80b70a9602a814 0x402e02dc2a580aa0 0xbfb1ff1fff03fc3f 0xfefec7fc7ffc0ff0

def z688 : W := mkw 0x0010000120801101 0x0000400004820044 0x0010000700800302 0x400040001c02000c

def z689 : W := mkw 0x10124000ffeea807 0xc040490003ffbaa0 0x90000000fffffc3c 0x0240000003fffff0

def z690 : W := mkw 0x2fedbffe405942ba 0x20bfb6fff901650a 0x7fffffffc073c00b 0xfdffffffff01cf00

def z691 : W := mkw 0x0fe03eb0d65beaa6 0x603f80fac3596faa 0x3f4038e0dc73c008 0x08fd00e38371cf00

def z692 : W := mkw 0x0a80120092008804 0x402a004802480220 0x0080030003000c00 0x0002000c000c0030

def z693 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x00b1c71f23003c03 0xf402c71c7c8c00f0

def z694 : W := mkw 0x0000000000000000 0x0000000000000000 0x030000003c00000c 0x2c0c000000f00000

def z695 : W := mkw 0x401600652cb33301 0x1100580194b2cccc 0x405e00e73cf3332e 0x410178039cf3cccc

def z696 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc4038f8c073c3eb 0x8af100e3e301cf0f

def z697 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6f4e3fff00000003 0x89bd38fffc000000

def z698 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x00b1c01f238c03d6 0x7402c7007c8e300f

def z699 : W := mkw 0x047208b068f942a3 0x2011c822c1a3e50a 0xff7e38f8fcffc3ff 0xfffdf8e3e3f3ff0f

def z700 : W := mkw 0x0b80360000000000 0x002e00d800000000 0x0380070000000000 0x200e001c00000000

def z701 : W := mkw 0x0470c99b61cc55f3 0xa811c3266d873157 0xbcb1df1fe38cfff7 0xf6f2c77c7f8e33ff

def z702 : W := mkw 0x3fffffde69ec003b 0x80ffffff79a7b000 0x6fffffff00fc0003 0xfdbffffffc03f000

def z703 : W := mkw 0x0000000000000000 0x0000000000000000 0x0020001800000003 0xd400800060000000

def z704 : W := mkw 0x0a80d30a93048c54 0xc82a034c2a4c1231 0xbca1db18c30cccd1 0x12f2876c630c3333

def z705 : W := mkw 0x0000000000000000 0x0000000000000000 0x435e000000000000 0x6d0d780000000000

def z706 : W := mkw 0x0b80360092000004 0x002e00d802480000 0x3f803f00ff00001d 0xbcfe00fc03fc0000

def z707 : W := mkw 0x2eed9bde00000038 0x00bbb66f78000000 0x6c7fd8ff00000002 0x41b1ff63fc000000

def z708 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0xffffffffc000c013 0xffffffffff000300

def z709 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0xc3fe27ff3fff3fff 0xff0ff89ffcfffcff

def z710 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0xdfffc000fffc03fc 0x7f7fff0003fff00f

def z711 : W := mkw 0x1efb5200fbec8807 0xc07bed4803efb220 0xfffffb00ffffcc3d 0xffffffec03ffff30

def z712 : W := mkw 0x1efb4000fbec0447 0x887bed0003efb011 0xdfffc000fffc0cdc 0x7f7fff0003fff033

def z713 : W := mkw 0x4a961265bab19b05 0x512a584996eac66c 0xfcde1be7c3f0cf13 0x53f3786f9f0fc33c

def z714 : W := mkw 0x411636652cb3bb01 0x510458d994b2ceec 0xe3de3fe73ff3ff3f 0xff8f78ff9cffcffc

def z715 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x7fffffffc000001f 0xfdffffffff000000

def z716 : W := mkw 0x4016006528b11301 0x1100580194a2c44c 0x435e04e73cf0332e 0xed0d78139cf3c0cc

def z717 : W := mkw 0x45762cd56cea71a3 0x3115d8b355b3a9c6 0xff3e1c1ffc0cf0d1 0x33fcf8707ff033c3

def z718 : W := mkw 0x0ee90000d2480006 0x003ba40003492000 0x5fffc000fffc001c 0x7d7fff0003fff000

def z719 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0x43ffc7ff3f003c02 0x610fff1ffcfc00f0

def z720 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fffc000fffc033e 0xfd7fff0003fff00c

def z721 : W := mkw 0x410624650c333300 0x110418919430cccc 0x435e24e71c73332a 0xed0d78939c71cccc

def z722 : W := mkw 0x2fedbfde404840ba 0x20bfb6ff79012102 0x6fffffff000c00c3 0xfdbffffffc003003

def z723 : W := mkw 0x157b76006deea803 0xc055edd801b7baa0 0xe07fff0000fffc21 0xc381fffc0003fff0

def z724 : W := mkw 0x401240212db73301 0x9100490084b6dccc 0x000000003fff333c 0x0000000000fffccc

def z725 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x80b1c71f238c3ff6 0x6202c71c7c8e30ff

def z726 : W := mkw 0x50124021ffffbb07 0xd140490087fffeec 0x90000000ffffff3c 0x0240000003fffffc

def z727 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0xffffff00fffffc3d 0xfffffffc03fffff0

def z728 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6f7fffff00000003 0xc9bdfffffc000000

def z729 : W := mkw 0x1efb4001fbec1107 0x807bed0007efb044 0x5fffc007fffc031e 0x7d7fff001ffff00c

def z730 : W := mkw 0x2fedbfde9200003c 0x00bfb6ff7a480000 0xffffffffff003c3f 0xfffffffffffc00f0

def z731 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x407fc7ff00000003 0xc101ff1ffc000000

def z732 : W := mkw 0x0000c10b01041550 0x880003042c041055 0x80a1c71f230c3ff7 0xb602871c7c8c30ff

def z733 : W := mkw 0x2b8dbfde00000038 0x00ae36ff78000000 0x6f9fffff00000003 0xbdbe7ffffc000000

def z734 : W := mkw 0x1a9b4000fbec0007 0x806a6d0003efb000 0x53dfc000fffc001c 0x6d4f7f0003fff000

def z735 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x6c7fd8ff00000003 0x51b1ff63fc000000

def z736 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbfa03f18ff03fc3f 0xfefe80fc63fc0ff0

def z737 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbcf1f8f8c0ffc3ff 0xfef3c7e3e303ff0f

def z738 : W := mkw 0x0010c10b21841551 0x880043042c861055 0xa0b1ff1f238ffff7 0xf682c7fc7c8e3fff

def z739 : W := mkw 0x411664652db73741 0x9904599194b6dcdd 0x435e24e73cff33ee 0xed0d78939cf3fccf

def z740 : W := mkw 0x4b927621bfb7bf45 0xd92e49d886fedefd 0xbf803f00fffffffd 0xbefe00fc03ffffff

def z741 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6ffff8ff00000002 0x7dbfffe3fc000000

def z742 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x40ffc0ff00000002 0x7503ff03fc000000

def z743 : W := mkw 0x0fe03eb0d65beaa6 0x603f80fac3596faa 0x03e007f83ffc3fc2 0x600f801fe0fff0ff

def z744 : W := mkw 0x000008b0405942a2 0x20000022c101650a 0xbc0038f8c0ffc3ff 0x9ef000e3e303ff0f

def z745 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fffffe700000000 0x7dbfffff9c000000

def z746 : W := mkw 0x2b8db76e4059429a 0x20ae36ddb901650a 0xd39fc707c0ffc3fc 0x234e7f1c1f03ff0f

def z747 : W := mkw 0x1a9b4000fbec0007 0x806a6d0003efb000 0x439fc0003ffc0000 0x210e7f0000fff000

def z748 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e24e73c73302c 0xad0d78939cf1ccc0

def z749 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0x3f803f00ff03fc2c 0xacfe00fc03fc0ff0

def z750 : W := mkw 0x0106244408200000 0x0004189110208000 0x435e24e71c70000a 0xed0d78939c71c000

def z751 : W := mkw 0x0012c10b29a41551 0x88004b042ca69055 0xc0ffc71f23fc3ff7 0xf703ff1c7c8ff0ff

def z752 : W := mkw 0x256dadde04022038 0x0095b6b778100880 0x437fe4ff3c03302e 0xed0dff93fcf00cc0

def z753 : W := mkw 0x0b90f70bb786bd55 0xc82e43dc2ede1af5 0x3f31f81fdc8fc3ca 0x48fcc7e07f723f0f

def z754 : W := mkw 0x411624652cb3bb01 0x5104589194b2ceec 0xc35e24e73cf3ff2e 0xef0d78939cf3cffc

def z755 : W := mkw 0x2fedbfde0402a838 0x40bfb6ff78100aa0 0xefffffff3c03fc2f 0xffbffffffcf00ff0

def z756 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0xefffffff3f003c37 0xffbffffffcfc00f0

def z757 : W := mkw 0x2fedbfde9200883c 0x40bfb6ff7a480220 0xffffffffe300fc37 0xffffffffff8c03f0

def z758 : W := mkw 0x2fedbfde04022038 0x00bfb6ff78100880 0x6fffffff3c003003 0xfdbffffffcf000c0

def z759 : W := mkw 0x2fedbfded64ae8be 0x60bfb6ff7b592ba2 0xffffffffff0ffcff 0xfffffffffffc3ff3

def z760 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x437e24ff3cf3332f 0xfd0df893fcf3cccc

def z761 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e20e73cf3332e 0x490d78839cf3cccc

def z762 : W := mkw 0x10124000fbec0007 0x8040490003efb000 0x53ffc000fffc001c 0x7d4fff0003fff000

def z763 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0xdfffc000fffc3c3c 0x7f7fff0003fff0f0

def z764 : W := mkw 0x2b8dbfde9602a83c 0x40ae36ff7a580aa0 0xff9fffffff03fc3f 0xbffe7ffffffc0ff0

def z765 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x43ffc0003ffc0014 0x750fff0000fff000

def z766 : W := mkw 0x2fedbfde00000478 0x08bfb6ff78000011 0xefffffff00000cc3 0xffbffffffc000033

def z767 : W := mkw 0x246d89de9602a83c 0x4091b6277a580aa0 0xd07fc0ffff03fc3e 0x4341ff03fffc0ff0

def z768 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0xc35e24e73cf3333f 0xff0d78939cf3cccc

def z769 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6ffffbff00000003 0x59bfffeffc000000

def z770 : W := mkw 0x411636652cb3bb01 0x510458d994b2ceec 0x435e27e73cf33f2e 0xed0d789f9cf3ccfc

def z771 : W := mkw 0x5b926421ffff3307 0x916e499087fffccc 0x1f802400ffff333c 0xbc7e009003fffccc

def z772 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbfa03f00ff8ffc3d 0xfefe80fc03fe3ff0

def z773 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0xffffffffdc03c03f 0xffffffffff700f00

def z774 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fffc000fffc0008 0x697fff0003fff000

def z775 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fffdfff00000003 0x71bfff7ffc000000

def z776 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e24e71cf3030a 0xed0d78939c73cc0c

def z777 : W := mkw 0x411624642cb32201 0x1104589190b2cc88 0x435e24e73cf3000e 0xed0d78939cf3cc00

def z778 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fffe0e0fffc001e 0xfd7fff8383fff000

def z779 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbf803f00ff03fc19 0x3afe00fc03fc0ff0

def z780 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fffffff00800327 0xfdbffffffc02000c

def z781 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0x3c6038f8c0ffc3cb 0xdcf180e3e303ff0f

def z782 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x9cb1c71fe38c3fff 0xfe72c71c7f8e30ff

def z783 : W := mkw 0x1a9b48b0bbb542a5 0xa06a6d22c2eed50a 0xe39ff8f83f03c3e3 0xa38e7fe3e0fc0f0f

def z784 : W := mkw 0x0470c9bb61dd57f3 0xa811c326ed87755f 0x3cd1ffe7e373fc08 0x28f347ff9f8dcff0

def z785 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0xdfffc300fffc0c1d 0x7f7fff0c03fff030

def z786 : W := mkw 0x411264212db73741 0x9904499084b6dcdd 0x838027003fff3ffd 0xbe0e009c00fffcff

def z787 : W := mkw 0x1eeb0000da680006 0x007bac000369a000 0x5f7fc000dc700008 0x497dff000371c000

def z788 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbf803f00ff03fc31 0xb2fe00fc03fc0ff0

def z789 : W := mkw 0x2eed89de00000038 0x00bbb62778000000 0x43ffc0ff00000002 0x610fff03fc000000

def z790 : W := mkw 0x2fedbfde4048003a 0x00bfb6ff79012000 0xffffffffc0ffc03f 0xffffffffff03ff00

def z791 : W := mkw 0x5fed6465d75f3306 0x917fb591975d7ccc 0x1ca1e4e7c30f3332 0x907287939f0c3ccc

def z792 : W := mkw 0x1a9b4000bba40005 0x806a6d0002ee9000 0x43ffc0003ffc001c 0x7d0fff0000fff000

def z793 : W := mkw 0x4106e56e0d372650 0x99041b95b834dc99 0xc3efe3f81f7f0cd9 0x1b0fbf8fe07dfc33

def z794 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0xc35e24e73ff33f3e 0xef0d78939cffccfc

def z795 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc6038f8c0ffc3fd 0x1af180e3e303ff0f

def z796 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x00b1c71f238c3fc3 0xf402c71c7c8e30ff

def z797 : W := mkw 0x0004814e00000010 0x0000120538000000 0x407fc0ff00000002 0x4101ff03fc000000

def z798 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x83b1c71f3f8c3fff 0xfe0ec71c7cfe30ff

def z799 : W := mkw 0x246d89de00000038 0x0091b62778000000 0xc07fc0ff008c03f7 0xd701ff03fc02300f

def z800 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0xefffffff00003c23 0xffbffffffc0000f0

def z801 : W := mkw 0x246d89de00000038 0x0091b62778000000 0xc0ffc7ff23003c37 0xf703ff1ffc8c00f0

def z802 : W := mkw 0x2fedbfde9200003c 0x00bfb6ff7a480000 0x6fffffff3f000003 0xfdbffffffcfc0000

def z803 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbf803f00ff83ff3f 0xfefe00fc03fe0ffc

def z804 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0xefffffff03000c13 0xffbffffffc0c0030

def z805 : W := mkw 0x4114646525973301 0x9104519194965ccc 0x00b1e4e7238f3336 0xf402c7939c8e3ccc

def z806 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x437fc0001cfc0000 0x410dff000073f000

def z807 : W := mkw 0x0a9b000028a00001 0x002a6c0000a28000 0x43dfc0003cf0000c 0x6d0f7f0000f3c000

def z808 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0xffffffffc303fc33 0xffffffffff0c0ff0

def z809 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbce038f8e3ffc3ff 0xfef380e3e38fff0f

def z810 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0xff7e3cfffcfff3ff 0xfffdf8f3fff3ffcf

def z811 : W := mkw 0x3efb5a90fbec002f 0x80fbed6a43efb000 0x7fffd800fffc001c 0x7dffff6003fff000

def z812 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0x7ffffffffc03f02f 0xfdfffffffff00fc0

def z813 : W := mkw 0x2b8db74e9602a81c 0x40ae36dd3a580aa0 0xffdfffe7ff03fc3f 0xffff7fff9ffc0ff0

def z814 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbfa03f18ff0ffcfd 0xbefe80fc63fc3ff3

def z815 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0x7fffffffff03c01f 0xfdfffffffffc0f00

def z816 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x6c7ff8ff00000002 0x49b1ffe3fc000000

def z817 : W := mkw 0x0b84b74e00000010 0x002e12dd38000000 0x6fffffff00000003 0xfdbffffffc000000

def z818 : W := mkw 0x4016006528b11301 0x1100580194a2c44c 0x435e00e71cf0030a 0x490d78039c73c00c

def z819 : W := mkw 0x1efb0000fae80007 0x007bec0003eba000 0x5fffc000fcf0000c 0x7d7fff0003f3c000

def z820 : W := mkw 0x0efb0000baa00005 0x003bec0002ea8000 0x5fffc000fff0001c 0x7d7fff0003ffc000

def z821 : W := mkw 0x0fed36449602a804 0x403fb4d912580aa0 0xffffffe7ff03fc3f 0xffffffff9ffc0ff0

def z822 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x6f5e3ce73cf3332f 0xfdbd78f39cf3cccc

def z823 : W := mkw 0x6efb9bbb2cb33339 0x11bbee6eecb2cccc 0x2ca1db183cf3332d 0x10b2876c60f3cccc

def z824 : W := mkw 0x410624650c333300 0x110418919430cccc 0x434e24e71c733008 0x090d38939c71ccc0

def z825 : W := mkw 0x1ee9c99ad34c44f6 0xa87ba7266b4d3113 0xbca1db18c30cccd1 0x12f2876c630c3333

def z826 : W := mkw 0x1eeb810bda681556 0x087bae042f69a055 0xdf4e071fdc703feb 0x8b7d381c7f71c0ff

def z827 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0xe35e3ce73cf3f32f 0xef8d78f39cf3cfcc

def z828 : W := mkw 0x1efb4000fbec4087 0xa07bed0003efb102 0xdfffc000fffcc0dc 0x7f7fff0003fff303

def z829 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x80b1c71f238c3ff5 0x3202c71c7c8e30ff

def z830 : W := mkw 0x2b8db74e9602a81c 0x40ae36dd3a580aa0 0x43dfe7e73f033c2e 0xed0f7f9f9cfc0cf0

def z831 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e20e71c730008 0x090d78839c71cc00

def z832 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0x3f803f00ff03fc1c 0x3cfe00fc03fc0ff0

def z833 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x7ffff800fffc001d 0xfdffffe003fff000

def z834 : W := mkw 0x2eed9bde00000038 0x00bbb66f78000000 0x6fffdbff00000003 0x7dbfff6ffc000000

def z835 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fffffff00000002 0x69bffffffc000000

def z836 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x40ffc7ff00000002 0x6103ff1ffc000000

def z837 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5f7fc000dcfc001c 0x5d7dff000373f000

def z838 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x43dfc0003f700000 0x210f7f0000fdc000

def z839 : W := mkw 0x411636652cb33301 0x110458d994b2cccc 0x635e3fe73cf3332f 0xed8d78ff9cf3cccc

def z840 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fffffff00f0000f 0xfdbffffffc03c000

def z841 : W := mkw 0x2fedbfde04022038 0x00bfb6ff78100880 0x6fffffff1c03000b 0xfdbffffffc700c00

def z842 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fbfc000fffc001c 0x317eff0003fff000

def z843 : W := mkw 0x2fedbfde9200883c 0x40bfb6ff7a480220 0xffffffffc303cc3f 0xffffffffff0c0f30

def z844 : W := mkw 0x256dbfde00000038 0x0095b6ff78000000 0x637fffff00000003 0xed8dfffffc000000

def z845 : W := mkw 0x0012400029a40001 0x8000490000a69000 0x437fc0003cfc000c 0x6d0dff0000f3f000

def z846 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc4038f8c0ffc3ff 0x8af100e3e303ff0f

def z847 : W := mkw 0x2eed89de00000038 0x00bbb62778000000 0x6ffff8ff00000003 0xfdbfffe3fc000000

def z848 : W := mkw 0x411664652db73741 0x9904599194b6dcdd 0xc3de27e73fff3fff 0xff0f789f9cfffcff

def z849 : W := mkw 0x0116244528a01101 0x0004589114a28044 0x435e24e73cf0332e 0xed0d78939cf3c0cc

def z850 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbf903f07ff03fc3f 0xfefe40fc1ffc0ff0

def z851 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0xefffffff238c3ff7 0xffbffffffc8e30ff

def z852 : W := mkw 0x2fedbfde9200003c 0x00bfb6ff7a480000 0x7fffffffc3000013 0xfdffffffff0c0000

def z853 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x4fffc0003ffc0000 0x7d3fff0000fff000

def z854 : W := mkw 0x3ee9db9ad34c047e 0x88fba76e6b4d3011 0xbca1db18c30c0cd1 0x12f2876c630c3033

def z855 : W := mkw 0x0b8436449602a804 0x402e10d912580aa0 0xffce3fe0ff03fc3d 0xbfff38ff83fc0ff0

def z856 : W := mkw 0x246d89de4048003a 0x0091b62779012000 0x407fc0ff00fc0002 0x4101ff03fc03f000

def z857 : W := mkw 0x1efb5200fbec0007 0x807bed4803efb000 0x7fffdb00fffc001d 0x7dffff6c03fff000

def z858 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc6038f8c0ffc3db 0x5af180e3e303ff0f

def z859 : W := mkw 0x40124021bfb7bf45 0xd900490086fedefd 0x90000000fffffffc 0x0240000003ffffff

def z860 : W := mkw 0x2ffd7ed521841569 0x88bff5fb54861055 0xef4e38e0238c3ff4 0x0bbd38e3808e30ff

def z861 : W := mkw 0x6104bfff04133778 0x198412fffc104cdd 0xa0003fff00033fe3 0x828000fffc000cff

def z862 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e04e73cf3332e 0x610d78139cf3cccc

def z863 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0xffffffffc08fc3ff 0xffffffffff023f0f

def z864 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc6038f8c0ffc3eb 0xcaf180e3e303ff0f

def z865 : W := mkw 0x1a9b4000bba40005 0x806a6d0002ee9000 0x43dfc0003f700008 0x290f7f0000fdc000

def z866 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0xdfffc018fffc00dd 0x7f7fff0063fff003

def z867 : W := mkw 0x2fedbfde0402a838 0x40bfb6ff78100aa0 0x6fffffff0003c003 0xfdbffffffc000f00

def z868 : W := mkw 0x1eeb0000da680006 0x007bac000369a000 0x5fffc000ff70001c 0x7d7fff0003fdc000

def z869 : W := mkw 0x1eeb4000db6c0006 0x807bad00036db000 0x5fefc000ff7c001c 0x3d7fbf0003fdf000

def z870 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x4fffc7ff00000002 0x7d3fff1ffc000000

def z871 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc6038f8e3ffffff 0xdef180e3e38fffff

def z872 : W := mkw 0x2b8db74e00000018 0x00ae36dd38000000 0x43dfe7e700000000 0x290f7f9f9c000000

def z873 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbce03ff8c0ffc3ff 0xfef380ffe303ff0f

def z874 : W := mkw 0x3ee9db9ad34c40be 0xa0fba76e6b4d3102 0xbca1db18c30cc0d1 0x12f2876c630c3303

def z875 : W := mkw 0x1a9b4000fbec0007 0x806a6d0003efb000 0x53bfc000fffc001c 0x754eff0003fff000

def z876 : W := mkw 0x2eed89de00000038 0x00bbb62778000000 0x4f7fc0ff00000002 0x493dff03fc000000

def z877 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0xefffffff3f03fc23 0xffbffffffcfc0ff0

def z878 : W := mkw 0x1efb4890fbec0027 0x807bed2243efb000 0x7fffd818fffc001d 0x7dffff6063fff000

def z879 : W := mkw 0x6104bfff041373b8 0x318412fffc104dce 0xa0003fff0003f3e3 0x828000fffc000fcf

def z880 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6cffffff00000003 0xd1b3fffffc000000

def z881 : W := mkw 0x501240216dff3303 0x9140490085b7fccc 0x000000003cff332c 0x0000000000f3fccc

def z882 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fffc018fffc001f 0xfd7fff0063fff000

def z883 : W := mkw 0x2eed9bde00000038 0x00bbb66f78000000 0x40ffc3ff00000002 0x4103ff0ffc000000

def z884 : W := mkw 0x2fedadde00000038 0x00bfb6b778000000 0x4fffe4ff00000002 0xfd3fff93fc000000

def z885 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc2038f8c0ffc3ff 0x92f080e3e303ff0f

def z886 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fffc000fffc0010 0x717fff0003fff000

def z887 : W := mkw 0x1efb4890fbec40a7 0xa07bed2243efb102 0x5fffc018fffc00dc 0x7d7fff0063fff003

def z888 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0x6fffffff3f033c2f 0xfdbffffffcfc0cf0

def z889 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fdfc000ff70001c 0x3d7f7f0003fdc000

def z890 : W := mkw 0x0a80000092000004 0x002a000002480000 0xbf803f00ff03fc3d 0xbefe00fc03fc0ff0

def z891 : W := mkw 0x4016006528b11301 0x1100580194a2c44c 0x435e20e73cf3032e 0xed0d78839cf3cc0c

def z892 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x80f1c71f23fc3fff 0xfe03c71c7c8ff0ff

def z893 : W := mkw 0x0eed004400000000 0x003bb40110000000 0x4fffc0e700000002 0x7d3fff039c000000

def z894 : W := mkw 0x256dbfde00000038 0x0095b6ff78000000 0x607ff8ff00000002 0x4181ffe3fc000000

def z895 : W := mkw 0x2b8dbfde00000038 0x00ae36ff78000000 0x63dfffff00000003 0xed8f7ffffc000000

def z896 : W := mkw 0x401600652cb33301 0x1100580194b2cccc 0x435e00e73cf3332e 0x6d0d78039cf3cccc

def z897 : W := mkw 0x2eed9bde9200883c 0x40bbb66f7a480220 0xfcffdbffc300cc13 0x53f3ff6fff0c0330

def z898 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x437e24ff3cff33ee 0xed0df893fcf3fccf

def z899 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e24e73cf03302 0xed0d78939cf3c0cc

def z900 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x40ffc3ff00000003 0x5103ff0ffc000000

def z901 : W := mkw 0x3ee99b9ad248003e 0x00fba66e6b492000 0x3ca1db18c0000001 0x10f2876c63000000

def z902 : W := mkw 0x1a9b4000fbec0007 0x806a6d0003efb000 0x5f9fc000fffc001c 0x3d7e7f0003fff000

def z903 : W := mkw 0x0a8012009602a804 0x402a004802580aa0 0xbc803b00ff03fc3d 0x9ef200ec03fc0ff0

def z904 : W := mkw 0x1eeb4000db6c0006 0x807bad00036db000 0x5f6fc000dc7c0008 0x097dbf000371f000

def z905 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbc803f00ff03fc3d 0x92f200fc03fc0ff0

def z906 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0xc35e24e73cff33fe 0xef0d78939cf3fccf

def z907 : W := mkw 0x411636652cb3bb01 0x510458d994b2ceec 0x635e3ce73cf3f32e 0xed8d78f39cf3cfcc

def z908 : W := mkw 0x010036009602a804 0x400400d802580aa0 0xbc003f00ff03fc3d 0x9ef000fc03fc0ff0

def z909 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x6cffffff00000003 0xfdb3fffffc000000

def z910 : W := mkw 0x1efb4890fbec0027 0x807bed2243efb000 0x7ffff8e0fffc001c 0x7dffffe383fff000

def z911 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0x7fdfffe7ff03fc08 0x29ff7fff9ffc0ff0

def z912 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fffc400fffc303c 0xfd7fff1003fff0c0

def z913 : W := mkw 0x1efb4001fbec1107 0x807bed0007efb044 0x5fffc407fffc301c 0x7d7fff101ffff0c0

def z914 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fffc018fffc03de 0x7d7fff0063fff00f

def z915 : W := mkw 0x0104a54e00000010 0x0004129538000000 0x437fe4ff00000002 0xed0dff93fc000000

def z916 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x80f1e7ff238c3ff7 0xfe03c79ffc8e30ff

def z917 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0xffffffffff00fc13 0xfffffffffffc03f0

def z918 : W := mkw 0x0010c10b21841551 0x880043042c861055 0xc3ffc71f238c3ff7 0xff0fff1c7c8e30ff

def z919 : W := mkw 0x410624640c332200 0x110418919030cc88 0x435e24e71cf3032e 0xed0d78939c73cc0c

def z920 : W := mkw 0x2b8db74e00000018 0x00ae36dd38000000 0x6fdfffe700000003 0xfdbf7fff9c000000

def z921 : W := mkw 0x410624640c332200 0x110418919030cc88 0x435e24e71c730008 0x290d78939c71cc00

def z922 : W := mkw 0x5b927621ffffbb07 0xd16e49d887fffeec 0xbf803f00ffffff3d 0xbefe00fc03fffffc

def z923 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0xffde3fe7fff3ff3f 0xffff78ff9fffcffc

def z924 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fdfc000fff0000c 0x6d7f7f0003ffc000

def z925 : W := mkw 0x2fedbfde9200003c 0x00bfb6ff7a480000 0x7fffffffdc00000b 0xfdffffffff700000

def z926 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5f5fc000dc700008 0x097d7f000371c000

def z927 : W := mkw 0x2ee99b9ad248c8be 0x60bba66e6b492322 0xbca1db18c30cccd1 0x12f2876c630c3333

def z928 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0x7fffffffff003c1f 0xfdfffffffffc00f0

def z929 : W := mkw 0x0000c10b01041550 0x880003042c041055 0x80b1c71f030c3ff3 0xf602c71c7c0c30ff

def z930 : W := mkw 0x1efb4001fbec1547 0x887bed0007efb055 0xdfffc407fffc3ffe 0xff7fff101ffff0ff

def z931 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fffffff00000001 0x39bffffffc000000

def z932 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x80b1c71f038c3ff3 0xd202c71c7c0e30ff

def z933 : W := mkw 0x011624442ca22001 0x0004589110b28880 0x435e24e73cf3302e 0xed0d78939cf3ccc0

def z934 : W := mkw 0x1efb4890fbec0027 0x807bed2243efb000 0xfffff8f8fffc03ff 0xffffffe3e3fff00f

def z935 : W := mkw 0x401240216dff77c3 0xb900490085b7fddf 0x90000000fffffffc 0x0240000003ffffff

def z936 : W := mkw 0x410624650c333300 0x110418919430cccc 0x434e24e73c73332e 0xad0d38939cf1cccc

def z937 : W := mkw 0x0004814e00000010 0x0000120538000000 0x40ffc7ff00000003 0xf503ff1ffc000000

def z938 : W := mkw 0x1efb4001fbec1107 0x807bed0007efb044 0xdfffc41ffffc33ff 0xff7fff107ffff0cf

def z939 : W := mkw 0x2fed3ef4d65beaae 0x60bfb4fbd3596faa 0x7f4e38e0dc73c008 0x09fd38e38371cf00

def z940 : W := mkw 0x2fedbfde404840ba 0x20bfb6ff79012102 0xffffffffc00fc0ff 0xffffffffff003f03

def z941 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e24e73c73332a 0xa90d78939cf1cccc

def z942 : W := mkw 0x2fedbfde9200883c 0x40bfb6ff7a480220 0x7fffffffc000c003 0xfdffffffff000300

def z943 : W := mkw 0x0a8012009602a804 0x402a004802580aa0 0xbc801f00ff03fc3d 0xb6f2007c03fc0ff0

def z944 : W := mkw 0x246d89de4048003a 0x0091b62779012000 0x5c7fc0ffc0fc001e 0x5d71ff03ff03f000

def z945 : W := mkw 0x0016004428a00001 0x0000580110a28000 0x435e00e73cf0000e 0x6d0d78039cf3c000

def z946 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc603ff8c0ffffff 0xdef180ffe303ffff

def z947 : W := mkw 0x0104246404132200 0x0004109190104c88 0x435e24e73cf3332e 0xed0d78939cf3cccc

def z948 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fffc000dffc0018 0x597fff00037ff000

def z949 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x00b1c71f238c3fd6 0x7402c71c7c8e30ff

def z950 : W := mkw 0x2eed9bde00000038 0x00bbb66f78000000 0x6cfffbff00000003 0xddb3ffeffc000000

def z951 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fffc000ff700008 0x7d7fff0003fdc000

def z952 : W := mkw 0x1efb4890fbec0027 0x807bed2243efb000 0x5fffc0f8fffc001e 0x7d7fff03e3fff000

def z953 : W := mkw 0x046908b0405942a2 0x2011a422c101650a 0xfc7ff8f8c0ffc3ff 0xdff1ffe3e303ff0f

def z954 : W := mkw 0x2eed9bde00000038 0x00bbb66f78000000 0x6cffdfff00000003 0xf5b3ff7ffc000000

def z955 : W := mkw 0x2b8db74e00000018 0x00ae36dd38000000 0x439fe7e700000002 0xa10e7f9f9c000000

def z956 : W := mkw 0x10124021fbfd57c7 0xa840490087eff55f 0x90000000fffffffc 0x0240000003ffffff

def z957 : W := mkw 0x0b84b74e9602a814 0x402e12dd3a580aa0 0xffffffffff03fc3f 0xfffffffffffc0ff0

def z958 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0xefffffff000c00d3 0xffbffffffc003003

def z959 : W := mkw 0x1a9b4000fbec0007 0x806a6d0003efb000 0x539fc000ff700008 0x214e7f0003fdc000

def z960 : W := mkw 0x3116ffdefbec003f 0x80c45bff7befb000 0x30003ffffffc001f 0x80c000fffffff000

def z961 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x437fc0ff00000002 0x410dff03fc000000

def z962 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fffc000dcfc0008 0x7d7fff000373f000

def z963 : W := mkw 0x1efb4000fbec8807 0xc07bed0003efb220 0xdfffc000fffccc1c 0x7f7fff0003fff330

def z964 : W := mkw 0x3ee9c99ad34c003e 0x80fba7266b4d3000 0x1ca1c018c30c0010 0x10728700630c3000

def z965 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0xffffd800fffcc01d 0x7fffff6003fff300

def z966 : W := mkw 0x410624650c333300 0x110418919430cccc 0x434e24e71cf3332e 0xcd0d38939c73cccc

def z967 : W := mkw 0x2fedbfde04022038 0x00bfb6ff78100880 0xfffffffffc03f03f 0xfffffffffff00fc0

def z968 : W := mkw 0x0fed244496022004 0x003fb49112580880 0x5fffe4e7ff03303e 0xfd7fff939ffc0cc0

def z969 : W := mkw 0x410624640c332200 0x110418919030cc88 0x434e24e71c73000a 0x890d38939c71cc00

def z970 : W := mkw 0x2fedbfde9200883c 0x40bfb6ff7a480220 0xffffffffff00cc1f 0xfffffffffffc0330

def z971 : W := mkw 0x0eeb000008200000 0x003bac0000208000 0x4fffc0001c700008 0x7d3fff000071c000

def z972 : W := mkw 0x5012402169fd1303 0x9140490085a7f44c 0x0000000000fc0300 0x000000000003f00c

def z973 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbf803f18ff03ffff 0xbefe00fc63fc0fff

def z974 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e20e71cf3032e 0xcd0d78839c73cc0c

def z975 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e24e71cf3332a 0xc90d78939c73cccc

def z976 : W := mkw 0x4012402129b51741 0x9900490084a6d45d 0x0000000000fc03c0 0x000000000003f00f

def z977 : W := mkw 0x2fedbfde4048003a 0x00bfb6ff79012000 0x7fffffffc00c0013 0xfdffffffff003000

def z978 : W := mkw 0x1efb4890fbec40a7 0xa07bed2243efb102 0x7fffd800fffcc01c 0x7dffff6003fff300

def z979 : W := mkw 0x0104a54e04022010 0x0004129538100880 0xc3ffe7ff3f033c3f 0xff0fff9ffcfc0cf0

def z980 : W := mkw 0x0b8436449602a804 0x402e10d912580aa0 0xbf803fe7ff03fc3f 0xbefe00ff9ffc0ff0

def z981 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fffffff20003027 0xfdbffffffc8000c0

def z982 : W := mkw 0x0efb000068e80003 0x003bec0001a3a000 0x5fffc000fcfc001c 0x7d7fff0003f3f000

def z983 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0x3c6038f8c0ffc3de 0x5cf180e3e303ff0f

def z984 : W := mkw 0x2fedbfded64aa83e 0x40bfb6ff7b592aa0 0xfffffffffffffc3f 0xfffffffffffffff0

def z985 : W := mkw 0x2fedbfde0402a838 0x40bfb6ff78100aa0 0x6fffffff00003c03 0xfdbffffffc0000f0

def z986 : W := mkw 0x1efb4001fbec1107 0x807bed0007efb044 0xdfffc707fffc3f3f 0xff7fff1c1ffff0fc

def z987 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0x3c6038f8c0ffc3ee 0xccf180e3e303ff0f

def z988 : W := mkw 0x1eeb0000da680006 0x007bac000369a000 0x5fffc000dcfc001c 0x7d7fff000373f000

def z989 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0xdfffc000ffffc03c 0x7f7fff0003ffff00

def z990 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x437fc0ff00000002 0x6d0dff03fc000000

def z991 : W := mkw 0x147b400069ec0003 0x8051ed0001a7b000 0x437fc0003cfc0000 0x610dff0000f3f000

def z992 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e24e73cf3332c 0x290d78939cf3cccc

def z993 : W := mkw 0x0104244400000000 0x0004109110000000 0x43ffe4e700000002 0xfd0fff939c000000

def z994 : W := mkw 0x0010c10b21841551 0x880043042c861055 0xbcb1df1fe38cfff7 0xf6f2c77c7f8e33ff

def z995 : W := mkw 0x1efb5200fbec8807 0xc07bed4803efb220 0x5fffc300fffc0c1c 0x7d7fff0c03fff030

def z996 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0x7fffffffff03fc0b 0xfdfffffffffc0ff0

def z997 : W := mkw 0x411664652db73301 0x9104599194b6dccc 0x435e24e73fff333e 0xed0d78939cfffccc

def z998 : W := mkw 0x1efb4890fbec40a7 0xa07bed2243efb102 0xffffd818fffcc3ff 0xffffff6063fff30f

def z999 : W := mkw 0x2fedbfde000040b8 0x20bfb6ff78000102 0xefffffff0000c0c3 0xffbffffffc000303

def z1000 : W := mkw 0x0472400069ec0003 0x8011c90001a7b000 0x5fffc000fffc001c 0x7d7fff0003fff000

def z1001 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbf803f00ff8ffffd 0xbefe00fc03fe3fff

def z1002 : W := mkw 0x000000009602a804 0x4000000002580aa0 0xbc803f00ff03fc3d 0xbef200fc03fc0ff0

def z1003 : W := mkw 0x2fed3ed400000028 0x00bfb4fb50000000 0x6ffffce700000002 0xfdbffff39c000000

def z1004 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fffe000ffff003c 0xfd7fff8003fffc00

def z1005 : W := mkw 0x0000c10b01041550 0x880003042c041055 0x80a1c71f038c3ff7 0xd602871c7c0e30ff

def z1006 : W := mkw 0x047b000028a00001 0x0011ec0000a28000 0x437fc0003cf0000c 0x6d0dff0000f3c000

def z1007 : W := mkw 0x1efb4001fbec1107 0x807bed0007efb044 0x5fffc000fffc333c 0x7d7fff0003fff0cc

def z1008 : W := mkw 0x0010c10b21841551 0x880043042c861055 0xacb1ff1f238c3ff7 0xfeb2c7fc7c8e30ff

def z1009 : W := mkw 0x2fedbfde9200003c 0x00bfb6ff7a480000 0xffffffffff03c03f 0xfffffffffffc0f00

def z1010 : W := mkw 0x1efb4001fbec1547 0x887bed0007efb055 0x5fffc000fffc3c1c 0x7d7fff0003fff0f0

def z1011 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0xffffffffdc03fc2b 0xffffffffff700ff0

def z1012 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fbfffff00000003 0xb1befffffc000000

def z1013 : W := mkw 0x0b8936009602a804 0x402e24d802580aa0 0xff9fff00ff03fc3d 0xbffe7ffc03fc0ff0

def z1014 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fffc700fffc3c1c 0x7d7fff1c03fff0f0

def z1015 : W := mkw 0x2b8db74e00000018 0x00ae36dd38000000 0x43ffe7ff00000003 0xfd0fff9ffc000000

def z1016 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0xffffffffdf03cc1b 0xffffffffff7c0f30

def z1017 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x80b1c71f238c3fd3 0x7202c71c7c8e30ff

def z1018 : W := mkw 0x0012c10b29a41551 0x88004b042ca69055 0x80b1c71f3ffc3fff 0xf602c71c7cfff0ff

def z1019 : W := mkw 0x4104a56f04133750 0x19041295bc104cdd 0x000024ff000333e2 0x80000093fc000ccf

def z1020 : W := mkw 0x2fedbfde404840ba 0x20bfb6ff79012102 0x7fffffffc000c003 0xfdffffffff000300

def z1021 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x43de27e73ff33f2e 0xed0f789f9cffccfc

def z1022 : W := mkw 0x256dbfde00000038 0x0095b6ff78000000 0x407fc7ff00000002 0x4101ff1ffc000000

def z1023 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc6038f8c0ffc3f3 0xd2f180e3e303ff0f

def z1024 : W := mkw 0x0100240004022000 0x0004009000100880 0xbf803f00ff03fc3d 0xbefe00fc03fc0ff0

def z1025 : W := mkw 0x2eed89de00000038 0x00bbb62778000000 0x4cffc0ff00000002 0x5133ff03fc000000

def z1026 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e24e73cf3300c 0x6d0d78939cf3ccc0

def z1027 : W := mkw 0x2fedbfde4048003a 0x00bfb6ff79012000 0x7fffffffc070000b 0xfdffffffff01c000

def z1028 : W := mkw 0x147b400069ec0003 0x8051ed0001a7b000 0x43ffc0003ffc001c 0x7d0fff0000fff000

def z1029 : W := mkw 0x210dbfde00000038 0x008436ff78000000 0x601fffff00000003 0x81807ffffc000000

def z1030 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbfc03f00fff3fc3d 0xfeff00fc03ffcff0

def z1031 : W := mkw 0x410624650c333300 0x110418919430cccc 0x434e20e71c73030a 0x090d38839c71cc0c

def z1032 : W := mkw 0x411664652db73301 0x9104599194b6dccc 0x437fe4e73cff332e 0xed0dff939cf3fccc

def z1033 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x405fc0e700000000 0x01017f039c000000

def z1034 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6f5ff8e700000000 0x09bd7fe39c000000

def z1035 : W := mkw 0x2fedbfde00008838 0x40bfb6ff78000220 0xefffffff0000cc03 0xffbffffffc000330

def z1036 : W := mkw 0x256dadde00000038 0x0095b6b778000000 0x407fe4ff00000002 0xc101ff93fc000000

def z1037 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0xdfffc718fffc3fff 0xff7fff1c63fff0ff

def z1038 : W := mkw 0x2fedbfded248c8be 0x60bfb6ff7b492322 0xffffffffc30cccd3 0xffffffffff0c3333

def z1039 : W := mkw 0x0104a54e00000010 0x0004129538000000 0x43dfe7e700000002 0xed0f7f9f9c000000

def z1040 : W := mkw 0x2fedbfde404840ba 0x20bfb6ff79012102 0xffffffffc08cc3f7 0xffffffffff02330f

def z1041 : W := mkw 0x0000002000110200 0x0000000080004408 0xbc6038f8c0ffc3ff 0xdef180e3e303ff0f

def z1042 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0x3f803f00ff03fc09 0xbcfe00fc03fc0ff0

def z1043 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x00b1c71f238c3fe6 0xe402c71c7c8e30ff

def z1044 : W := mkw 0x2fedbfded248003e 0x00bfb6ff7b492000 0x7ffffffffffc001f 0xfdfffffffffff000

def z1045 : W := mkw 0x147b400069ec0003 0x8051ed0001a7b000 0x5f7fc000fcfc001c 0x7d7dff0003f3f000

def z1046 : W := mkw 0x0012c10b29a41551 0x88004b042ca69055 0xc3bfc71f3f8c3ff7 0xf70eff1c7cfe30ff

def z1047 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fdfffe700000002 0xedbf7fff9c000000

def z1048 : W := mkw 0x1efb5200fbec8807 0xc07bed4803efb220 0x7fffd800fffcc01c 0x7dffff6003fff300

def z1049 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x90b1c71fe38fffff 0xf642c71c7f8e3fff

def z1050 : W := mkw 0x1efb4890fbec40a7 0xa07bed2243efb102 0xfffff8f8fffcc0df 0xffffffe3e3fff303

def z1051 : W := mkw 0x50124021ffff3747 0x9940490087fffcdd 0x90000000ffff3ffc 0x0240000003fffcff

def z1052 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc703cffc0ffc3ff 0xfef1c0f3ff03ff0f

def z1053 : W := mkw 0x0b8436449602a804 0x402e10d912580aa0 0xff9e3f07ff03fc3d 0xbffe78fc1ffc0ff0

def z1054 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0xffffffffe303fc3f 0xffffffffff8c0ff0

def z1055 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbfb1ff00ff03fc3d 0xfefec7fc03fc0ff0

def z1056 : W := mkw 0x2fedbfde04022038 0x00bfb6ff78100880 0xefffffff3f033c3f 0xffbffffffcfc0cf0

def z1057 : W := mkw 0x0ee9899a00000030 0x003ba62668000000 0x6fffffff00000003 0xfdbffffffc000000

def z1058 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x80b1e71f238f3fff 0xfe02c79c7c8e3cff

def z1059 : W := mkw 0x256dadde00000038 0x0095b6b778000000 0x437fe0ff00000002 0x490dff83fc000000

def z1060 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbce03bf8c3ffcfff 0xdef380efe30fff3f

def z1061 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e04e73cf0330e 0x6d0d78139cf3c0cc

def z1062 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x43dfc7e700000000 0x210f7f1f9c000000

def z1063 : W := mkw 0x147b400069ec0003 0x8051ed0001a7b000 0x437fc0001cfc0008 0x490dff000073f000

def z1064 : W := mkw 0x256dadde00000038 0x0095b6b778000000 0x437fc4ff00000002 0x610dff13fc000000

def z1065 : W := mkw 0x1eeb0000da680006 0x007bac000369a000 0x5fefc000dc700008 0x197fbf000371c000

def z1066 : W := mkw 0x1a9b4000bba40005 0x806a6d0002ee9000 0x5fdfc000fff0001c 0x7d7f7f0003ffc000

def z1067 : W := mkw 0x50124021ffff7387 0xb140490087fffdce 0x90000000fffff3fc 0x0240000003ffffcf

def z1068 : W := mkw 0x2b8d36449602a80c 0x40ae34d912580aa0 0xff8e3f00ff03fc3d 0xbffe38fc03fc0ff0

def z1069 : W := mkw 0x411624652cb33741 0x1904589194b2ccdd 0xc35e24e73cf33fee 0xef0d78939cf3ccff

def z1070 : W := mkw 0x6104adff04133338 0x118412b7fc104ccc 0x000024ff00033322 0x80000093fc000ccc

def z1071 : W := mkw 0x401240212db73741 0x9900490084b6dcdd 0x000000003ff33f2c 0x0000000000ffccfc

def z1072 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0xefffffff0003c023 0xffbffffffc000f00

def z1073 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fffc700fffc001d 0xfd7fff1c03fff000

def z1074 : W := mkw 0x2fedbfde0402a838 0x40bfb6ff78100aa0 0xefffffff2303fc37 0xffbffffffc8c0ff0

def z1075 : W := mkw 0x210da54e00000018 0x0084369538000000 0x435fe4e700000002 0xed0d7f939c000000

def z1076 : W := mkw 0x1eeb0000da680006 0x007bac000369a000 0x5fdfc000dc700008 0x297f7f000371c000

def z1077 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0xefffffff000003e3 0xffbffffffc00000f

def z1078 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e04e73cf03326 0xe50d78139cf3c0cc

def z1079 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e04e73c703000 0x210d78139cf1c0c0

def z1080 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc6038f8c0ffc3fe 0x4af180e3e303ff0f

def z1081 : W := mkw 0x4016006528b11301 0x1100580194a2c44c 0x435e00e73cf00302 0x610d78039cf3c00c

def z1082 : W := mkw 0x3ee9db9ad34c883e 0xc0fba76e6b4d3220 0xbca1db18c30ccc11 0x12f2876c630c3330

def z1083 : W := mkw 0x0000810a00000010 0x0000020428000000 0x80b1c71f238c3ff7 0xf602c71c7c8e30ff

def z1084 : W := mkw 0x147b4000fbec0007 0x8051ed0003efb000 0x537fc000fffc001c 0x6d4dff0003fff000

def z1085 : W := mkw 0x411624652cb37381 0x3104589194b2cdce 0xc35e24e73cf3f3ee 0xef0d78939cf3cfcf

def z1086 : W := mkw 0x6104bfff0413bb38 0x518412fffc104eec 0xa0003fff0003ff23 0x828000fffc000ffc

def z1087 : W := mkw 0x411664652db73741 0x9904599194b6dcdd 0xc3ffe4e73fff3ffe 0xff0fff939cfffcff

def z1088 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0xefffffff00000037 0xffbffffffc000000

def z1089 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x407fc0ff008c03c2 0x4101ff03fc02300f

def z1090 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xff7e38f8c0ffc3ff 0xfffdf8e3e303ff0f

def z1091 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0x6fffffff1c000003 0xfdbffffffc700000

def z1092 : W := mkw 0x0b8d244400000000 0x002e349110000000 0x43dfe4e700000002 0xed0f7f939c000000

def z1093 : W := mkw 0x1eeb4000db6c0006 0x807bad00036db000 0x5fefc000dffc001c 0x5d7fbf00037ff000

def z1094 : W := mkw 0x256dbfde00000038 0x0095b6ff78000000 0x6c7fffff00000003 0xddb1fffffc000000

def z1095 : W := mkw 0x1efb4890fbec0027 0x807bed2243efb000 0xfffff8f8ffffc03f 0xffffffe3e3ffff00

def z1096 : W := mkw 0x0564adde00000030 0x001592b778000000 0x6fffffff00000003 0xfdbffffffc000000

def z1097 : W := mkw 0x411664652db73301 0x9104599194b6dccc 0x43dfe4e73ff3332e 0xed0f7f939cffcccc

def z1098 : W := mkw 0x0feda54e00000010 0x003fb69538000000 0x4fffe7ff00000003 0xfd3fff9ffc000000

def z1099 : W := mkw 0x0012400029a40001 0x8000490000a69000 0x43dfc0003ff0000c 0x6d0f7f0000ffc000

def z1100 : W := mkw 0x2fedbfde4048003a 0x00bfb6ff79012000 0x6fffffff00fc0003 0xfdbffffffc03f000

def z1101 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0x7f7ff8ffdc03c00a 0x49fdffe3ff700f00

def z1102 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x80b1c71f238c3fe3 0xe202c71c7c8e30ff

def z1103 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x407fe0ff00000002 0xcd01ff83fc000000

def z1104 : W := mkw 0x6104bffe04132238 0x118412fff8104c88 0x20003fff00030003 0x808000fffc000c00

def z1105 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6f7ffcff00000002 0xedbdfff3fc000000

def z1106 : W := mkw 0x1efb4001fbec1547 0x887bed0007efb055 0x5fffc000fffc03dc 0x7d7fff0003fff00f

def z1107 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x407fc4ff00000002 0xe501ff13fc000000

def z1108 : W := mkw 0x2fedbfde9602203c 0x00bfb6ff7a580880 0x7fffffffff03303f 0xfdfffffffffc0cc0

def z1109 : W := mkw 0x2fedbfde404840ba 0x20bfb6ff79012102 0xffffffffc0fcc0df 0xffffffffff03f303

def z1110 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x7f5e3ce7fcf3f32e 0xedfd78f39ff3cfcc

def z1111 : W := mkw 0x4104a56f04133310 0x11041295bc104ccc 0x000027ff00033323 0x8000009ffc000ccc

def z1112 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x407fc0ff00000003 0xd501ff03fc000000

def z1113 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e24e73c73300a 0xed0d78939cf1ccc0

def z1114 : W := mkw 0x1efb4000bba40005 0x807bed0002ee9000 0x4fffc0003ff0000c 0x7d3fff0000ffc000

def z1115 : W := mkw 0x410624640c332200 0x110418919030cc88 0x435e20e71c73000a 0x490d78839c71cc00

def z1116 : W := mkw 0x2eed89de00000038 0x00bbb62778000000 0x4fffc7ff00000003 0xfd3fff1ffc000000

def z1117 : W := mkw 0x1efb4001fbec1547 0x887bed0007efb055 0xdfffc700fffc3ffd 0xff7fff1c03fff0ff

def z1118 : W := mkw 0x1a9b4000bba40005 0x806a6d0002ee9000 0x439fc0003ff0000c 0x210e7f0000ffc000

def z1119 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fffffff23000017 0xfdbffffffc8c0000

def z1120 : W := mkw 0x410624640c332200 0x110418919030cc88 0x435e24e73c73302e 0xed0d78939cf1ccc0

def z1121 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xffde3f00ff03fc3d 0xffff78fc03fc0ff0

def z1122 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fffc000ff7c0018 0x397fff0003fdf000

def z1123 : W := mkw 0x1eeb4000db6c0006 0x807bad00036db000 0x5fffc000df7c0018 0x7d7fff00037df000

def z1124 : W := mkw 0x1efb5a90fbecc8a7 0xe07bed6a43efb322 0xffffdb18fffcccdd 0x7fffff6c63fff333

def z1125 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fdfffe700000001 0xbdbf7fff9c000000

def z1126 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x43ffe4e73cf3332e 0xfd0fff939cf3cccc

def z1127 : W := mkw 0x256dadde00000038 0x0095b6b778000000 0x6f7ffcff00000003 0xfdbdfff3fc000000

def z1128 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x80a1c71f238c3ff7 0x9202871c7c8e30ff

def z1129 : W := mkw 0x246d9bde00000038 0x0091b66f78000000 0x607fdbff00000003 0x4181ff6ffc000000

def z1130 : W := mkw 0x256dbfde00000038 0x0095b6ff78000000 0x60ffffff00000003 0xf583fffffc000000

def z1131 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x43ffe7ff00000002 0xed0fff9ffc000000

def z1132 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbf803b00ff03fc3d 0x1afe00ec03fc0ff0

def z1133 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x43de27e73cf3332f 0xfd0f789f9cf3cccc

def z1134 : W := mkw 0x246d89de404840ba 0x2091b62779012102 0xfc7fd8ffc00cc0d3 0x53f1ff63ff003303

def z1135 : W := mkw 0x1efb4890fbec40a7 0xa07bed2243efb102 0xfffff818ffffc0fd 0xffffffe063ffff03

def z1136 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x607ff8ff00000003 0xc181ffe3fc000000

def z1137 : W := mkw 0x4476c9ff69fd57f3 0xb911db27fda7f55f 0x407fc0ff00fc03c2 0x4101ff03fc03f00f

def z1138 : W := mkw 0x0efb400029a40001 0x803bed0000a69000 0x4fffc0003ffc001c 0x7d3fff0000fff000

def z1139 : W := mkw 0x1efb400069ec0003 0x807bed0001a7b000 0x4fffc0003cfc000c 0x7d3fff0000f3f000

def z1140 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbf003f00ff03fc3d 0x8afc00fc03fc0ff0

def z1141 : W := mkw 0x0012810b28a01551 0x08004a042ca28055 0xc35e071f3cf03fef 0xef0d781c7cf3c0ff

def z1142 : W := mkw 0x147bc9bb69fd57f3 0xa851ef26eda7f55f 0x407fc0ff00fc03c2 0x4101ff03fc03f00f

def z1143 : W := mkw 0x0012002128b11301 0x0000480084a2c44c 0x435e24e73cf3332e 0xed0d78939cf3cccc

def z1144 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x7ffff800ffffc01c 0x7dffffe003ffff00

def z1145 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0xffdfffe7ff03fc3d 0xbfff7fff9ffc0ff0

def z1146 : W := mkw 0x411664652db73741 0x9904599194b6dcdd 0x435e24e73ff33f2e 0xed0d78939cffccfc

def z1147 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbf803f00ff03fc3c 0x2afe00fc03fc0ff0

def z1148 : W := mkw 0x256dadde00000038 0x0095b6b778000000 0x43ffe7ff00000003 0xfd0fff9ffc000000

def z1149 : W := mkw 0x1efb5200fbec8807 0xc07bed4803efb220 0xffffdf00fffcfc3d 0xffffff7c03fff3f0

def z1150 : W := mkw 0x0116246428b10201 0x0004589190a2c408 0x435e24e73cf3032e 0xed0d78939cf3cc0c

def z1151 : W := mkw 0x1a9b4000bba40005 0x806a6d0002ee9000 0x43dfc0003ff00000 0x610f7f0000ffc000

def z1152 : W := mkw 0x2fedb74e00000018 0x00bfb6dd38000000 0x4fffe7e700000002 0xfd3fff9f9c000000

def z1153 : W := mkw 0x246d89de404840ba 0x2091b62779012102 0x407fc0ff000c00c2 0x4101ff03fc003003

def z1154 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0xc35e24ff3cf333ef 0xef0d7893fcf3cccf

def z1155 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e00e71cf00302 0x410d78039c73c00c

def z1156 : W := mkw 0x4104b76f0413bf50 0x590412ddbc104efd 0xa0003fff0003ffe3 0x828000fffc000fff

def z1157 : W := mkw 0x2104bffe0413eab8 0x608412fff8104faa 0xa0003fff0003ffe3 0x828000fffc000fff

def z1158 : W := mkw 0x2fedbfde9200883c 0x40bfb6ff7a480220 0x6fffffff03000c03 0xfdbffffffc0c0030

def z1159 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbf6038f8fcffc3ff 0xfefd80e3e3f3ff0f

def z1160 : W := mkw 0x2fedbfde04022038 0x00bfb6ff78100880 0x6fffffff00033023 0xfdbffffffc000cc0

def z1161 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6f7ff8ff00000003 0xddbdffe3fc000000

def z1162 : W := mkw 0x246d89de00000038 0x0091b62778000000 0xfc7ff8ffc003c03f 0xdff1ffe3ff000f00

def z1163 : W := mkw 0x200d89de00000038 0x0080362778000000 0x401fc0ff00000002 0x01007f03fc000000

def z1164 : W := mkw 0x1eeb4000db6c0006 0x807bad00036db000 0x5fcfc000df700008 0x097f3f00037dc000

def z1165 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fffc407fffc001e 0xfd7fff101ffff000

def z1166 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x63ffffff00000003 0xe18ffffffc000000

def z1167 : W := mkw 0x50124021bfb73305 0x9140490086fedccc 0x000000003ff3332c 0x0000000000ffcccc

def z1168 : W := mkw 0x1efb4001fbec1547 0x887bed0007efb055 0xdfffc018fffc3fff 0xff7fff0063fff0ff

def z1169 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x437e24e73cff333e 0xfd0df8939cf3fccc

def z1170 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0xfffff818ffffc3ff 0xffffffe063ffff0f

def z1171 : W := mkw 0x101b400029a40001 0x80406d0000a69000 0x435fc0003cf0000c 0x6d0d7f0000f3c000

def z1172 : W := mkw 0x50124021fbfd1307 0x9140490087eff44c 0x10000000fffc031c 0x0040000003fff00c

def z1173 : W := mkw 0x0012000028a00001 0x0000480000a28000 0x43ffc0003cf0000c 0x7d0fff0000f3c000

def z1174 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbf801f00ff03fc3d 0x32fe007c03fc0ff0

def z1175 : W := mkw 0x0a8012009602a804 0x402a004802580aa0 0xbf801b00ff03fc3d 0x3efe006c03fc0ff0

def z1176 : W := mkw 0x4012402129b51741 0x9900490084a6d45d 0x8000000023fc3ff4 0x02000000008ff0ff

def z1177 : W := mkw 0x4b96f74fbfa6bd55 0xd92e5bdd3efe9af5 0x439fc7073f003c00 0x210e7f1c1cfc00f0

def z1178 : W := mkw 0x2fedbfde4048003a 0x00bfb6ff79012000 0xffffffffc0fc03ff 0xffffffffff03f00f

def z1179 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x43ffc0003ffc000c 0x6d0fff0000fff000

def z1180 : W := mkw 0x411664652db73301 0x9104599194b6dccc 0xc3ffe4ff3fff33ff 0xff0fff93fcfffccf

def z1181 : W := mkw 0x6104b76f04133318 0x118412ddbc104ccc 0x000027e700033322 0x8000009f9c000ccc

def z1182 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fffffff008c03c3 0xfdbffffffc02300f

def z1183 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x434e24e73cf3332e 0x890d38939cf3cccc

def z1184 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x5f5e24e7fcf3333e 0xfd7d78939ff3cccc

def z1185 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5f7fc000fffc001c 0x497dff0003fff000

def z1186 : W := mkw 0x0010c10b21841551 0x880043042c861055 0x80b1c71f230c3ff3 0xb202c71c7c8c30ff

def z1187 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fffffff008c0017 0xfdbffffffc023000

def z1188 : W := mkw 0x4104adff041377f0 0x390412b7fc104ddf 0xa0003fff0003ffe3 0x828000fffc000fff

def z1189 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0xd35e24e7fcf3f33e 0xef4d78939ff3cfcc

def z1190 : W := mkw 0x4116246528b11301 0x1104589194a2c44c 0x435e24e73cf0030e 0xed0d78939cf3c00c

def z1191 : W := mkw 0x046d004400000000 0x0011b40110000000 0x407fc0e700000002 0x4101ff039c000000

def z1192 : W := mkw 0x3fedbfded248003e 0x00ffb6ff7b492000 0x7fffffffc0000003 0xfdffffffff000000

def z1193 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5f7fc000fcfc000c 0x6d7dff0003f3f000

def z1194 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbfc03fe0ff03fc3f 0xfeff00ff83fc0ff0

def z1195 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fffffff3c00000f 0xfdbffffffcf00000

def z1196 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x43ffc7ff00000003 0xf50fff1ffc000000

def z1197 : W := mkw 0x411636652cb3bb01 0x510458d994b2ceec 0xff5e3fe7fcf3ff3f 0xfffd78ff9ff3cffc

def z1198 : W := mkw 0x2b8dbfde00000038 0x00ae36ff78000000 0x439fc7ff00000002 0x210e7f1ffc000000

def z1199 : W := mkw 0x2fedbfde0402a838 0x40bfb6ff78100aa0 0xffffffffc003fc3f 0xffffffffff000ff0

def z1200 : W := mkw 0x2104bfde00000038 0x008412ff78000000 0x63ffffff00000003 0xfd8ffffffc000000

def z1201 : W := mkw 0x2fedbfde9602a83c 0x40bfb6ff7a580aa0 0xffffffffff8fffff 0xfffffffffffe3fff

def z1202 : W := mkw 0x2b8dbfde9602a83c 0x40ae36ff7a580aa0 0xe39fffff3f03fc23 0xa38e7ffffcfc0ff0

def z1203 : W := mkw 0x2eed89de9200003c 0x00bbb6277a480000 0x5fffc0ffff00001e 0x7d7fff03fffc0000

def z1204 : W := mkw 0x4104a56f04133750 0x19041295bc104cdd 0x000027e700033f22 0x8000009f9c000cfc

def z1205 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x53ffc000fffc001c 0x614fff0003fff000

def z1206 : W := mkw 0x0fed364400000000 0x003fb4d910000000 0x6fffffe700000003 0xfdbfffff9c000000

def z1207 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0xdfffc000fffc003d 0xff7fff0003fff000

def z1208 : W := mkw 0x411624452ca23101 0x1104589114b288c4 0x435e24e73cf0300e 0xed0d78939cf3c0c0

def z1209 : W := mkw 0x2b8dbfde00000038 0x00ae36ff78000000 0x63bfffff00000003 0xf58efffffc000000

def z1210 : W := mkw 0x2b8dbfde00000038 0x00ae36ff78000000 0x639fffe700000000 0x218e7fff9c000000

def z1211 : W := mkw 0x200d814e00000018 0x0080360538000000 0x405fc0e700000002 0x41017f039c000000

def z1212 : W := mkw 0x0b8036009602a804 0x402e00d802580aa0 0xbf803f00ff03fc29 0xaafe00fc03fc0ff0

def z1213 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fffffff0003002f 0xfdbffffffc000c00

def z1214 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0xc35e27e73cf33f2f 0xef0d789f9cf3ccfc

def z1215 : W := mkw 0x256dbfde0402a838 0x4095b6ff78100aa0 0xe07fffff0003fc23 0xc381fffffc000ff0

def z1216 : W := mkw 0x056d244400000000 0x0015b49110000000 0x437fe4e700000002 0xed0dff939c000000

def z1217 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e24e73cf3330a 0x690d78939cf3cccc

def z1218 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e20e73cf3030e 0x6d0d78839cf3cc0c

def z1219 : W := mkw 0x046008b0405942a2 0x20118022c101650a 0xbc603cf8e0fff3ff 0xfef180f3e383ffcf

def z1220 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fdfffff00000003 0xa9bf7ffffc000000

def z1221 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fefc000fffc001c 0x197fbf0003fff000

def z1222 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x6fffffff23003c03 0xfdbffffffc8c00f0

def z1223 : W := mkw 0x0fed2cd400000020 0x003fb4b350000000 0x6ffffcff00000003 0xfdbffff3fc000000

def z1224 : W := mkw 0x0a924000bba40005 0x802a490002ee9000 0x5fffc000fffc001c 0x7d7fff0003fff000

def z1225 : W := mkw 0x401240212db73741 0x9900490084b6dcdd 0x000000003cff33ec 0x0000000000f3fccf

def z1226 : W := mkw 0x246d89de00000038 0x0091b62778000000 0x4c7fc0ff00000002 0x5d31ff03fc000000

def z1227 : W := mkw 0x411664652db73301 0x9104599194b6dccc 0xc3ffe7e73fff3f3f 0xff0fff9f9cfffcfc

def z1228 : W := mkw 0x1efb4000fbec0007 0x807bed0003efb000 0x5fdfc000fffc001c 0x297f7f0003fff000

def z1229 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x43de24e73ff3333e 0xfd0f78939cffcccc

def z1230 : W := mkw 0x411624652cb33301 0x1104589194b2cccc 0x435e24e73cf33322 0xe10d78939cf3cccc

def z1231 : W := mkw 0x2fedbfde00000038 0x00bfb6ff78000000 0x7fffffffc003c00b 0xfdffffffff000f00

def z1232 : W := mkw 0x411664652db73741 0x9904599194b6dcdd 0xc37e24ff3fff3fff 0xff0df893fcfffcff

def z1233 : W := mkw 0x2b8db74e00000018 0x00ae36dd38000000 0x43dfc7e700000002 0x610f7f1f9c000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z7,z5,z8,z6]),(0,[z0,z2,z3,z9,z4,z10,z6]),(1,[z0,z2,z3,z4,z11,z6]),(0,[z0,z12,z3,z4,z5,z13,z6]),(0,[z0,z2,z3,z4,z14,z10,z6]),(0,[z0,z15,z2,z3,z14,z5,z6])],[(0,[z16,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z17,z18,z5,z6])],[(0,[z19,z0,z2,z3,z4,z10,z6]),(1,[z0,z2,z3,z4,z5,z20]),(1,[z21,z2,z3,z4,z7,z6]),(0,[z0,z2,z3,z4,z5,z22,z6]),(0,[z0,z2,z3,z4,z18,z23,z6]),(0,[z0,z24,z2,z3,z4,z25,z6]),(0,[z0,z26,z2,z3,z4,z5,z6]),(0,[z0,z27,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z28])],[(0,[z0,z2,z3,z4,z5,z6,z29]),(0,[z0,z12,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z10,z30,z6]),(0,[z0,z31,z2,z32,z4,z5,z6]),(0,[z33,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z34,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z35])],[(0,[z0,z2,z3,z36,z18,z5,z6]),(0,[z37,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z38,z6]),(0,[z0,z2,z3,z39,z4,z5,z6]),(1,[z0,z2,z3,z40,z5,z6]),(0,[z0,z2,z3,z4,z14,z13,z6]),(0,[z0,z2,z3,z4,z5,z41,z6]),(0,[z0,z2,z3,z4,z5,z42,z6]),(0,[z0,z2,z3,z4,z43,z5,z6]),(0,[z0,z2,z3,z44,z4,z5,z45])],[(1,[z0,z2,z3,z4,z46,z6]),(0,[z0,z2,z47,z3,z4,z23,z6]),(0,[z48,z0,z12,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z49]),(0,[z0,z2,z3,z17,z4,z23,z6])],[(0,[z50,z0,z2,z3,z4,z5,z6]),(1,[z51,z2,z3,z4,z8,z6]),(0,[z0,z3,z52,z4,z18,z5,z6]),(0,[z53,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z54,z6]),(1,[z0,z2,z4,z10,z23,z6]),(0,[z0,z2,z55,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z56,z4,z5,z6]),(0,[z0,z2,z3,z4,z23,z54,z6])],[(0,[z0,z2,z3,z4,z5,z57,z6]),(0,[z0,z2,z58,z3,z4,z5,z6]),(0,[z59,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z36,z4,z23,z6]),(0,[z0,z60,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z61,z5,z6]),(0,[z0,z2,z3,z62,z4,z5,z6]),(0,[z0,z12,z2,z3,z4,z10,z6]),(0,[z0,z2,z63,z3,z4,z5,z6]),(0,[z0,z2,z3,z64,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z65]),(0,[z0,z2,z66,z3,z4,z5,z6]),(0,[z0,z2,z3,z67,z4,z5,z6]),(0,[z0,z68,z2,z3,z4,z5,z6]),(0,[z69,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z70,z5,z6]),(0,[z0,z71,z2,z3,z4,z72,z6]),(0,[z0,z2,z3,z4,z73,z5,z6])],[(0,[z51,z2,z3,z4,z5,z8,z6]),(0,[z74,z0,z2,z3,z4,z5,z75]),(0,[z0,z2,z3,z4,z76,z5,z6]),(0,[z0,z2,z3,z4,z77,z5,z6]),(0,[z0,z2,z3,z78,z4,z5,z6])],[(0,[z0,z2,z79,z3,z4,z5,z6]),(0,[z80,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z81,z4,z5,z6]),(0,[z0,z82,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z83]),(0,[z0,z2,z3,z5,z6,z84,z85])],[(0,[z0,z2,z86,z3,z4,z5,z6]),(0,[z2,z3,z4,z87,z5,z6,z88]),(0,[z0,z2,z3,z4,z89,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z90]),(0,[z0,z2,z3,z4,z91,z5,z6])],[(0,[z0,z60,z86,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z92,z6]),(0,[z0,z2,z3,z93,z52,z5,z6]),(0,[z0,z94,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z95,z6,z45]),(0,[z0,z96,z2,z3,z4,z5,z6]),(0,[z0,z97,z2,z3,z4,z98,z6])]],
   [[],[(0,[z99,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z100,z6]),(0,[z0,z2,z47,z101,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z102,z6]),(0,[z0,z2,z3,z103,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z104,z6]),(0,[z0,z2,z3,z4,z98,z23,z6]),(0,[z0,z2,z3,z4,z105,z5,z6])],[(0,[z2,z101,z3,z106,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z11,z6]),(0,[z0,z107,z2,z3,z4,z108,z6]),(0,[z0,z31,z2,z3,z4,z109,z6])],[(0,[z110,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z93,z36,z5,z6]),(1,[z0,z2,z3,z111,z5,z6]),(1,[z0,z112,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z113,z5,z6]),(0,[z114,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z115,z5,z6]),(1,[z0,z2,z3,z116,z5,z6])],[(0,[z19,z2,z86,z3,z4,z5,z6]),(0,[z117,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z6,z84])],[(0,[z0,z118,z2,z3,z4,z5,z6]),(1,[z0,z2,z4,z23,z6,z119]),(0,[z120,z0,z2,z3,z4,z5,z6])],[(0,[z121,z0,z2,z3,z4,z5,z6]),(0,[z122,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z123,z6])],[(0,[z0,z2,z3,z4,z5,z6,z20]),(0,[z0,z2,z3,z4,z5,z6,z124]),(0,[z125,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z38,z6]),(0,[z126,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z70,z23,z6]),(0,[z0,z2,z3,z44,z4,z5,z127])]],
   [[(0,[z0,z2,z3,z128,z4,z5,z6]),(0,[z0,z129,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z46,z6]),(0,[z0,z2,z3,z4,z5,z8,z6]),(1,[z0,z2,z3,z130,z5,z6]),(0,[z131,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z132,z6]),(0,[z0,z2,z3,z4,z133,z5,z6])],[(0,[z0,z2,z3,z4,z134,z5,z6]),(0,[z0,z2,z3,z4,z23,z8,z6]),(0,[z21,z0,z2,z3,z135,z5,z6]),(0,[z74,z0,z2,z3,z4,z38,z6]),(0,[z0,z2,z136,z3,z4,z5,z6]),(0,[z0,z2,z3,z137,z4,z5,z6]),(0,[z0,z2,z138,z3,z4,z5,z6])],[(0,[z0,z2,z86,z3,z4,z23,z6]),(0,[z0,z139,z2,z3,z4,z5,z6]),(0,[z140,z0,z2,z3,z4,z10,z6]),(1,[z0,z24,z3,z4,z5,z30]),(0,[z0,z2,z3,z93,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z141,z6])],[(0,[z0,z142,z2,z3,z4,z5,z6]),(0,[z143,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z7,z6]),(0,[z0,z144,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z23,z145,z6]),(0,[z0,z2,z3,z146,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z147,z6]),(0,[z0,z2,z148,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z149])],[(0,[z150,z0,z2,z3,z4,z5,z6]),(0,[z151,z0,z2,z3,z4,z5,z6]),(1,[z152,z2,z106,z4,z5,z6]),(1,[z140,z2,z3,z87,z5,z6]),(0,[z0,z2,z3,z52,z87,z5,z6]),(0,[z0,z24,z2,z3,z4,z5,z6]),(0,[z0,z2,z153,z3,z4,z5,z6]),(1,[z0,z154,z2,z3,z4,z5])],[(0,[z0,z2,z3,z155,z4,z5,z6]),(0,[z0,z2,z101,z3,z4,z10,z6]),(0,[z156,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z157,z4,z5,z6]),(0,[z158,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z159,z5,z6])],[(0,[z160,z0,z2,z3,z4,z5,z6]),(0,[z0,z161,z2,z3,z4,z5,z6]),(0,[z162,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z75,z6]),(0,[z0,z2,z3,z4,z163,z5,z6]),(0,[z0,z2,z3,z164,z4,z145,z6]),(0,[z0,z2,z3,z4,z165,z5,z6]),(0,[z0,z2,z3,z4,z5,z166,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z167,z6]),(0,[z168,z0,z2,z106,z4,z5,z6]),(0,[z0,z2,z3,z4,z169,z5,z6]),(0,[z0,z2,z3,z4,z5,z170,z6]),(0,[z0,z2,z3,z4,z5,z171,z6]),(0,[z0,z2,z3,z4,z7,z23,z6]),(0,[z172,z0,z2,z3,z52,z5,z6]),(0,[z48,z0,z2,z3,z4,z173,z6]),(1,[z0,z2,z3,z174,z5,z6]),(0,[z0,z175,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z176,z5,z6]),(0,[z177,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z93,z18,z5,z6]),(0,[z0,z2,z3,z178,z4,z5,z6]),(1,[z0,z2,z3,z179,z5,z6]),(0,[z0,z31,z2,z3,z180,z5,z6]),(0,[z0,z2,z55,z4,z5,z23,z6]),(0,[z0,z15,z2,z3,z164,z5,z6])],[(1,[z0,z181,z3,z4,z5,z6]),(0,[z0,z2,z3,z182,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z183]),(0,[z0,z2,z3,z4,z5,z6,z184]),(0,[z0,z2,z3,z4,z23,z185,z6])],[(0,[z0,z2,z3,z186,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z187]),(0,[z0,z2,z3,z4,z5,z127,z88]),(0,[z0,z2,z3,z18,z180,z5,z6]),(0,[z188,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z189,z6]),(0,[z0,z2,z3,z4,z10,z98,z6]),(0,[z190,z0,z2,z3,z4,z5,z6])],[(0,[z51,z0,z97,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z191,z5,z6]),(1,[z0,z2,z192,z4,z23,z6]),(0,[z0,z193,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z194,z4,z5,z6]),(0,[z48,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z55,z4,z5,z127,z6])],[(0,[z0,z2,z3,z195,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z196,z6]),(0,[z0,z2,z197,z3,z4,z5,z6]),(0,[z0,z107,z2,z3,z52,z5,z6]),(0,[z198,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z93,z4,z23,z6]),(0,[z0,z2,z3,z4,z10,z145,z6]),(0,[z0,z2,z3,z4,z5,z199,z6]),(0,[z0,z2,z3,z164,z4,z185,z6])],[(0,[z0,z2,z106,z9,z4,z5,z6]),(1,[z200,z0,z2,z4,z10,z6])]],
   [[(0,[z0,z2,z3,z4,z201,z5,z6]),(0,[z0,z2,z3,z4,z87,z23,z6]),(0,[z0,z2,z3,z4,z202,z5,z6]),(0,[z0,z2,z3,z3,z4,z23,z6]),(0,[z200,z0,z2,z4,z10,z5,z6])],[(1,[z0,z2,z3,z135,z5,z6]),(0,[z0,z112,z2,z3,z4,z6,z88]),(0,[z0,z24,z2,z3,z4,z23,z6]),(1,[z0,z2,z3,z4,z203,z6]),(0,[z0,z2,z204,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z205,z6]),(0,[z0,z15,z97,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z206,z5,z6]),(0,[z74,z0,z2,z47,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z207,z6]),(0,[z0,z2,z3,z4,z5,z132,z6])],[(0,[z208,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z209,z6]),(0,[z172,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z210,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z211])],[(0,[z0,z2,z3,z4,z212,z5,z6]),(0,[z0,z2,z3,z87,z5,z6,z45]),(1,[z0,z2,z3,z5,z213,z6]),(0,[z0,z2,z3,z4,z5,z214,z6]),(0,[z0,z2,z32,z3,z4,z10,z6]),(0,[z0,z31,z2,z3,z93,z5,z6]),(0,[z0,z2,z3,z4,z10,z6,z45]),(0,[z0,z15,z2,z3,z4,z5,z45]),(0,[z0,z215,z2,z3,z4,z5,z6])],[(0,[z216,z0,z2,z3,z4,z5,z6]),(0,[z217,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z185,z6])],[(0,[z0,z2,z3,z4,z5,z6,z218]),(0,[z0,z2,z3,z219,z4,z5,z6]),(0,[z0,z2,z220,z3,z4,z5,z6]),(0,[z221,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z164,z185,z6])],[(0,[z0,z2,z3,z4,z222,z5,z6]),(0,[z0,z2,z3,z4,z87,z10,z6]),(0,[z0,z2,z3,z3,z4,z10,z6]),(0,[z0,z97,z2,z3,z4,z5,z85])]],
   [[(1,[z223,z224,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z225,z6]),(0,[z0,z2,z226,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z227,z6])],[(0,[z228,z0,z2,z3,z4,z5,z6]),(0,[z0,z107,z3,z4,z18,z5,z6]),(0,[z0,z229,z2,z3,z4,z5,z6]),(0,[z0,z230,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z98,z5,z145])],[(0,[z19,z0,z2,z3,z4,z231,z6]),(0,[z19,z0,z2,z3,z4,z5,z232]),(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z0,z233,z2,z3,z4,z5,z6]),(0,[z0,z234,z2,z3,z4,z5,z6]),(0,[z172,z0,z2,z3,z18,z5,z6]),(1,[z0,z2,z55,z4,z23,z6]),(0,[z0,z97,z2,z3,z4,z6,z85])],[(0,[z0,z2,z235,z3,z4,z5,z6]),(0,[z51,z0,z2,z3,z4,z10,z6]),(1,[z172,z0,z3,z52,z5,z6])],[(0,[z152,z0,z2,z3,z4,z23,z6]),(0,[z236,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z237,z4,z5,z6]),(0,[z0,z12,z2,z3,z4,z173,z6])],[(0,[z0,z238,z2,z3,z4,z5,z6]),(0,[z239,z2,z3,z36,z4,z5,z6]),(0,[z0,z2,z3,z52,z5,z95,z6])],[(0,[z172,z0,z2,z3,z4,z23,z6]),(0,[z240,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z241]),(0,[z156,z2,z3,z4,z5,z6,z88]),(0,[z0,z107,z2,z3,z18,z5,z6]),(0,[z0,z2,z3,z4,z242,z5,z6])],[(0,[z0,z2,z3,z4,z18,z5,z6]),(0,[z217,z0,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z5,z243,z6])],[(1,[z19,z86,z3,z4,z5,z6]),(0,[z140,z2,z3,z4,z87,z5,z6]),(0,[z0,z2,z3,z4,z244,z5,z6]),(0,[z245,z0,z2,z3,z4,z5,z6]),(0,[z0,z246,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z247,z4,z5,z6]),(0,[z0,z12,z2,z3,z4,z5,z6]),(0,[z0,z97,z2,z3,z4,z13,z6]),(0,[z0,z2,z3,z4,z5,z6,z85])],[(0,[z248,z0,z2,z3,z4,z5,z6]),(0,[z249,z0,z2,z3,z4,z5,z6]),(0,[z152,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z250,z6]),(0,[z0,z2,z4,z10,z5,z23,z6]),(0,[z0,z2,z3,z4,z23,z6,z85]),(1,[z0,z2,z3,z4,z5,z251]),(0,[z0,z2,z3,z17,z14,z5,z6])],[(0,[z0,z2,z3,z4,z252,z5,z6]),(0,[z239,z140,z2,z3,z4,z5,z6]),(0,[z253,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z254,z5,z6]),(0,[z0,z2,z3,z9,z4,z23,z6]),(1,[z0,z2,z3,z4,z108,z6]),(0,[z0,z2,z3,z4,z14,z23,z6]),(0,[z0,z2,z55,z3,z255,z5,z6])],[(0,[z256,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z47,z3,z4,z5,z6]),(0,[z257,z0,z2,z3,z4,z5,z6]),(0,[z0,z107,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z5,z258,z6]),(0,[z0,z12,z2,z3,z259,z5,z6]),(0,[z0,z260,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z5,z6,z84])],[(0,[z19,z0,z2,z3,z4,z23,z6]),(0,[z0,z2,z261,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z262,z5,z6]),(0,[z263,z0,z2,z3,z4,z5,z30]),(0,[z0,z24,z2,z3,z4,z5,z264]),(0,[z0,z15,z2,z3,z4,z5,z127]),(0,[z0,z2,z265,z3,z4,z5,z6])],[(0,[z152,z0,z2,z101,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z266]),(0,[z0,z2,z3,z36,z14,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z267]),(0,[z268,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z269,z6])]],
   [[(0,[z0,z2,z3,z270,z4,z5,z6]),(0,[z0,z2,z3,z271,z4,z5,z6]),(0,[z0,z2,z3,z272,z4,z5,z6]),(0,[z273,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z274,z4,z5,z6]),(0,[z0,z2,z275,z3,z4,z5,z6])],[(0,[z276,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z13,z6]),(0,[z0,z277,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z6,z278]),(0,[z0,z2,z3,z4,z5,z6,z279])],[(0,[z280,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z106,z4,z10,z6]),(0,[z140,z0,z2,z3,z36,z5,z6]),(0,[z0,z2,z3,z4,z23,z13,z6]),(0,[z0,z2,z55,z3,z4,z5,z127])],[(0,[z0,z107,z2,z3,z4,z10,z6]),(0,[z0,z154,z2,z3,z4,z5,z185]),(0,[z0,z2,z3,z4,z5,z6,z281]),(0,[z0,z2,z3,z282,z4,z5,z6])],[],[(1,[z0,z283,z2,z3,z5,z6]),(0,[z0,z60,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z10,z6,z85]),(1,[z0,z2,z3,z284,z4,z6])],[(0,[z224,z2,z86,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z285,z5,z6]),(0,[z0,z2,z3,z93,z87,z5,z6]),(0,[z0,z2,z3,z4,z5,z196,z264]),(0,[z286,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z196,z119]),(0,[z0,z2,z3,z4,z98,z5,z196]),(0,[z0,z2,z287,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z288,z5,z6]),(0,[z289,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z98,z5,z6])],[(0,[z290,z0,z2,z3,z4,z5,z88]),(1,[z74,z0,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z291,z5,z6]),(0,[z0,z2,z192,z3,z4,z10,z6]),(0,[z0,z292,z2,z3,z4,z5,z6])],[(0,[z19,z0,z86,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z293,z6]),(0,[z140,z0,z2,z3,z4,z5,z6])],[(0,[z168,z223,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z294,z4,z5,z6]),(0,[z295,z0,z2,z3,z4,z5,z6])],[(0,[z223,z0,z2,z3,z4,z10,z6]),(0,[z296,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z297]),(0,[z0,z2,z3,z259,z4,z5,z6]),(0,[z0,z2,z3,z4,z173,z5,z6]),(0,[z0,z2,z3,z272,z4,z23,z6]),(0,[z0,z2,z3,z298,z4,z5,z6])],[(0,[z0,z2,z3,z299,z4,z5,z6]),(0,[z300,z0,z2,z3,z4,z5,z6]),(0,[z301,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z302,z3,z4,z5,z6])],[(0,[z223,z224,z2,z3,z4,z5,z6]),(0,[z0,z2,z101,z3,z4,z5,z6]),(1,[z0,z2,z3,z303,z5,z6]),(0,[z0,z97,z2,z3,z4,z5,z88]),(0,[z0,z60,z2,z9,z4,z5,z6]),(0,[z0,z304,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z305,z5,z6]),(0,[z21,z0,z97,z2,z3,z4,z6]),(0,[z0,z2,z306,z3,z4,z5,z6]),(0,[z0,z307,z2,z3,z4,z5,z6]),(0,[z0,z71,z2,z55,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z196,z45]),(1,[z0,z2,z3,z4,z5,z123]),(0,[z0,z2,z55,z3,z4,z308,z6]),(0,[z0,z2,z3,z4,z5,z6,z309])],[(0,[z0,z2,z47,z106,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z310,z6]),(0,[z0,z2,z3,z311,z4,z5,z6]),(0,[z0,z2,z3,z312,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z313])],[(0,[z0,z314,z2,z3,z4,z5,z6]),(0,[z315,z0,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z316,z5,z6]),(0,[z0,z2,z3,z317,z4,z5,z6]),(0,[z200,z0,z2,z55,z4,z5,z6])],[(0,[z0,z2,z3,z5,z213,z6,z88]),(1,[z0,z12,z3,z4,z13,z6]),(0,[z0,z71,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z318,z5,z6]),(0,[z0,z2,z3,z4,z5,z319,z6])],[(0,[z168,z0,z2,z3,z4,z10,z6]),(0,[z0,z320,z2,z3,z4,z5,z6]),(0,[z140,z0,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z321,z4,z5,z6]),(0,[z0,z2,z3,z4,z180,z10,z6]),(0,[z0,z15,z2,z3,z180,z5,z6]),(0,[z0,z2,z55,z3,z4,z322,z6]),(0,[z0,z2,z3,z14,z5,z185,z6])],[(0,[z323,z0,z2,z3,z4,z5,z6]),(0,[z324,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z325,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z7,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z326]),(0,[z0,z2,z3,z327,z4,z5,z6]),(0,[z0,z2,z3,z328,z4,z10,z6])]],
   [[(0,[z0,z2,z3,z4,z173,z23,z6]),(0,[z200,z0,z2,z3,z4,z10,z6])],[(0,[z0,z2,z3,z4,z5,z329,z6]),(0,[z0,z2,z3,z330,z4,z5,z6]),(0,[z0,z2,z3,z4,z331,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z88]),(0,[z0,z2,z3,z332,z4,z5,z6]),(0,[z0,z2,z333,z3,z4,z5,z6])],[(0,[z334,z0,z2,z3,z4,z5,z6]),(0,[z335,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z101,z3,z4,z23,z6]),(0,[z156,z0,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z5,z30,z88]),(0,[z0,z2,z3,z4,z23,z6,z88]),(0,[z290,z2,z3,z4,z5,z196,z6]),(0,[z0,z31,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z336,z4,z5,z6]),(1,[z0,z2,z3,z44,z5,z95])],[(0,[z19,z0,z2,z337,z4,z5,z6]),(1,[z0,z2,z3,z4,z231,z6]),(1,[z0,z2,z3,z4,z5,z232])],[(0,[z0,z2,z3,z4,z231,z5,z6]),(0,[z0,z2,z338,z3,z4,z5,z6]),(0,[z0,z339,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z340,z4,z5,z6]),(0,[z341,z0,z2,z3,z4,z5,z6])],[(0,[z342,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z343,z4,z5,z6]),(0,[z344,z0,z2,z3,z4,z5,z6]),(0,[z0,z345,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z346,z6])],[(0,[z21,z0,z2,z3,z4,z10,z6]),(1,[z0,z2,z3,z4,z347,z6]),(0,[z0,z2,z3,z348,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z349,z6])],[(0,[z0,z2,z3,z4,z5,z350,z6]),(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z87,z5,z6]),(0,[z0,z351,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z181,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z352,z6]),(0,[z263,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z93,z5,z95,z6]),(0,[z353,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z354,z5,z6])],[(0,[z140,z0,z15,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z355,z6]),(0,[z0,z15,z2,z3,z93,z5,z6]),(0,[z0,z2,z3,z164,z5,z185,z6]),(0,[z356,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z101,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z357,z5,z6]),(0,[z0,z2,z358,z3,z4,z5,z6])],[(0,[z51,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z359,z5,z6]),(0,[z0,z2,z360,z3,z4,z5,z6])],[(0,[z0,z2,z3,z17,z4,z145,z6])],[(0,[z0,z2,z3,z4,z10,z6,z88]),(0,[z0,z361,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z362,z6])],[(0,[z0,z2,z3,z363,z4,z5,z6]),(0,[z364,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z365,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z366]),(0,[z0,z2,z3,z4,z10,z8,z6]),(0,[z0,z2,z3,z4,z5,z367,z6]),(0,[z0,z2,z3,z368,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z369]),(1,[z0,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z10,z354,z6]),(0,[z0,z2,z3,z4,z370,z10,z6])]],
   [[(0,[z168,z2,z86,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z173,z7,z6]),(0,[z0,z2,z371,z3,z4,z5,z6]),(0,[z0,z2,z32,z3,z4,z23,z6]),(0,[z0,z2,z3,z44,z4,z10,z6]),(0,[z0,z372,z2,z3,z4,z5,z6]),(0,[z0,z2,z373,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z374])],[(0,[z0,z86,z3,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z375,z5,z6]),(0,[z0,z2,z3,z4,z5,z376,z6])],[(0,[z377,z0,z2,z3,z4,z5,z6]),(0,[z21,z0,z2,z3,z4,z5,z378]),(0,[z0,z2,z3,z4,z23,z196,z6]),(0,[z0,z379,z2,z3,z4,z5,z6]),(0,[z0,z15,z2,z3,z5,z6,z45])],[(0,[z380,z0,z2,z3,z4,z5,z6]),(0,[z152,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z25,z5,z6]),(1,[z0,z2,z32,z180,z5,z6]),(0,[z0,z2,z3,z17,z4,z185,z6])],[(0,[z0,z2,z3,z381,z4,z5,z6]),(0,[z290,z0,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z5,z6,z382]),(0,[z0,z2,z3,z4,z5,z383,z6])],[(0,[z0,z384,z2,z3,z4,z5,z6]),(0,[z0,z385,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z264,z119]),(0,[z0,z2,z3,z386,z4,z5,z6]),(0,[z0,z387,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z388,z5,z6])],[(0,[z0,z389,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z390,z5,z6]),(0,[z0,z2,z3,z4,z14,z173,z6]),(1,[z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z391,z5,z6])],[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z392,z0,z2,z3,z4,z5,z6]),(0,[z152,z2,z3,z106,z4,z5,z6]),(0,[z51,z0,z2,z3,z4,z23,z6]),(1,[z156,z2,z3,z4,z5,z88]),(0,[z74,z0,z2,z3,z130,z5,z6]),(1,[z0,z2,z3,z4,z5,z393]),(0,[z0,z394,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z395]),(0,[z0,z2,z3,z4,z98,z145,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z396]),(0,[z0,z2,z3,z397,z4,z5,z6]),(0,[z0,z398,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z399,z5,z6]),(0,[z0,z2,z3,z4,z5,z347,z6])],[(0,[z400,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z401])],[(0,[z402,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z189,z6])],[(0,[z0,z2,z3,z403,z4,z5,z6]),(0,[z290,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z9,z4,z5,z6]),(1,[z48,z0,z3,z4,z173,z6]),(1,[z263,z0,z3,z4,z5,z264]),(0,[z0,z2,z3,z4,z5,z6,z404]),(0,[z0,z2,z3,z4,z14,z5,z6]),(0,[z0,z405,z2,z3,z4,z5,z6])],[(0,[z0,z107,z2,z3,z4,z5,z6])],[(0,[z19,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z196,z6]),(0,[z0,z2,z3,z406,z4,z5,z6]),(0,[z0,z2,z407,z3,z4,z5,z6]),(0,[z0,z2,z408,z3,z4,z5,z6])],[(0,[z409,z0,z2,z3,z4,z5,z6]),(0,[z21,z2,z3,z4,z7,z5,z6]),(1,[z0,z2,z3,z4,z410,z6]),(0,[z0,z2,z3,z4,z411,z5,z6]),(0,[z0,z412,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z413,z10,z6]),(0,[z414,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z415,z4,z5,z6]),(0,[z416,z0,z2,z3,z4,z5,z6])],[(0,[z140,z0,z2,z3,z87,z5,z6]),(0,[z239,z0,z2,z3,z4,z10,z6]),(0,[z21,z0,z2,z3,z4,z5,z417])]],
   [[(0,[z0,z2,z3,z4,z5,z95,z196]),(0,[z0,z97,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z164,z17,z5,z6]),(0,[z0,z2,z3,z4,z5,z95,z6])],[(0,[z0,z2,z3,z4,z23,z95,z6])],[(0,[z0,z2,z3,z418,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z378]),(0,[z0,z2,z3,z419,z4,z5,z6]),(0,[z0,z2,z3,z164,z4,z14,z6])],[(0,[z0,z2,z3,z18,z5,z185,z6]),(0,[z0,z2,z3,z4,z420,z5,z6]),(0,[z0,z2,z3,z421,z4,z23,z6]),(0,[z0,z2,z3,z4,z5,z6,z422])],[(0,[z0,z2,z2,z3,z4,z5,z6]),(0,[z152,z0,z2,z3,z274,z5,z6]),(0,[z0,z2,z3,z4,z423,z5,z6]),(0,[z0,z2,z3,z111,z4,z5,z6]),(0,[z0,z2,z3,z4,z424,z5,z6]),(0,[z0,z2,z425,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z426,z6]),(0,[z0,z2,z55,z3,z116,z5,z6])],[(0,[z0,z2,z427,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z428]),(0,[z0,z60,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z357,z6]),(0,[z0,z429,z2,z3,z4,z5,z6]),(0,[z0,z430,z2,z3,z4,z23,z6]),(0,[z431,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z127,z6]),(0,[z0,z2,z3,z432,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z433])],[(0,[z434,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z435,z3,z4,z5,z6]),(0,[z0,z436,z2,z3,z4,z5,z6]),(0,[z437,z0,z2,z3,z4,z5,z6]),(0,[z0,z438,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z23,z127,z6])],[(0,[z19,z0,z2,z3,z252,z5,z6]),(0,[z0,z2,z3,z106,z4,z23,z6]),(0,[z0,z2,z439,z3,z4,z5,z6]),(0,[z440,z0,z2,z3,z4,z5,z6]),(0,[z51,z0,z2,z3,z4,z7,z6]),(0,[z0,z2,z3,z4,z5,z6,z441]),(0,[z442,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z443]),(0,[z0,z31,z2,z3,z4,z5,z123]),(0,[z0,z2,z444,z3,z4,z5,z6]),(0,[z0,z445,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z446,z6]),(0,[z0,z2,z3,z447,z4,z5,z6]),(0,[z0,z112,z2,z3,z4,z5,z6])],[(0,[z21,z0,z2,z3,z303,z5,z6]),(0,[z0,z2,z3,z4,z410,z6,z88]),(1,[z314,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z448,z4,z5,z6]),(1,[z0,z2,z3,z4,z449,z6]),(0,[z0,z450,z2,z3,z4,z5,z6])],[(0,[z315,z0,z2,z3,z4,z5,z6]),(0,[z19,z0,z2,z381,z4,z5,z6]),(0,[z0,z451,z2,z3,z4,z5,z6]),(1,[z125,z2,z3,z4,z5,z6]),(0,[z74,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z452,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z453,z6]),(0,[z0,z2,z32,z3,z4,z449,z6])],[(0,[z454,z0,z2,z3,z4,z5,z6]),(0,[z74,z0,z2,z3,z4,z5,z393]),(1,[z0,z2,z3,z4,z25,z6])],[(1,[z0,z2,z337,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z393]),(1,[z0,z2,z3,z4,z455,z6]),(0,[z0,z2,z3,z4,z10,z95,z6]),(0,[z0,z71,z2,z3,z4,z5,z6]),(1,[z356,z2,z3,z4,z5,z6])],[(0,[z19,z0,z224,z3,z4,z5,z6]),(0,[z456,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z457,z4,z5,z6]),(0,[z0,z2,z192,z3,z4,z23,z6]),(0,[z0,z2,z3,z164,z4,z10,z6])],[],[(0,[z117,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z417]),(0,[z0,z2,z3,z52,z180,z5,z6]),(1,[z0,z31,z2,z93,z5,z6]),(0,[z0,z2,z3,z328,z4,z5,z6])]],
   [[(0,[z223,z0,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z5,z266,z6]),(0,[z0,z2,z3,z4,z5,z410,z6]),(1,[z0,z2,z3,z458,z5,z6]),(0,[z0,z24,z2,z3,z4,z5,z30]),(0,[z0,z31,z2,z93,z4,z5,z6]),(0,[z200,z0,z2,z192,z4,z5,z6])],[],[(0,[z0,z2,z3,z4,z5,z6,z459]),(0,[z0,z460,z2,z3,z4,z5,z6]),(0,[z461,z0,z2,z3,z4,z5,z6]),(0,[z0,z462,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z463,z6]),(0,[z464,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z465,z5,z6]),(0,[z466,z0,z2,z3,z4,z5,z6]),(0,[z467,z0,z2,z3,z4,z5,z6]),(1,[z339,z2,z3,z4,z5,z6])],[(0,[z152,z168,z2,z3,z4,z5,z6]),(0,[z0,z468,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z13,z185,z6]),(0,[z0,z2,z3,z4,z10,z10,z6]),(0,[z0,z2,z3,z4,z469,z5,z6]),(0,[z0,z2,z3,z4,z98,z5,z85])],[(0,[z0,z60,z224,z3,z4,z5,z6]),(0,[z0,z2,z470,z3,z4,z5,z6]),(0,[z0,z97,z2,z3,z164,z4,z6])],[(1,[z239,z2,z3,z36,z5,z6]),(0,[z21,z0,z2,z3,z4,z5,z6]),(0,[z315,z0,z2,z3,z4,z23,z6])],[(0,[z0,z2,z471,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z472,z6]),(1,[z0,z2,z3,z4,z61,z6]),(0,[z0,z15,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z6,z473])]],
   [[(0,[z474,z0,z2,z3,z4,z5,z6]),(0,[z475,z0,z2,z3,z4,z5,z6]),(0,[z140,z0,z2,z3,z5,z95,z6]),(0,[z74,z0,z60,z3,z4,z5,z6]),(0,[z0,z2,z3,z476,z4,z5,z6]),(0,[z0,z71,z2,z3,z4,z23,z6]),(1,[z0,z2,z477,z4,z5,z6])],[(0,[z0,z2,z101,z3,z4,z478,z6]),(0,[z239,z2,z3,z4,z5,z6,z88]),(0,[z0,z2,z3,z4,z479,z5,z6]),(0,[z156,z0,z2,z3,z4,z5,z6]),(0,[z156,z0,z2,z3,z4,z5,z196]),(0,[z0,z2,z3,z4,z5,z196,z30]),(0,[z0,z2,z3,z480,z4,z5,z6]),(0,[z74,z0,z2,z3,z4,z357,z6]),(0,[z0,z2,z3,z4,z10,z13,z6]),(0,[z0,z2,z3,z4,z5,z6,z264]),(0,[z158,z0,z2,z3,z4,z5,z6]),(0,[z0,z481,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z145,z6,z85])],[(0,[z168,z0,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z5,z6,z482]),(0,[z0,z2,z3,z483,z4,z5,z6]),(0,[z0,z2,z484,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z180,z23,z6])],[(1,[z168,z2,z101,z4,z5,z6]),(0,[z290,z2,z3,z4,z87,z5,z6]),(0,[z0,z2,z3,z4,z5,z88,z264]),(0,[z0,z2,z3,z485,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z449,z6]),(0,[z0,z2,z486,z3,z4,z5,z6]),(0,[z487,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z488,z6])],[(0,[z223,z0,z86,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z88,z119]),(0,[z200,z0,z2,z3,z4,z23,z6]),(0,[z0,z2,z55,z3,z4,z10,z6])],[(0,[z2,z86,z3,z106,z4,z5,z6]),(0,[z140,z0,z2,z3,z4,z5,z489]),(0,[z0,z2,z3,z36,z180,z5,z6]),(0,[z490,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z6,z491])],[(0,[z152,z0,z2,z3,z4,z5,z293]),(0,[z0,z2,z3,z492,z4,z5,z6]),(0,[z74,z125,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z455,z6]),(0,[z0,z31,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z72,z5,z6])],[(0,[z0,z493,z2,z3,z4,z5,z6]),(0,[z494,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z495,z6]),(0,[z0,z2,z3,z4,z370,z5,z6]),(0,[z0,z2,z3,z4,z5,z251,z6]),(0,[z0,z97,z2,z3,z44,z4,z5])]],
   [[(0,[z0,z2,z3,z4,z496,z5,z6]),(0,[z0,z2,z3,z497,z4,z5,z6]),(0,[z0,z24,z3,z4,z5,z30,z6]),(0,[z0,z2,z3,z4,z203,z5,z6]),(1,[z0,z2,z3,z498,z5,z6])],[(0,[z0,z2,z3,z499,z4,z5,z6]),(0,[z0,z2,z3,z4,z40,z5,z6])],[(0,[z0,z2,z500,z3,z4,z5,z6]),(0,[z21,z0,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z501,z5,z6]),(0,[z0,z502,z2,z3,z4,z5,z6]),(0,[z503,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z284,z4,z5,z6]),(0,[z0,z97,z2,z477,z4,z5,z6])],[(1,[z0,z2,z340,z4,z5,z6])],[(0,[z19,z0,z2,z3,z299,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z417]),(0,[z0,z2,z3,z4,z5,z88,z45]),(0,[z74,z0,z2,z3,z458,z5,z6]),(0,[z0,z2,z3,z52,z5,z185,z6]),(0,[z263,z0,z2,z3,z4,z23,z6])],[(0,[z168,z0,z2,z101,z4,z5,z6]),(0,[z0,z2,z3,z255,z4,z5,z6]),(0,[z0,z2,z3,z504,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z478,z6]),(0,[z0,z505,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z127,z264]),(0,[z0,z2,z93,z4,z180,z5,z6])],[(0,[z0,z2,z47,z3,z4,z11,z6]),(0,[z0,z24,z2,z3,z174,z5,z6]),(0,[z0,z2,z32,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z488,z6]),(1,[z0,z71,z2,z4,z5,z119])]],
   [[(0,[z239,z0,z2,z3,z36,z5,z6]),(0,[z0,z24,z2,z3,z179,z5,z6])],[(0,[z0,z506,z2,z3,z4,z5,z6]),(0,[z507,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z508,z6]),(0,[z0,z12,z2,z3,z40,z5,z6]),(1,[z0,z2,z3,z259,z5,z6]),(0,[z0,z2,z3,z4,z23,z346,z6])],[(0,[z152,z0,z2,z3,z375,z5,z6]),(0,[z0,z2,z3,z509,z4,z5,z6]),(0,[z0,z2,z3,z510,z4,z5,z6])],[(0,[z0,z2,z511,z3,z4,z5,z6]),(0,[z290,z0,z2,z3,z4,z5,z6]),(0,[z0,z97,z2,z3,z4,z173,z6]),(1,[z0,z97,z2,z3,z4,z85])],[(0,[z0,z2,z3,z4,z5,z512,z6]),(0,[z0,z2,z3,z44,z4,z23,z6])],[(0,[z0,z2,z3,z513,z4,z5,z6]),(0,[z514,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z55,z4,z5,z127]),(0,[z0,z2,z3,z4,z5,z515,z6])],[(1,[z0,z2,z3,z4,z5,z516]),(0,[z0,z71,z2,z3,z4,z5,z119]),(0,[z0,z2,z3,z4,z5,z517,z6]),(0,[z0,z2,z3,z518,z4,z5,z6])],[(0,[z239,z0,z2,z3,z4,z5,z6]),(0,[z519,z0,z2,z3,z4,z5,z6]),(0,[z172,z0,z107,z3,z4,z5,z6]),(0,[z0,z107,z2,z3,z4,z520,z6]),(0,[z0,z2,z3,z521,z4,z5,z6]),(0,[z0,z522,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z523,z6]),(0,[z0,z2,z3,z4,z5,z6,z491])]],
   [[(1,[z0,z2,z3,z252,z5,z6]),(0,[z0,z2,z524,z3,z4,z5,z6]),(0,[z168,z2,z101,z3,z4,z5,z6]),(0,[z0,z2,z525,z3,z4,z5,z6]),(0,[z0,z2,z3,z179,z4,z5,z6]),(0,[z0,z2,z3,z526,z4,z5,z6]),(0,[z0,z97,z2,z3,z4,z5,z6])],[(0,[z527,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z36,z5,z6,z45]),(0,[z74,z0,z3,z9,z4,z5,z6])],[(0,[z239,z0,z2,z3,z5,z95,z6]),(0,[z528,z0,z2,z3,z4,z5,z6]),(0,[z0,z529,z2,z3,z4,z5,z6]),(0,[z21,z0,z2,z3,z4,z7,z6]),(0,[z0,z2,z3,z4,z5,z6,z530]),(0,[z15,z339,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z531,z5,z6])],[(1,[z0,z2,z381,z4,z5,z6]),(0,[z0,z2,z3,z4,z532,z5,z6]),(0,[z0,z2,z3,z533,z4,z5,z6]),(0,[z0,z2,z3,z4,z98,z5,z88]),(0,[z0,z2,z3,z4,z5,z534,z6]),(0,[z0,z2,z3,z4,z5,z6,z535]),(0,[z0,z2,z3,z498,z5,z6,z85])],[],[(0,[z0,z2,z3,z4,z5,z536,z6]),(0,[z0,z2,z537,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z538,z6]),(0,[z431,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z14,z5,z95,z6])],[(0,[z0,z2,z3,z164,z36,z5,z6]),(0,[z539,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z540,z5,z6]),(0,[z0,z2,z3,z541,z4,z5,z6])],[(1,[z0,z2,z3,z274,z5,z6]),(0,[z542,z0,z2,z3,z4,z5,z6]),(0,[z543,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z544,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z545]),(0,[z0,z2,z3,z4,z5,z6,z546])],[(0,[z263,z0,z2,z3,z4,z5,z264]),(0,[z0,z2,z4,z5,z23,z6,z119]),(0,[z356,z15,z2,z3,z4,z5,z6]),(0,[z0,z2,z547,z3,z4,z5,z6]),(0,[z548,z0,z2,z3,z4,z5,z6])],[(0,[z549,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z550]),(0,[z0,z2,z551,z3,z4,z5,z6]),(0,[z156,z0,z2,z3,z316,z5,z6]),(0,[z74,z0,z2,z3,z4,z5,z6]),(0,[z0,z60,z2,z47,z4,z5,z6]),(0,[z48,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z421,z4,z5,z6])],[(0,[z239,z0,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z0,z2,z3,z4,z108,z5,z6]),(0,[z0,z31,z2,z3,z4,z455,z6])],[(0,[z0,z2,z3,z4,z173,z8,z6]),(0,[z0,z2,z3,z552,z4,z5,z6]),(0,[z0,z2,z553,z3,z4,z5,z6]),(0,[z0,z15,z2,z3,z52,z5,z6]),(0,[z0,z2,z3,z4,z174,z5,z6]),(0,[z0,z554,z2,z3,z4,z5,z6]),(0,[z0,z430,z2,z3,z4,z5,z6]),(0,[z0,z97,z2,z3,z4,z23,z6])],[(0,[z555,z0,z2,z3,z4,z5,z6]),(0,[z556,z0,z2,z3,z4,z5,z6]),(0,[z0,z277,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z164,z4,z5,z6]),(0,[z557,z0,z2,z3,z4,z5,z6]),(0,[z558,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z106,z4,z5,z6]),(0,[z0,z2,z559,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z173,z145,z6]),(0,[z560,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z561,z6]),(0,[z48,z0,z2,z3,z4,z13,z6]),(0,[z0,z2,z3,z4,z562,z5,z6])]],
   [[],[(0,[z0,z2,z563,z3,z4,z5,z6]),(0,[z0,z2,z3,z18,z87,z5,z6]),(0,[z0,z2,z3,z4,z5,z378,z6])],[(0,[z0,z2,z3,z564,z4,z5,z6]),(0,[z0,z3,z4,z173,z5,z13,z6]),(0,[z0,z2,z3,z4,z540,z23,z6])],[(0,[z0,z2,z3,z4,z5,z6,z489]),(0,[z0,z2,z3,z4,z565,z5,z6]),(0,[z566,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z516])],[(0,[z0,z2,z567,z3,z4,z5,z6]),(0,[z2,z3,z36,z4,z87,z5,z6]),(0,[z0,z2,z568,z3,z4,z5,z6]),(0,[z0,z2,z192,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z23,z6]),(0,[z0,z2,z569,z3,z4,z5,z6])],[(0,[z152,z0,z570,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z135,z5,z6]),(0,[z0,z2,z3,z4,z173,z185,z6]),(0,[z0,z2,z3,z4,z5,z6,z571]),(0,[z0,z2,z3,z4,z23,z23,z6]),(0,[z0,z2,z3,z4,z5,z572,z6])],[(0,[z239,z0,z15,z2,z3,z5,z6]),(0,[z573,z0,z2,z3,z4,z5,z6]),(0,[z74,z0,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z5,z6,z574])],[(0,[z223,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z575,z3,z4,z5,z6]),(0,[z0,z576,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z316,z5,z6]),(0,[z0,z2,z3,z4,z577,z5,z6]),(0,[z0,z2,z3,z17,z4,z14,z6]),(0,[z0,z15,z2,z3,z4,z5,z6])]],
   [[(0,[z19,z0,z2,z3,z4,z578,z6]),(0,[z0,z2,z3,z4,z5,z213,z6]),(0,[z0,z2,z3,z4,z5,z127,z196]),(0,[z0,z579,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z52,z4,z10,z6]),(0,[z0,z2,z3,z4,z580,z5,z6]),(0,[z0,z71,z2,z3,z4,z5,z127]),(0,[z0,z2,z477,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z581,z6]),(0,[z0,z2,z3,z164,z4,z23,z6])],[(0,[z152,z0,z2,z106,z4,z5,z6]),(0,[z0,z2,z3,z87,z14,z5,z6]),(0,[z582,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z583,z4,z5,z6])],[(0,[z223,z2,z3,z106,z4,z5,z6]),(0,[z156,z0,z2,z3,z111,z5,z6]),(0,[z584,z0,z2,z3,z4,z5,z6]),(0,[z585,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z586]),(0,[z0,z2,z3,z4,z5,z6,z587])],[(0,[z588,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z589]),(0,[z0,z2,z3,z4,z23,z446,z6]),(0,[z0,z2,z3,z4,z590,z23,z6])],[(1,[z0,z2,z3,z299,z5,z6]),(0,[z0,z2,z3,z44,z87,z5,z6]),(0,[z239,z290,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z196,z6,z88]),(0,[z0,z2,z3,z4,z5,z6,z591]),(0,[z0,z15,z2,z3,z44,z5,z6]),(0,[z0,z2,z3,z4,z592,z5,z6])],[(0,[z0,z2,z3,z4,z13,z8,z6]),(0,[z74,z0,z2,z9,z4,z5,z6]),(0,[z0,z47,z3,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z18,z10,z6]),(0,[z0,z15,z2,z3,z18,z5,z6]),(0,[z0,z2,z32,z4,z180,z5,z6]),(0,[z0,z2,z3,z4,z6,z491,z45])],[(0,[z0,z224,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z593,z4,z5,z6]),(0,[z0,z594,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z251,z185]),(0,[z0,z2,z3,z284,z4,z6,z45])]],
   [[(0,[z0,z2,z3,z4,z478,z5,z6]),(0,[z0,z2,z3,z4,z13,z145,z6]),(0,[z0,z2,z3,z4,z10,z23,z6]),(0,[z0,z595,z2,z3,z4,z5,z6])],[(0,[z168,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z293]),(0,[z0,z2,z3,z4,z5,z596,z6]),(0,[z0,z2,z3,z4,z180,z5,z6]),(0,[z0,z2,z3,z597,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z598]),(0,[z0,z599,z2,z3,z4,z5,z6]),(0,[z0,z2,z47,z3,z4,z10,z6]),(0,[z0,z2,z3,z600,z4,z5,z6]),(0,[z0,z2,z3,z17,z4,z10,z6])],[(0,[z51,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z601,z5,z6]),(0,[z0,z2,z3,z458,z4,z5,z6]),(0,[z200,z0,z2,z3,z4,z5,z6]),(0,[z0,z15,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z5,z602,z6])],[(0,[z152,z0,z2,z3,z4,z100,z6]),(0,[z0,z12,z2,z3,z4,z13,z6]),(0,[z0,z603,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z127,z6])],[(0,[z0,z2,z3,z4,z5,z604,z6]),(0,[z51,z0,z2,z3,z4,z145,z6]),(0,[z0,z2,z3,z605,z4,z5,z6]),(0,[z0,z606,z2,z3,z4,z5,z6]),(0,[z607,z0,z2,z3,z4,z5,z6]),(0,[z0,z608,z2,z3,z4,z5,z6]),(0,[z0,z31,z2,z3,z4,z5,z6]),(0,[z609,z0,z2,z3,z4,z5,z6])],[(0,[z0,z224,z2,z3,z4,z10,z6]),(0,[z0,z2,z570,z3,z4,z5,z6]),(0,[z610,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z36,z4,z10,z6]),(0,[z290,z156,z2,z3,z4,z5,z6]),(0,[z0,z611,z2,z3,z4,z5,z6])],[(0,[z223,z0,z224,z3,z4,z5,z6]),(0,[z152,z0,z2,z3,z4,z5,z20]),(0,[z0,z2,z612,z3,z4,z5,z6]),(0,[z0,z15,z2,z3,z4,z98,z5])]],
   [[(0,[z50,z0,z2,z3,z4,z23,z6]),(0,[z0,z2,z55,z3,z4,z23,z6])],[(0,[z0,z2,z613,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z614,z5,z6]),(0,[z0,z2,z3,z303,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z615,z6]),(1,[z0,z2,z3,z4,z520,z6]),(0,[z0,z2,z3,z4,z5,z6,z616]),(0,[z0,z154,z2,z3,z4,z5,z6]),(0,[z0,z617,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z18,z5,z95,z6]),(0,[z0,z2,z3,z4,z618,z5,z6]),(0,[z619,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z620]),(0,[z0,z2,z3,z4,z621,z5,z6]),(0,[z0,z2,z3,z4,z5,z622,z6])],[(0,[z0,z2,z623,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z624,z6]),(0,[z0,z2,z3,z4,z5,z6,z625]),(0,[z263,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z255,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z626]),(0,[z239,z0,z2,z3,z87,z5,z6]),(0,[z0,z2,z3,z44,z36,z5,z6]),(0,[z0,z2,z3,z4,z627,z5,z6]),(0,[z628,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z629,z5,z6]),(0,[z0,z2,z3,z4,z109,z5,z6]),(0,[z0,z2,z3,z44,z4,z5,z95]),(0,[z0,z97,z2,z3,z4,z5,z145])],[(1,[z0,z2,z3,z375,z5,z6]),(0,[z0,z2,z3,z87,z180,z5,z6]),(0,[z0,z283,z2,z3,z5,z6,z88]),(0,[z0,z2,z3,z4,z23,z6,z264]),(0,[z0,z630,z2,z3,z4,z5,z6]),(0,[z0,z31,z2,z3,z4,z5,z516]),(0,[z0,z2,z3,z4,z5,z6,z119]),(0,[z0,z2,z3,z4,z5,z6,z631])],[(0,[z0,z2,z3,z4,z632,z5,z6]),(0,[z0,z2,z3,z633,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z30,z119]),(0,[z0,z2,z192,z4,z5,z23,z6]),(0,[z0,z2,z3,z4,z23,z6,z119]),(0,[z0,z2,z3,z4,z308,z5,z6])],[(0,[z0,z2,z3,z634,z4,z5,z6]),(0,[z635,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z145,z6])]],
   [[(0,[z74,z314,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z636])],[(0,[z0,z2,z3,z637,z4,z5,z6]),(0,[z0,z2,z638,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z639])],[(0,[z0,z2,z640,z3,z4,z5,z6]),(0,[z641,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z642,z6]),(0,[z0,z2,z3,z4,z5,z95,z88]),(0,[z0,z2,z3,z4,z5,z643,z6]),(0,[z644,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z645,z6]),(0,[z0,z2,z3,z44,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z646,z6]),(0,[z0,z2,z3,z647,z4,z5,z6]),(0,[z0,z648,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z65]),(0,[z0,z2,z649,z3,z4,z5,z6]),(0,[z650,z0,z2,z3,z4,z5,z6]),(0,[z651,z0,z2,z3,z4,z5,z6]),(0,[z0,z24,z2,z3,z4,z347,z6]),(0,[z0,z2,z3,z4,z10,z6,z616]),(0,[z0,z2,z3,z4,z5,z6,z45])],[(0,[z0,z2,z86,z3,z4,z10,z6]),(0,[z0,z2,z3,z652,z4,z5,z6]),(1,[z0,z107,z3,z18,z5,z6]),(0,[z0,z2,z3,z4,z653,z5,z6]),(0,[z0,z2,z3,z4,z23,z6,z45]),(0,[z0,z2,z3,z4,z5,z185,z6]),(0,[z0,z2,z3,z44,z5,z95,z6])],[(1,[z0,z15,z2,z3,z5,z45])]],
   [[(0,[z0,z2,z3,z654,z4,z5,z6]),(0,[z0,z2,z655,z3,z4,z5,z6]),(0,[z0,z2,z3,z656,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z6,z264])],[(0,[z0,z2,z3,z657,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z658,z6]),(0,[z0,z659,z2,z3,z4,z5,z6]),(0,[z660,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z6,z119]),(0,[z0,z15,z2,z3,z4,z5,z119])],[(0,[z19,z0,z2,z3,z4,z5,z65]),(0,[z0,z2,z3,z164,z87,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z661]),(0,[z172,z0,z3,z52,z4,z5,z6]),(1,[z0,z2,z3,z4,z72,z6])],[(0,[z0,z2,z337,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z662,z5,z6]),(0,[z0,z663,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z520,z6]),(1,[z0,z2,z3,z4,z109,z6])],[(0,[z0,z2,z3,z664,z4,z5,z6]),(0,[z263,z0,z24,z3,z4,z5,z6])],[(0,[z665,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z666]),(0,[z0,z2,z3,z4,z5,z6,z667]),(0,[z120,z0,z2,z3,z4,z10,z6])],[(0,[z668,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z669,z6]),(0,[z290,z0,z2,z3,z4,z5,z196]),(0,[z0,z2,z670,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z671,z6]),(0,[z0,z2,z3,z4,z5,z6,z672]),(0,[z0,z2,z55,z3,z4,z5,z119]),(0,[z0,z2,z3,z498,z4,z5,z6])],[(0,[z673,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z209,z5,z6]),(0,[z0,z2,z32,z3,z4,z203,z6]),(1,[z0,z2,z3,z4,z308,z6])]],
   [[(0,[z263,z0,z3,z4,z5,z6,z264]),(0,[z0,z2,z3,z4,z5,z127,z30]),(0,[z0,z2,z3,z4,z23,z512,z6]),(0,[z0,z97,z2,z340,z4,z5,z6])],[(1,[z0,z2,z3,z4,z578,z6]),(1,[z0,z2,z3,z4,z5,z489]),(0,[z674,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z52,z36,z5,z6]),(0,[z0,z2,z3,z4,z7,z13,z6]),(0,[z0,z2,z3,z4,z413,z5,z6]),(0,[z0,z175,z2,z3,z4,z23,z6])],[(0,[z0,z2,z3,z4,z675,z5,z6]),(0,[z0,z2,z3,z93,z4,z10,z6]),(0,[z0,z2,z3,z4,z116,z5,z6])],[(0,[z140,z0,z2,z3,z4,z5,z266]),(0,[z0,z97,z2,z3,z4,z5,z196]),(0,[z0,z2,z47,z3,z4,z61,z6]),(0,[z0,z2,z3,z4,z676,z5,z6]),(0,[z677,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z44,z4,z98,z5])],[(0,[z0,z2,z3,z4,z5,z6,z678])],[(0,[z679,z0,z2,z3,z4,z5,z6]),(0,[z0,z24,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z680,z5,z6]),(0,[z681,z0,z2,z3,z4,z5,z6]),(0,[z0,z682,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z322,z6]),(0,[z0,z2,z3,z683,z4,z5,z6])],[(0,[z51,z21,z2,z3,z4,z5,z6]),(0,[z48,z0,z2,z3,z4,z23,z6]),(0,[z0,z97,z2,z3,z17,z4,z6]),(1,[z0,z2,z3,z4,z98,z145])],[(0,[z152,z0,z181,z3,z4,z5,z6]),(0,[z0,z2,z3,z684,z4,z5,z6]),(0,[z0,z2,z3,z4,z130,z5,z6]),(0,[z0,z2,z3,z17,z52,z5,z6])]],
   [[(0,[z0,z685,z2,z3,z4,z5,z6]),(1,[z0,z570,z3,z4,z5,z6]),(0,[z0,z2,z3,z52,z4,z5,z6]),(0,[z0,z3,z4,z5,z30,z6,z264])],[(0,[z0,z283,z2,z3,z4,z5,z6]),(0,[z665,z0,z2,z3,z4,z23,z6])],[(0,[z0,z2,z3,z686,z4,z5,z6])],[(0,[z0,z2,z3,z687,z4,z5,z6]),(0,[z0,z2,z32,z3,z180,z5,z6])],[(0,[z688,z0,z2,z3,z4,z5,z6]),(0,[z156,z0,z2,z3,z4,z5,z88]),(0,[z0,z2,z3,z4,z23,z6,z545])],[(0,[z0,z224,z3,z9,z4,z5,z6]),(0,[z48,z0,z3,z4,z173,z5,z6]),(0,[z0,z2,z3,z689,z4,z5,z6])],[(0,[z21,z0,z2,z3,z4,z8,z6])],[(0,[z19,z223,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z690,z6]),(0,[z0,z2,z3,z691,z4,z5,z6]),(0,[z0,z2,z692,z3,z4,z5,z6]),(0,[z693,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z30,z6]),(0,[z694,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z695,z6]),(0,[z0,z2,z3,z4,z676,z23,z6])]],
   [[(0,[z152,z0,z2,z3,z4,z209,z6]),(0,[z0,z696,z2,z3,z4,z5,z6]),(0,[z21,z0,z2,z3,z4,z145,z6]),(1,[z0,z2,z3,z4,z5,z75]),(0,[z0,z2,z3,z4,z23,z30,z6])],[(0,[z0,z2,z101,z3,z4,z46,z6]),(0,[z0,z2,z3,z4,z697,z5,z6]),(0,[z698,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z204,z3,z4,z10,z6]),(0,[z0,z2,z699,z3,z4,z5,z6])],[(0,[z0,z2,z700,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z173,z6]),(0,[z0,z2,z701,z3,z4,z5,z6]),(0,[z0,z71,z2,z4,z5,z6,z119]),(0,[z0,z2,z3,z17,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z578,z6]),(0,[z0,z60,z47,z3,z4,z5,z6]),(0,[z172,z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z702,z6]),(0,[z0,z2,z3,z4,z590,z5,z6]),(0,[z0,z2,z3,z4,z391,z10,z6]),(0,[z0,z2,z3,z4,z269,z5,z6]),(0,[z0,z2,z3,z164,z5,z95,z6]),(0,[z0,z15,z2,z3,z4,z5,z95])],[(0,[z0,z2,z3,z52,z4,z23,z6]),(0,[z0,z2,z3,z4,z212,z10,z6])],[(0,[z703,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z232,z6]),(0,[z0,z2,z704,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z127,z6,z119]),(0,[z0,z2,z3,z44,z4,z5,z119]),(0,[z705,z0,z2,z3,z4,z5,z6])],[(0,[z0,z224,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z36,z4,z5,z6]),(0,[z0,z2,z32,z3,z93,z5,z6]),(0,[z200,z0,z2,z4,z5,z6,z119]),(0,[z0,z71,z2,z3,z4,z132,z6])],[(1,[z0,z2,z3,z4,z100,z6]),(1,[z290,z2,z3,z4,z5,z196]),(0,[z0,z2,z3,z180,z5,z95,z6]),(0,[z0,z2,z3,z4,z10,z5,z6]),(0,[z0,z2,z3,z4,z5,z322,z6]),(0,[z0,z2,z706,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z97,z2,z3,z4,z396]),(0,[z0,z2,z3,z4,z707,z6]),(0,[z0,z2,z3,z4,z708,z6]),(0,[z0,z2,z3,z4,z5,z709]),(0,[z0,z462,z3,z4,z13,z6])],[(0,[z0,z2,z3,z710,z5,z6]),(0,[z21,z0,z2,z340,z4,z6]),(0,[z0,z24,z3,z4,z347,z30]),(0,[z0,z2,z3,z711,z5,z6]),(1,[z0,z154,z2,z3,z164]),(0,[z0,z154,z2,z3,z4,z5])],[(1,[z570,z106,z4,z5,z6]),(0,[z0,z2,z3,z303,z10,z6]),(0,[z0,z2,z3,z712,z5,z6]),(0,[z314,z2,z3,z4,z5,z75]),(0,[z0,z71,z2,z4,z5,z713])],[(0,[z0,z2,z3,z111,z23,z6]),(0,[z125,z2,z3,z4,z5,z75]),(0,[z0,z2,z3,z406,z5,z95]),(0,[z0,z2,z3,z116,z23,z6]),(0,[z0,z2,z638,z4,z23,z6])],[(0,[z0,z2,z3,z4,z5,z714]),(0,[z290,z2,z3,z316,z5,z6]),(0,[z0,z2,z3,z4,z715,z6]),(0,[z0,z2,z3,z174,z5,z6]),(0,[z0,z2,z3,z4,z10,z123])],[(0,[z0,z2,z3,z4,z5,z716]),(0,[z21,z2,z3,z4,z7,z378]),(0,[z0,z283,z112,z2,z3,z6]),(0,[z0,z107,z3,z18,z5,z6]),(0,[z0,z2,z3,z179,z5,z6]),(0,[z263,z0,z3,z4,z5,z717]),(0,[z0,z2,z3,z718,z23,z6]),(0,[z0,z2,z4,z308,z23,z6])],[(0,[z0,z181,z3,z4,z5,z6]),(0,[z0,z97,z2,z3,z303,z6]),(0,[z0,z2,z3,z4,z719,z6]),(0,[z339,z2,z3,z180,z5,z6])],[(0,[z0,z2,z3,z720,z5,z6]),(0,[z0,z2,z3,z4,z5,z721]),(0,[z0,z2,z3,z4,z722,z6]),(0,[z0,z2,z723,z4,z5,z6]),(0,[z0,z175,z2,z4,z5,z119])]],
   [[(0,[z0,z2,z3,z4,z724,z6]),(0,[z0,z2,z3,z130,z23,z6]),(0,[z725,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z726])],[(0,[z0,z2,z3,z727,z5,z6]),(0,[z0,z2,z3,z4,z728,z6]),(0,[z0,z2,z3,z729,z5,z6]),(0,[z0,z2,z3,z4,z730,z6]),(0,[z0,z2,z3,z4,z731,z6]),(0,[z0,z2,z3,z458,z5,z75]),(0,[z732,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z72,z6]),(0,[z0,z2,z340,z4,z6,z85])],[(0,[z0,z2,z500,z4,z23,z6]),(0,[z0,z2,z3,z4,z733,z6]),(0,[z0,z2,z3,z734,z5,z6]),(0,[z0,z24,z3,z4,z23,z30]),(0,[z0,z2,z3,z4,z109,z6]),(0,[z0,z2,z3,z116,z10,z6]),(0,[z0,z71,z2,z4,z72,z119])],[(0,[z0,z2,z551,z4,z23,z6]),(0,[z0,z2,z3,z4,z735,z6])],[(0,[z0,z2,z736,z4,z5,z6]),(0,[z0,z737,z3,z4,z5,z6]),(0,[z295,z2,z3,z87,z5,z6]),(0,[z2,z3,z4,z316,z5,z88]),(0,[z0,z2,z553,z4,z5,z127]),(0,[z0,z2,z3,z480,z5,z95]),(0,[z738,z2,z3,z4,z5,z6])],[(0,[z152,z2,z106,z4,z23,z6]),(0,[z0,z2,z3,z4,z5,z739]),(0,[z140,z2,z3,z87,z23,z6]),(0,[z0,z2,z3,z135,z5,z6]),(0,[z0,z2,z3,z4,z6,z740]),(0,[z0,z2,z3,z4,z203,z6])],[(0,[z0,z2,z3,z4,z741,z6]),(0,[z0,z2,z3,z4,z742,z6]),(0,[z0,z2,z3,z284,z36,z6]),(0,[z0,z2,z3,z303,z5,z378]),(0,[z0,z2,z743,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z717]),(0,[z744,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z308,z6]),(0,[z0,z2,z4,z10,z359,z6])],[(0,[z0,z2,z3,z4,z745,z6]),(0,[z33,z2,z3,z87,z5,z6]),(0,[z0,z2,z654,z4,z23,z6]),(0,[z314,z2,z3,z4,z38,z6]),(0,[z0,z2,z3,z4,z746,z6]),(0,[z0,z2,z3,z747,z23,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z748]),(0,[z0,z2,z749,z4,z5,z6]),(0,[z0,z750,z2,z3,z4,z5]),(0,[z125,z2,z3,z4,z38,z6]),(0,[z0,z2,z3,z130,z5,z393]),(0,[z0,z2,z3,z174,z23,z6]),(0,[z751,z2,z3,z4,z5,z6]),(0,[z0,z2,z55,z4,z752,z6]),(0,[z0,z339,z2,z3,z5,z45])],[(0,[z168,z2,z753,z4,z5,z6]),(0,[z0,z2,z4,z23,z6,z530]),(0,[z0,z2,z3,z179,z23,z6]),(0,[z0,z2,z3,z4,z5,z754]),(0,[z339,z2,z3,z93,z5,z6]),(0,[z0,z2,z3,z4,z755,z6])],[(0,[z0,z181,z3,z4,z23,z6]),(0,[z21,z2,z3,z4,z7,z417]),(0,[z0,z2,z3,z4,z109,z516]),(0,[z0,z2,z3,z164,z185,z6])],[(0,[z0,z2,z3,z4,z756,z6]),(0,[z644,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z757,z6]),(0,[z0,z2,z3,z4,z758,z6]),(0,[z0,z2,z3,z4,z759,z6]),(0,[z0,z15,z2,z340,z4,z5])],[(0,[z0,z2,z3,z4,z5,z760]),(0,[z0,z2,z3,z4,z5,z761]),(0,[z0,z2,z3,z4,z322,z6])],[(0,[z0,z2,z3,z762,z5,z6]),(0,[z0,z2,z3,z4,z98,z145])],[(0,[z0,z2,z3,z299,z5,z65]),(0,[z0,z2,z3,z763,z5,z6]),(0,[z74,z314,z9,z4,z5,z6]),(0,[z0,z2,z3,z458,z38,z6]),(0,[z0,z2,z3,z4,z764,z6]),(0,[z0,z2,z55,z4,z23,z6])],[(0,[z0,z570,z3,z4,z5,z6]),(0,[z0,z2,z3,z765,z5,z6]),(0,[z0,z181,z3,z274,z5,z6]),(0,[z0,z2,z3,z4,z766,z6]),(0,[z172,z0,z3,z52,z5,z6]),(0,[z0,z2,z4,z23,z6,z546]),(0,[z200,z0,z2,z4,z767,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z768]),(0,[z0,z2,z337,z4,z5,z65]),(0,[z0,z2,z3,z4,z769,z6]),(0,[z152,z2,z753,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z770]),(0,[z0,z2,z3,z4,z6,z771])],[(0,[z0,z2,z772,z4,z5,z6]),(0,[z0,z2,z3,z4,z773,z6]),(0,[z0,z2,z3,z135,z23,z6]),(0,[z0,z292,z3,z4,z13,z6]),(0,[z0,z2,z3,z4,z23,z739])],[(0,[z0,z2,z3,z774,z5,z6]),(0,[z0,z2,z3,z252,z578,z6]),(0,[z0,z2,z3,z4,z775,z6]),(0,[z339,z2,z3,z5,z6,z45])],[(0,[z0,z2,z3,z4,z5,z776]),(0,[z0,z2,z192,z4,z767,z6]),(0,[z0,z2,z204,z3,z189,z6]),(0,[z0,z405,z2,z4,z10,z6])],[(0,[z0,z2,z3,z4,z5,z777]),(0,[z0,z2,z3,z778,z5,z6])],[(0,[z0,z2,z381,z4,z578,z6]),(0,[z0,z2,z779,z4,z5,z6]),(0,[z0,z2,z3,z4,z780,z6]),(0,[z0,z781,z3,z4,z5,z6]),(0,[z0,z2,z568,z4,z23,z6]),(0,[z0,z31,z2,z93,z5,z123])],[(0,[z19,z86,z3,z4,z231,z6]),(0,[z19,z86,z3,z4,z5,z232]),(0,[z782,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z130,z357,z6]),(1,[z0,z3,z783,z5,z6]),(0,[z172,z0,z3,z783,z5,z6])],[(0,[z784,z86,z3,z4,z5,z6]),(0,[z0,z2,z3,z785,z5,z6]),(0,[z0,z2,z3,z4,z786,z6]),(1,[z314,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z75]),(0,[z120,z0,z3,z4,z173,z6]),(0,[z0,z24,z3,z4,z5,z717]),(0,[z0,z2,z32,z180,z10,z6]),(0,[z0,z2,z3,z787,z10,z6]),(0,[z0,z450,z2,z4,z10,z6])]],
   [[(0,[z223,z224,z3,z4,z23,z6]),(0,[z0,z2,z788,z4,z5,z6]),(0,[z0,z2,z3,z4,z789,z6]),(0,[z0,z2,z3,z4,z790,z6]),(0,[z0,z2,z3,z5,z791,z45])],[],[(0,[z0,z2,z3,z792,z5,z6]),(0,[z168,z2,z101,z4,z46,z6]),(0,[z2,z3,z4,z5,z196,z793]),(0,[z314,z2,z3,z130,z5,z6]),(0,[z0,z3,z4,z173,z746,z6])],[(0,[z0,z2,z3,z4,z5,z794]),(0,[z0,z2,z3,z4,z5,z266]),(0,[z0,z2,z3,z5,z95,z90]),(0,[z0,z795,z3,z4,z5,z6]),(0,[z156,z2,z3,z4,z10,z88]),(0,[z125,z2,z3,z130,z5,z6]),(0,[z796,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z393]),(0,[z172,z0,z3,z52,z23,z6])],[(0,[z584,z86,z3,z4,z5,z6]),(0,[z156,z2,z3,z5,z213,z88]),(0,[z797,z0,z2,z3,z4,z6]),(0,[z798,z2,z3,z4,z5,z6]),(0,[z0,z15,z2,z3,z284,z45])],[(0,[z0,z2,z3,z4,z799,z6]),(0,[z283,z339,z2,z3,z5,z6])],[(0,[z0,z2,z3,z4,z100,z6]),(0,[z0,z2,z3,z4,z800,z6]),(0,[z0,z2,z3,z4,z801,z6]),(0,[z0,z2,z3,z4,z802,z6]),(0,[z0,z24,z3,z4,z25,z30])],[(0,[z0,z2,z803,z4,z5,z6]),(0,[z280,z2,z106,z4,z5,z6]),(0,[z223,z224,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z804,z6]),(0,[z0,z2,z3,z5,z805,z6]),(0,[z503,z2,z3,z4,z5,z88]),(0,[z0,z2,z3,z4,z11,z6]),(0,[z0,z2,z3,z541,z185,z6])]],
   [[(0,[z0,z2,z3,z806,z5,z6]),(0,[z110,z2,z106,z4,z5,z6]),(0,[z0,z570,z3,z274,z5,z6]),(0,[z0,z2,z807,z3,z5,z6]),(0,[z0,z2,z3,z4,z808,z6]),(0,[z0,z15,z2,z3,z5,z278])],[(0,[z0,z2,z3,z4,z5,z20]),(0,[z0,z809,z3,z4,z5,z6]),(0,[z21,z2,z3,z4,z7,z6]),(0,[z0,z12,z3,z4,z269,z6])],[(0,[z19,z86,z3,z4,z23,z6]),(0,[z0,z2,z3,z4,z5,z810]),(0,[z253,z2,z3,z87,z5,z6]),(0,[z0,z154,z2,z3,z164,z6])],[(0,[z0,z570,z106,z4,z5,z6]),(0,[z0,z2,z3,z4,z23,z251])],[(0,[z223,z784,z3,z4,z5,z6]),(0,[z152,z2,z106,z4,z5,z293]),(0,[z0,z97,z2,z3,z4,z417]),(0,[z0,z2,z3,z5,z811,z6]),(0,[z0,z2,z3,z4,z812,z6]),(0,[z0,z2,z3,z4,z38,z6]),(0,[z0,z2,z3,z4,z813,z6]),(0,[z0,z2,z44,z4,z23,z119]),(0,[z0,z2,z3,z44,z5,z622])],[(0,[z0,z2,z814,z4,z5,z6]),(0,[z0,z2,z3,z4,z46,z6]),(0,[z0,z2,z3,z4,z815,z6])],[(0,[z0,z2,z3,z4,z816,z6]),(0,[z51,z2,z3,z4,z8,z6]),(0,[z51,z2,z3,z4,z354,z6]),(0,[z0,z2,z3,z4,z10,z378]),(0,[z0,z2,z4,z10,z23,z6])],[(0,[z0,z2,z3,z4,z23,z266]),(0,[z0,z2,z4,z767,z23,z6]),(0,[z217,z2,z3,z4,z446,z6])]],
   [[(0,[z0,z2,z3,z817,z4,z6]),(0,[z0,z2,z3,z4,z5,z818]),(0,[z0,z15,z97,z2,z3,z164])],[(0,[z0,z181,z3,z4,z5,z293]),(0,[z283,z2,z3,z87,z5,z6]),(0,[z0,z2,z3,z819,z5,z6]),(0,[z273,z2,z3,z4,z5,z196]),(0,[z0,z2,z3,z820,z5,z6]),(0,[z0,z460,z2,z4,z5,z119])],[(0,[z0,z2,z3,z4,z357,z393]),(0,[z0,z2,z4,z23,z602,z6]),(0,[z0,z2,z3,z821,z4,z6])],[(0,[z280,z0,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z822]),(0,[z0,z2,z271,z4,z10,z6]),(0,[z0,z12,z3,z4,z746,z6])],[(0,[z0,z2,z4,z5,z6,z713])],[(0,[z314,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z823])],[(0,[z0,z283,z2,z3,z23,z6]),(0,[z314,z2,z3,z4,z5,z393]),(0,[z125,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z824]),(0,[z0,z2,z3,z255,z5,z127]),(0,[z0,z15,z2,z3,z284,z4])],[(0,[z0,z2,z3,z825,z4,z5]),(0,[z0,z2,z3,z274,z100,z6]),(0,[z2,z3,z36,z826,z5,z6]),(0,[z125,z2,z3,z4,z5,z393]),(0,[z0,z2,z3,z4,z5,z827]),(0,[z0,z2,z3,z828,z5,z6]),(0,[z0,z522,z3,z4,z173,z6])]],
   [[(0,[z168,z570,z3,z4,z5,z6]),(0,[z2,z570,z106,z4,z5,z6]),(0,[z140,z339,z2,z3,z5,z6]),(0,[z0,z107,z3,z18,z520,z6]),(0,[z0,z12,z3,z4,z13,z6]),(0,[z829,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z830,z6]),(0,[z0,z2,z4,z23,z6,z616]),(0,[z0,z2,z55,z4,z23,z119]),(0,[z356,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z6,z823])],[(0,[z74,z0,z9,z4,z23,z6])],[(0,[z0,z2,z3,z4,z578,z65]),(0,[z0,z2,z3,z274,z5,z20]),(0,[z0,z2,z3,z116,z5,z6])],[(1,[z86,z381,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z417]),(0,[z2,z3,z4,z5,z793,z6]),(0,[z0,z2,z3,z4,z5,z831]),(0,[z0,z2,z3,z783,z5,z6]),(0,[z0,z2,z655,z4,z10,z6]),(0,[z0,z12,z3,z259,z13,z6]),(0,[z0,z31,z2,z93,z10,z6])],[(0,[z0,z2,z832,z4,z5,z6]),(1,[z2,z3,z826,z5,z6]),(0,[z0,z2,z3,z458,z10,z6]),(0,[z0,z2,z3,z833,z5,z6]),(0,[z0,z2,z3,z718,z5,z6]),(0,[z0,z2,z3,z4,z834,z6])],[(0,[z0,z2,z3,z4,z835,z6]),(0,[z0,z2,z3,z4,z836,z6]),(0,[z0,z181,z3,z375,z5,z6]),(0,[z0,z283,z2,z3,z10,z6]),(0,[z0,z2,z3,z458,z5,z393]),(0,[z0,z2,z4,z23,z30,z119]),(0,[z0,z2,z3,z820,z23,z6]),(0,[z0,z2,z477,z4,z23,z6])],[(1,[z784,z3,z4,z5,z6]),(0,[z0,z2,z3,z837,z5,z6]),(0,[z0,z2,z3,z838,z5,z6]),(0,[z301,z2,z3,z87,z5,z6]),(0,[z0,z2,z3,z303,z23,z6]),(0,[z156,z283,z2,z3,z5,z88]),(0,[z0,z2,z63,z4,z23,z6]),(0,[z0,z2,z3,z4,z5,z839])],[(0,[z0,z2,z381,z4,z5,z65]),(0,[z0,z2,z3,z4,z231,z232]),(0,[z0,z2,z226,z4,z23,z6]),(0,[z0,z2,z3,z130,z5,z6]),(0,[z0,z2,z3,z4,z840,z6]),(0,[z0,z2,z3,z4,z132,z6]),(0,[z339,z2,z3,z4,z10,z6])]],
   [[(0,[z0,z2,z3,z4,z841,z6]),(0,[z239,z2,z3,z552,z5,z6]),(0,[z0,z2,z3,z842,z5,z6]),(0,[z0,z2,z3,z4,z843,z6]),(0,[z0,z2,z3,z4,z844,z6]),(0,[z0,z2,z3,z4,z23,z123]),(0,[z0,z71,z2,z4,z132,z119])],[(1,[z2,z753,z4,z5,z6]),(0,[z0,z845,z2,z3,z5,z6]),(0,[z0,z846,z3,z4,z5,z6]),(0,[z2,z3,z87,z5,z88,z45]),(0,[z0,z389,z3,z18,z5,z6]),(0,[z0,z2,z3,z4,z847,z6]),(0,[z0,z24,z3,z4,z5,z30]),(0,[z0,z2,z3,z4,z10,z848])],[(0,[z0,z849,z2,z3,z4,z5]),(0,[z239,z2,z3,z36,z10,z6]),(0,[z0,z2,z850,z4,z5,z6]),(0,[z0,z2,z3,z4,z851,z6]),(0,[z0,z2,z3,z4,z347,z6]),(0,[z0,z2,z3,z4,z852,z6]),(0,[z0,z97,z2,z3,z498,z4])],[(0,[z0,z2,z3,z4,z410,z417]),(0,[z314,z60,z3,z4,z5,z6]),(0,[z0,z2,z3,z853,z5,z6]),(0,[z0,z3,z4,z746,z5,z6]),(0,[z0,z2,z3,z255,z308,z6])],[(0,[z300,z86,z3,z4,z5,z6]),(0,[z152,z2,z106,z4,z5,z6]),(0,[z140,z2,z3,z87,z5,z6]),(0,[z53,z2,z3,z4,z5,z196]),(0,[z0,z2,z477,z4,z10,z6])],[(0,[z151,z86,z3,z4,z5,z6]),(0,[z19,z86,z3,z299,z5,z6]),(0,[z0,z2,z3,z4,z5,z854]),(0,[z0,z2,z855,z4,z5,z6]),(0,[z0,z283,z2,z3,z410,z6]),(0,[z125,z2,z3,z4,z357,z6]),(0,[z0,z3,z4,z5,z6,z717])],[(0,[z0,z2,z3,z4,z856,z6]),(0,[z0,z154,z2,z3,z18,z5]),(0,[z0,z2,z3,z857,z5,z6]),(0,[z0,z2,z3,z747,z5,z6])],[(0,[z19,z86,z337,z4,z5,z6]),(0,[z0,z858,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z859,z6]),(0,[z168,z2,z101,z4,z10,z6]),(0,[z2,z3,z4,z5,z860,z6]),(0,[z0,z2,z3,z5,z6,z861]),(0,[z0,z2,z3,z4,z5,z862])]],
   [[(0,[z0,z2,z3,z4,z863,z6]),(0,[z542,z0,z2,z3,z5,z45]),(0,[z0,z2,z137,z4,z23,z6])],[(0,[z0,z864,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z860,z6]),(0,[z0,z2,z3,z316,z5,z88]),(0,[z0,z2,z3,z865,z5,z6]),(0,[z0,z2,z3,z255,z322,z6])],[(0,[z0,z2,z3,z866,z5,z6]),(0,[z0,z2,z3,z4,z867,z6]),(0,[z51,z2,z3,z4,z860,z6]),(0,[z0,z2,z4,z10,z653,z6]),(0,[z0,z2,z3,z868,z23,z6]),(0,[z0,z2,z3,z44,z23,z95]),(0,[z0,z97,z2,z3,z498,z85])],[(0,[z0,z2,z3,z4,z23,z232]),(0,[z0,z2,z3,z869,z5,z6]),(0,[z0,z505,z2,z93,z5,z6]),(0,[z0,z2,z3,z4,z870,z6]),(0,[z0,z2,z3,z458,z357,z6]),(0,[z0,z292,z3,z18,z5,z6]),(0,[z0,z2,z192,z4,z23,z6]),(0,[z0,z2,z55,z255,z23,z6])],[(0,[z0,z871,z3,z4,z5,z6]),(0,[z140,z2,z3,z87,z5,z489]),(0,[z0,z2,z3,z4,z872,z6]),(0,[z0,z2,z3,z498,z10,z6])],[(0,[z0,z873,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z874]),(0,[z0,z2,z4,z23,z6,z672])],[(0,[z0,z2,z3,z875,z5,z6]),(0,[z0,z570,z3,z375,z5,z6]),(0,[z0,z2,z3,z4,z876,z6]),(0,[z0,z229,z2,z4,z23,z6]),(0,[z200,z0,z2,z4,z10,z6]),(0,[z0,z2,z138,z4,z23,z6])],[(0,[z74,z0,z9,z4,z357,z6]),(0,[z0,z2,z3,z4,z877,z6]),(0,[z0,z2,z3,z878,z5,z6]),(0,[z0,z2,z3,z5,z6,z879]),(0,[z0,z2,z32,z180,z5,z6]),(0,[z0,z2,z3,z4,z880,z6]),(0,[z0,z2,z3,z4,z6,z881]),(0,[z0,z2,z340,z4,z10,z6])]],
   [[(0,[z0,z2,z3,z882,z5,z6]),(0,[z461,z2,z3,z4,z5,z88]),(0,[z0,z617,z3,z18,z5,z6]),(0,[z0,z2,z178,z4,z23,z6]),(0,[z0,z2,z3,z4,z883,z6]),(0,[z0,z2,z3,z4,z884,z6]),(0,[z0,z2,z3,z4,z391,z488]),(0,[z0,z885,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z100,z293]),(0,[z0,z2,z182,z4,z23,z6]),(0,[z0,z2,z3,z886,z5,z6]),(0,[z0,z2,z3,z887,z5,z6]),(0,[z0,z31,z2,z93,z455,z6]),(0,[z0,z2,z3,z44,z10,z95])],[(0,[z0,z2,z3,z4,z10,z6]),(0,[z0,z2,z3,z4,z10,z232]),(0,[z0,z2,z3,z4,z209,z6])],[(0,[z0,z2,z3,z4,z724,z489]),(0,[z0,z2,z3,z5,z213,z6]),(0,[z0,z2,z3,z4,z5,z393]),(0,[z0,z2,z3,z4,z888,z6]),(0,[z0,z71,z2,z4,z10,z119])],[(0,[z223,z2,z381,z4,z5,z6]),(0,[z0,z2,z3,z889,z5,z6]),(0,[z0,z2,z890,z4,z5,z6]),(0,[z335,z0,z9,z4,z5,z6]),(0,[z0,z2,z3,z23,z213,z6]),(0,[z0,z2,z3,z4,z5,z891]),(0,[z0,z15,z2,z3,z5,z211]),(0,[z0,z2,z340,z4,z13,z6])],[(0,[z152,z2,z106,z274,z5,z6]),(0,[z892,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z259,z10,z6]),(0,[z0,z2,z3,z893,z4,z6])],[(0,[z0,z2,z3,z4,z894,z6])],[(0,[z223,z224,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z895,z6]),(0,[z48,z0,z3,z4,z173,z6]),(0,[z0,z2,z4,z202,z23,z6]),(0,[z0,z2,z3,z4,z5,z896]),(0,[z0,z2,z3,z164,z189,z6])]],
   [[(0,[z0,z97,z2,z3,z4,z410]),(1,[z0,z2,z723,z5,z6]),(0,[z0,z2,z3,z4,z897,z6])],[(0,[z0,z2,z3,z4,z5,z898]),(0,[z0,z2,z55,z4,z10,z127])],[(0,[z0,z2,z3,z284,z87,z6]),(0,[z74,z0,z9,z458,z5,z6]),(0,[z0,z2,z3,z4,z5,z899]),(0,[z0,z2,z3,z4,z10,z516])],[(0,[z0,z2,z3,z4,z900,z6]),(0,[z0,z2,z32,z180,z23,z6]),(0,[z0,z97,z2,z340,z4,z85])],[(0,[z0,z2,z3,z252,z10,z6]),(0,[z0,z2,z3,z4,z5,z901]),(0,[z0,z2,z3,z902,z5,z6]),(0,[z0,z154,z2,z3,z4,z13]),(0,[z0,z2,z903,z4,z5,z6]),(0,[z0,z2,z3,z904,z5,z6]),(0,[z0,z2,z905,z4,z5,z6]),(0,[z0,z2,z3,z4,z145,z823])],[(0,[z0,z2,z3,z4,z5,z906]),(0,[z0,z2,z3,z375,z100,z6]),(0,[z0,z2,z3,z4,z5,z907]),(0,[z0,z908,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z455,z123]),(0,[z0,z2,z3,z164,z205,z6])],[(0,[z0,z2,z3,z4,z909,z6]),(0,[z0,z2,z3,z910,z5,z6]),(0,[z0,z2,z3,z4,z5,z378]),(0,[z0,z2,z3,z303,z5,z417]),(0,[z0,z2,z3,z4,z767,z6])],[(0,[z0,z2,z381,z4,z10,z6]),(0,[z0,z2,z3,z4,z911,z6]),(0,[z0,z2,z3,z912,z5,z6]),(0,[z156,z2,z3,z4,z23,z88]),(0,[z0,z2,z3,z10,z213,z6]),(0,[z0,z2,z3,z4,z23,z393])]],
   [[(0,[z0,z2,z3,z375,z5,z20]),(0,[z2,z3,z87,z5,z6,z489]),(0,[z2,z3,z826,z4,z5,z6]),(0,[z15,z339,z2,z3,z5,z45])],[(0,[z19,z86,z3,z4,z5,z6]),(0,[z0,z2,z3,z913,z5,z6]),(0,[z0,z2,z3,z4,z357,z6]),(0,[z0,z97,z2,z3,z4,z616])],[(0,[z0,z2,z3,z914,z5,z6]),(0,[z0,z915,z2,z3,z4,z6]),(0,[z916,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z917,z6]),(0,[z918,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z251])],[(0,[z0,z2,z3,z4,z5,z919]),(0,[z0,z2,z3,z274,z10,z6]),(0,[z0,z2,z3,z274,z209,z6]),(0,[z0,z2,z3,z4,z920,z6]),(0,[z0,z2,z3,z4,z108,z6]),(0,[z0,z2,z3,z103,z185,z6]),(0,[z0,z2,z3,z4,z5,z921]),(0,[z263,z0,z3,z4,z23,z264]),(0,[z0,z2,z3,z4,z6,z922])],[(0,[z0,z2,z3,z4,z5,z923]),(0,[z239,z283,z2,z3,z5,z6]),(0,[z339,z2,z3,z52,z5,z6]),(0,[z0,z2,z3,z4,z540,z145]),(0,[z0,z2,z340,z164,z4,z6]),(0,[z0,z2,z3,z5,z6,z84])],[(0,[z0,z2,z3,z924,z5,z6]),(0,[z0,z2,z3,z4,z925,z6]),(0,[z239,z2,z3,z5,z95,z88]),(0,[z0,z2,z3,z926,z5,z6]),(0,[z0,z2,z3,z23,z6,z84])],[(0,[z0,z2,z3,z299,z231,z6]),(0,[z0,z283,z2,z3,z5,z95]),(0,[z0,z2,z3,z4,z927,z5]),(0,[z0,z2,z3,z4,z928,z6]),(0,[z0,z2,z338,z4,z23,z6]),(0,[z0,z2,z4,z767,z5,z6]),(0,[z929,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z930,z5,z6])],[(0,[z0,z2,z3,z4,z931,z6]),(0,[z0,z784,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z25,z6]),(0,[z932,z2,z3,z4,z5,z6]),(0,[z0,z933,z2,z3,z4,z23]),(0,[z0,z2,z360,z4,z23,z6])]],
   [[(0,[z0,z2,z337,z4,z231,z6]),(0,[z0,z2,z337,z4,z5,z232]),(0,[z0,z2,z3,z934,z5,z6]),(0,[z0,z2,z340,z4,z5,z88]),(0,[z0,z2,z4,z10,z469,z6])],[(0,[z0,z2,z4,z244,z23,z6]),(0,[z0,z2,z3,z5,z6,z791])],[(0,[z0,z2,z3,z4,z935,z6]),(0,[z0,z181,z3,z4,z5,z20]),(0,[z0,z2,z3,z4,z5,z936]),(0,[z2,z3,z4,z860,z8,z6]),(0,[z0,z2,z3,z4,z23,z378]),(0,[z263,z0,z3,z4,z10,z264]),(0,[z937,z0,z2,z3,z4,z6])],[(0,[z19,z86,z3,z252,z5,z6]),(0,[z0,z2,z3,z4,z5,z417]),(0,[z0,z2,z3,z4,z5,z793]),(0,[z0,z2,z3,z938,z5,z6]),(0,[z0,z31,z2,z93,z5,z6])],[(0,[z0,z161,z3,z4,z13,z6]),(0,[z0,z154,z2,z3,z52,z5]),(0,[z2,z3,z4,z939,z23,z6]),(0,[z0,z97,z2,z3,z498,z5])],[(0,[z0,z283,z2,z3,z5,z6]),(0,[z0,z2,z3,z284,z4,z196]),(0,[z0,z2,z3,z284,z4,z6])],[(0,[z19,z86,z381,z4,z5,z6]),(0,[z156,z2,z3,z4,z410,z88]),(0,[z158,z0,z2,z3,z4,z616]),(0,[z0,z2,z3,z4,z940,z6]),(0,[z0,z2,z3,z284,z44,z4])],[(0,[z0,z2,z3,z4,z5,z941]),(0,[z0,z2,z3,z4,z942,z6]),(0,[z339,z2,z3,z4,z5,z6]),(0,[z431,z2,z3,z4,z7,z6]),(0,[z0,z2,z943,z4,z5,z6]),(0,[z0,z2,z3,z4,z944,z6]),(0,[z431,z2,z3,z4,z212,z6]),(0,[z0,z945,z2,z3,z4,z10]),(0,[z0,z2,z3,z284,z95,z6]),(1,[z0,z2,z3,z4,z823])]],
   [[(0,[z0,z946,z3,z4,z5,z6]),(0,[z74,z0,z9,z4,z5,z6]),(0,[z0,z947,z2,z3,z4,z5]),(0,[z0,z2,z3,z10,z6,z84])],[(0,[z2,z86,z381,z4,z5,z6]),(0,[z19,z784,z3,z4,z5,z6]),(0,[z0,z2,z3,z948,z5,z6]),(0,[z314,z2,z3,z4,z23,z6]),(0,[z949,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z950,z6])],[(0,[z0,z2,z3,z951,z5,z6]),(0,[z239,z2,z3,z36,z5,z6]),(0,[z125,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z952,z5,z6]),(0,[z0,z2,z408,z4,z23,z6]),(0,[z0,z953,z3,z4,z10,z6]),(0,[z0,z2,z340,z4,z391,z6])],[(0,[z86,z106,z9,z4,z5,z6]),(0,[z126,z224,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z954,z6]),(0,[z0,z2,z3,z316,z10,z6]),(0,[z0,z2,z3,z4,z61,z6]),(0,[z0,z31,z2,z93,z5,z516]),(0,[z0,z2,z3,z164,z242,z6]),(0,[z0,z2,z3,z4,z955,z6])],[(0,[z0,z2,z337,z4,z23,z6]),(0,[z2,z784,z3,z4,z5,z6]),(0,[z0,z2,z3,z956,z4,z6]),(0,[z0,z2,z3,z957,z4,z6]),(0,[z0,z2,z477,z4,z5,z6]),(0,[z356,z2,z3,z4,z23,z6]),(0,[z0,z2,z4,z23,z6,z83])],[(0,[z0,z2,z3,z4,z958,z6]),(0,[z0,z2,z3,z303,z5,z6]),(0,[z0,z2,z427,z4,z10,z6]),(0,[z0,z2,z3,z959,z5,z6]),(0,[z0,z97,z2,z3,z4,z666]),(0,[z0,z2,z32,z180,z449,z6]),(0,[z0,z15,z2,z3,z5,z473]),(0,[z0,z2,z3,z4,z960,z6]),(0,[z339,z2,z3,z44,z5,z6])],[(0,[z0,z2,z3,z4,z961,z6]),(0,[z0,z2,z3,z962,z5,z6]),(0,[z339,z2,z3,z18,z5,z6]),(0,[z0,z2,z93,z723,z5,z6]),(0,[z0,z2,z3,z963,z5,z6]),(0,[z0,z2,z3,z4,z10,z964])],[(0,[z0,z2,z3,z4,z23,z417]),(0,[z2,z3,z316,z5,z6,z88]),(0,[z0,z2,z3,z4,z5,z123]),(0,[z0,z31,z2,z93,z23,z6])]],
   [[(0,[z0,z570,z3,z4,z100,z6]),(0,[z0,z2,z3,z458,z23,z6]),(0,[z0,z2,z3,z965,z5,z6]),(0,[z0,z2,z3,z723,z5,z6])],[(0,[z0,z2,z3,z299,z10,z6]),(0,[z0,z2,z3,z4,z5,z966]),(0,[z0,z2,z3,z62,z185,z6]),(0,[z0,z2,z3,z4,z6,z491])],[(0,[z0,z2,z4,z10,z176,z6]),(0,[z0,z2,z3,z4,z967,z6]),(0,[z0,z2,z3,z968,z4,z6]),(0,[z0,z2,z3,z4,z5,z969]),(0,[z0,z2,z3,z4,z970,z6])],[(0,[z0,z2,z337,z4,z10,z6]),(0,[z0,z570,z3,z4,z5,z20]),(0,[z152,z2,z106,z375,z5,z6]),(0,[z0,z2,z3,z410,z213,z6]),(0,[z0,z2,z3,z40,z13,z6]),(0,[z339,z2,z3,z4,z23,z6]),(0,[z0,z2,z55,z4,z5,z243])],[(0,[z454,z2,z3,z4,z5,z88]),(0,[z0,z2,z3,z498,z5,z6])],[(0,[z0,z2,z3,z4,z209,z293]),(0,[z0,z2,z3,z4,z10,z293]),(0,[z0,z283,z2,z3,z98,z5]),(0,[z0,z2,z3,z971,z5,z6]),(0,[z0,z2,z210,z3,z185,z6]),(0,[z0,z2,z3,z4,z6,z972])],[(0,[z0,z2,z973,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z974]),(0,[z0,z2,z3,z4,z5,z975]),(0,[z239,z2,z3,z36,z23,z6]),(0,[z0,z2,z3,z4,z976,z6]),(0,[z0,z2,z3,z4,z977,z6])],[(0,[z0,z2,z3,z978,z5,z6]),(0,[z0,z979,z2,z3,z4,z6]),(0,[z0,z175,z2,z3,z4,z545]),(0,[z0,z2,z980,z4,z5,z6]),(0,[z339,z2,z3,z4,z98,z5])]],
   [[(0,[z0,z24,z3,z174,z5,z30]),(0,[z0,z430,z3,z4,z512,z6]),(0,[z0,z2,z312,z4,z23,z6])],[(0,[z0,z2,z3,z4,z981,z6]),(0,[z0,z2,z3,z868,z5,z6]),(0,[z0,z2,z3,z982,z5,z6]),(0,[z0,z24,z3,z179,z5,z30]),(0,[z0,z2,z3,z44,z5,z95])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z231,z6]),(0,[z0,z2,z3,z4,z5,z232]),(0,[z0,z983,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z984,z6]),(0,[z665,z0,z3,z4,z70,z6])],[(0,[z168,z2,z101,z4,z23,z6]),(0,[z599,z2,z3,z4,z5,z88]),(0,[z0,z2,z3,z4,z985,z6]),(0,[z0,z2,z4,z23,z6,z149]),(0,[z0,z2,z569,z4,z10,z6]),(0,[z0,z2,z3,z986,z5,z6]),(0,[z0,z2,z3,z116,z308,z6])],[(0,[z0,z987,z3,z4,z5,z6])],[(0,[z0,z2,z3,z988,z5,z6]),(0,[z152,z181,z106,z4,z5,z6]),(0,[z290,z2,z3,z4,z5,z310]),(0,[z295,z2,z3,z4,z5,z88]),(0,[z0,z2,z3,z989,z5,z6]),(0,[z0,z2,z3,z259,z5,z6]),(0,[z289,z0,z3,z4,z5,z264]),(0,[z0,z2,z3,z4,z990,z6])],[(0,[z635,z2,z3,z36,z5,z6]),(0,[z0,z2,z3,z4,z38,z75]),(0,[z0,z2,z3,z991,z5,z6]),(0,[z0,z154,z2,z3,z14,z5])],[(0,[z0,z2,z3,z4,z5,z992]),(0,[z0,z993,z2,z3,z4,z6]),(0,[z314,z2,z3,z4,z357,z6]),(0,[z994,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z995,z5,z6]),(0,[z0,z2,z3,z255,z10,z6])]],
   [[(0,[z0,z2,z337,z4,z996,z6]),(0,[z0,z2,z3,z4,z5,z997]),(0,[z0,z2,z3,z4,z752,z6]),(0,[z0,z2,z3,z498,z23,z6])],[(0,[z0,z2,z3,z375,z10,z6]),(0,[z0,z2,z3,z375,z209,z6]),(0,[z290,z2,z3,z4,z5,z793]),(0,[z0,z2,z3,z998,z5,z6]),(0,[z0,z2,z3,z4,z999,z6]),(0,[z0,z3,z4,z5,z30,z717]),(0,[z0,z2,z55,z4,z5,z127]),(0,[z0,z2,z3,z44,z5,z426]),(0,[z0,z2,z3,z116,z322,z6])],[(0,[z0,z2,z1000,z3,z5,z6]),(0,[z0,z2,z3,z4,z100,z20]),(0,[z0,z2,z470,z180,z5,z6])],[(0,[z0,z2,z1001,z4,z5,z6]),(0,[z19,z86,z3,z4,z5,z65]),(0,[z0,z314,z9,z4,z5,z6]),(0,[z0,z2,z340,z4,z23,z6])],[(0,[z0,z2,z3,z252,z231,z6]),(0,[z0,z2,z3,z252,z5,z232]),(0,[z1002,z0,z2,z4,z5,z6]),(0,[z570,z3,z106,z4,z5,z6]),(0,[z0,z2,z3,z4,z1003,z6]),(0,[z558,z2,z3,z36,z5,z6]),(0,[z0,z2,z3,z1004,z5,z6]),(0,[z1005,z2,z3,z4,z5,z6]),(0,[z0,z154,z2,z3,z4,z23]),(0,[z0,z2,z1006,z3,z10,z6]),(0,[z0,z2,z3,z498,z98,z5])],[(0,[z2,z3,z826,z87,z5,z6]),(0,[z51,z445,z2,z3,z4,z6]),(0,[z0,z2,z3,z1007,z5,z6]),(0,[z1008,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1009,z6])],[(0,[z0,z2,z3,z4,z23,z6]),(0,[z0,z2,z3,z1010,z5,z6]),(0,[z0,z2,z3,z4,z1011,z6]),(1,[z2,z3,z87,z5,z489]),(0,[z0,z2,z3,z4,z1012,z6]),(0,[z0,z2,z1013,z4,z5,z6])],[(0,[z0,z2,z381,z4,z231,z6]),(0,[z0,z2,z381,z4,z5,z232]),(0,[z0,z2,z3,z1014,z5,z6]),(0,[z0,z2,z3,z4,z1015,z6]),(0,[z0,z2,z3,z4,z1016,z6]),(0,[z0,z283,z2,z3,z5,z119]),(0,[z1017,z2,z3,z4,z5,z6]),(0,[z0,z71,z2,z4,z23,z119]),(0,[z0,z2,z3,z960,z185,z6]),(0,[z1018,z2,z3,z4,z5,z6]),(1,[z0,z97,z2,z3,z498])]],
   [[],[(0,[z168,z2,z79,z4,z5,z6]),(0,[z0,z2,z3,z5,z1019,z6]),(0,[z21,z2,z3,z4,z860,z6]),(0,[z21,z2,z3,z4,z590,z6]),(0,[z0,z2,z3,z259,z23,z6]),(0,[z339,z2,z3,z4,z5,z119])],[(0,[z0,z2,z3,z4,z1020,z6]),(0,[z314,z2,z3,z458,z5,z6]),(0,[z0,z107,z3,z18,z10,z6]),(0,[z0,z2,z3,z4,z540,z346]),(0,[z0,z2,z3,z787,z5,z6]),(0,[z0,z2,z3,z164,z349,z6])],[(0,[z0,z2,z3,z4,z5,z1021]),(0,[z125,z2,z3,z458,z5,z6]),(0,[z0,z2,z3,z4,z1022,z6]),(0,[z0,z394,z2,z4,z5,z119]),(0,[z0,z1023,z3,z4,z5,z6]),(0,[z0,z15,z2,z3,z10,z45]),(0,[z0,z2,z4,z132,z6,z119])],[(0,[z0,z1024,z2,z4,z5,z6]),(0,[z519,z0,z2,z4,z10,z6]),(0,[z0,z2,z3,z4,z1025,z6])],[(0,[z0,z2,z3,z4,z5,z1026]),(0,[z0,z2,z3,z4,z1027,z6]),(0,[z0,z2,z3,z1028,z5,z6]),(0,[z0,z2,z3,z4,z1029,z6]),(0,[z0,z2,z1030,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1031]),(0,[z0,z2,z55,z4,z23,z127])],[(0,[z152,z570,z106,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1032]),(0,[z156,z2,z3,z4,z5,z88]),(0,[z156,z2,z3,z4,z5,z793]),(0,[z0,z230,z3,z4,z5,z30]),(0,[z0,z2,z3,z4,z23,z516]),(0,[z0,z97,z2,z3,z78,z4])],[(0,[z0,z2,z3,z4,z1033,z6]),(0,[z0,z283,z2,z3,z5,z45]),(0,[z0,z2,z3,z4,z1034,z6]),(0,[z0,z2,z3,z4,z1035,z6])]],
   [[(0,[z0,z2,z3,z252,z23,z6]),(0,[z0,z2,z3,z4,z1036,z6])],[(0,[z0,z2,z553,z4,z23,z6]),(0,[z0,z2,z3,z130,z5,z75]),(0,[z0,z2,z3,z1037,z5,z6]),(0,[z0,z2,z3,z4,z1038,z6]),(0,[z0,z2,z302,z4,z23,z6])],[(0,[z0,z1039,z2,z3,z4,z6]),(0,[z239,z339,z2,z3,z5,z6]),(0,[z0,z2,z525,z4,z23,z6]),(0,[z0,z2,z3,z4,z1040,z6]),(0,[z0,z3,z783,z18,z5,z6]),(0,[z263,z0,z3,z4,z5,z264])],[(0,[z0,z2,z381,z4,z23,z6]),(0,[z1041,z0,z3,z4,z5,z6]),(0,[z143,z0,z3,z52,z5,z6]),(0,[z0,z2,z3,z272,z185,z6]),(0,[z744,z0,z3,z4,z10,z6])],[(0,[z0,z2,z1042,z4,z5,z6]),(0,[z0,z2,z3,z303,z145,z6]),(0,[z1043,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1044,z6]),(0,[z0,z2,z3,z1045,z5,z6]),(0,[z1046,z2,z3,z4,z5,z6]),(0,[z0,z154,z2,z3,z17,z4]),(0,[z0,z2,z3,z4,z98,z823])],[(0,[z0,z2,z3,z4,z1047,z6]),(0,[z2,z3,z753,z4,z5,z6]),(0,[z0,z2,z3,z1048,z5,z6]),(0,[z0,z2,z439,z4,z23,z6]),(0,[z0,z2,z3,z4,z10,z489]),(0,[z0,z2,z3,z4,z410,z6]),(0,[z1049,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z391,z23,z6]),(0,[z0,z154,z2,z3,z164,z185]),(0,[z0,z2,z3,z4,z98,z227])],[(0,[z0,z2,z723,z180,z5,z6]),(0,[z0,z2,z3,z1050,z5,z6])],[(0,[z0,z2,z3,z274,z23,z6]),(0,[z0,z2,z3,z4,z6,z1051]),(0,[z239,z2,z3,z826,z5,z6]),(0,[z0,z1052,z3,z4,z5,z6]),(0,[z314,z3,z9,z4,z5,z6]),(0,[z0,z12,z3,z40,z13,z6]),(0,[z0,z2,z1053,z4,z5,z6]),(1,[z0,z2,z3,z5,z791])]],
   [[(0,[z0,z2,z4,z752,z23,z6])],[(0,[z0,z2,z3,z4,z1054,z6]),(0,[z0,z2,z1055,z4,z5,z6]),(0,[z0,z2,z3,z4,z1056,z6])],[(0,[z0,z2,z3,z4,z996,z6]),(0,[z0,z2,z3,z1057,z4,z6]),(0,[z140,z2,z3,z87,z5,z266]),(0,[z0,z953,z3,z4,z5,z6])],[(0,[z1058,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z939,z5,z6]),(0,[z0,z107,z3,z18,z108,z6]),(0,[z0,z15,z2,z3,z284,z5])],[(0,[z0,z2,z381,z4,z1033,z6]),(0,[z0,z570,z3,z4,z10,z6]),(0,[z0,z570,z3,z4,z209,z6]),(0,[z0,z2,z3,z4,z1059,z6]),(1,[z339,z2,z3,z5,z45])],[(0,[z152,z2,z106,z4,z100,z6]),(0,[z0,z1060,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1061]),(0,[z74,z0,z743,z4,z5,z6]),(0,[z0,z2,z415,z4,z23,z6]),(0,[z0,z97,z2,z3,z4,z620])],[(0,[z584,z2,z106,z4,z5,z6]),(0,[z0,z2,z3,z4,z1062,z6]),(0,[z0,z2,z3,z1063,z5,z6]),(0,[z0,z97,z2,z3,z4,z625]),(0,[z0,z2,z3,z130,z38,z6]),(0,[z0,z154,z2,z3,z4,z173]),(0,[z0,z2,z3,z4,z1064,z6]),(0,[z0,z2,z3,z4,z5,z964]),(0,[z0,z2,z3,z1065,z5,z6])],[(0,[z0,z86,z381,z4,z5,z6]),(0,[z0,z2,z3,z1066,z5,z6]),(0,[z0,z2,z3,z4,z6,z1067])]],
   [[(0,[z314,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z1068,z5,z6]),(0,[z152,z2,z106,z4,z5,z20]),(0,[z0,z2,z3,z826,z5,z6]),(0,[z0,z2,z3,z4,z5,z1069]),(0,[z0,z2,z3,z4,z449,z6]),(0,[z0,z2,z3,z5,z6,z1070])],[(0,[z0,z2,z3,z299,z5,z6]),(0,[z125,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z299,z5,z232]),(0,[z239,z2,z3,z5,z166,z6]),(0,[z0,z283,z2,z3,z5,z127]),(0,[z0,z154,z2,z3,z164,z4]),(0,[z356,z15,z2,z3,z5,z45])],[(0,[z0,z2,z3,z4,z1071,z6]),(0,[z0,z181,z3,z4,z100,z6]),(0,[z0,z2,z3,z4,z1072,z6]),(0,[z0,z2,z3,z52,z520,z6]),(0,[z0,z277,z3,z4,z269,z6])],[(0,[z0,z2,z337,z4,z5,z6]),(0,[z0,z2,z3,z1073,z5,z6]),(0,[z356,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1074,z6]),(0,[z0,z743,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z455,z6]),(0,[z0,z2,z4,z23,z6,z281]),(0,[z0,z2,z55,z4,z5,z713]),(0,[z339,z2,z3,z4,z5,z127]),(0,[z339,z2,z3,z4,z5,z95]),(0,[z0,z97,z2,z3,z4,z349]),(0,[z0,z2,z3,z44,z5,z791])],[(0,[z19,z86,z3,z4,z578,z6]),(0,[z0,z2,z3,z4,z231,z65]),(0,[z0,z2,z3,z4,z10,z75]),(0,[z0,z2,z3,z4,z1075,z6]),(0,[z0,z2,z3,z1076,z5,z6])],[(0,[z0,z2,z3,z4,z1077,z6]),(0,[z0,z2,z3,z4,z5,z1078]),(0,[z0,z2,z3,z4,z5,z293]),(0,[z0,z2,z753,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1079]),(0,[z0,z15,z2,z4,z23,z119]),(0,[z0,z15,z2,z3,z491,z45])],[(0,[z0,z1080,z3,z4,z5,z6]),(0,[z0,z94,z3,z18,z5,z6]),(0,[z0,z2,z3,z4,z5,z1081]),(0,[z0,z2,z3,z4,z5,z1082]),(0,[z1083,z2,z3,z4,z23,z6]),(0,[z0,z97,z2,z3,z84,z85])],[(0,[z2,z753,z106,z4,z5,z6]),(0,[z0,z2,z3,z316,z23,z6]),(0,[z0,z2,z4,z23,z196,z119]),(0,[z0,z2,z3,z458,z5,z6]),(0,[z0,z2,z3,z1084,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z1085]),(0,[z0,z31,z2,z93,z109,z6]),(0,[z0,z2,z3,z5,z6,z1086]),(0,[z0,z2,z3,z4,z5,z1087]),(0,[z339,z2,z3,z14,z5,z6]),(0,[z0,z97,z2,z477,z4,z85])],[(0,[z0,z2,z3,z4,z1088,z6]),(0,[z0,z2,z3,z4,z1089,z6]),(0,[z74,z125,z9,z4,z5,z6]),(0,[z0,z2,z3,z23,z6,z1086]),(0,[z0,z1090,z3,z4,z5,z6]),(0,[z0,z2,z340,z44,z4,z5])],[(0,[z0,z2,z3,z4,z1091,z6]),(0,[z0,z2,z3,z1092,z4,z6])],[(0,[z0,z2,z3,z1093,z5,z6]),(0,[z651,z2,z3,z4,z5,z88]),(0,[z290,z2,z3,z4,z10,z196]),(0,[z0,z2,z287,z180,z5,z6]),(0,[z0,z2,z3,z4,z455,z516]),(0,[z0,z97,z2,z3,z4,z823])],[(0,[z21,z2,z3,z135,z7,z6]),(0,[z0,z2,z3,z4,z1094,z6]),(0,[z0,z2,z3,z10,z6,z1070]),(0,[z0,z2,z3,z4,z5,z848])],[(0,[z0,z2,z337,z252,z5,z6]),(0,[z0,z2,z3,z299,z23,z6]),(0,[z0,z2,z3,z1095,z23,z6])],[(0,[z0,z2,z381,z299,z5,z6]),(0,[z0,z2,z1096,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z1097]),(0,[z0,z2,z3,z4,z209,z20]),(0,[z0,z2,z3,z4,z10,z20]),(0,[z0,z599,z2,z3,z5,z45]),(0,[z0,z2,z3,z1098,z4,z6])],[(0,[z0,z1099,z2,z3,z5,z6]),(0,[z156,z2,z3,z316,z5,z88]),(0,[z162,z0,z3,z4,z5,z264]),(0,[z0,z107,z3,z783,z5,z6]),(0,[z0,z2,z3,z255,z5,z6])]],
   [[(0,[z86,z3,z381,z4,z5,z6]),(0,[z0,z283,z2,z3,z5,z489]),(0,[z0,z15,z2,z3,z5,z620]),(0,[z0,z15,z2,z3,z388,z5])],[(0,[z0,z2,z3,z4,z23,z293]),(0,[z0,z2,z3,z4,z1100,z6]),(0,[z0,z2,z3,z40,z10,z6])],[(0,[z168,z2,z101,z4,z5,z6]),(0,[z0,z2,z3,z4,z1101,z6]),(0,[z168,z2,z101,z4,z478,z6]),(0,[z51,z0,z2,z340,z4,z6]),(0,[z1102,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z38,z393]),(0,[z0,z2,z3,z4,z1103,z6]),(0,[z0,z2,z3,z4,z23,z1082])],[(0,[z0,z2,z3,z5,z6,z1104]),(0,[z0,z2,z3,z4,z357,z75]),(0,[z0,z2,z4,z10,z767,z6])],[(0,[z0,z2,z3,z4,z1105,z6]),(0,[z0,z2,z3,z1106,z5,z6]),(0,[z0,z2,z3,z4,z1107,z6]),(0,[z314,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z18,z520,z6]),(0,[z0,z2,z148,z4,z23,z6]),(0,[z0,z2,z3,z4,z109,z123]),(0,[z0,z2,z1006,z3,z5,z6]),(0,[z0,z15,z2,z3,z5,z791]),(0,[z0,z2,z3,z4,z1108,z6]),(0,[z0,z2,z3,z4,z1109,z6])],[(0,[z0,z2,z3,z4,z5,z1110]),(0,[z2,z3,z4,z87,z5,z489]),(0,[z0,z2,z340,z4,z173,z6]),(0,[z0,z2,z477,z4,z308,z6])],[(0,[z0,z2,z3,z274,z5,z293]),(0,[z0,z2,z3,z5,z1111,z6]),(0,[z539,z0,z3,z52,z5,z6]),(0,[z0,z2,z55,z255,z5,z127])],[(0,[z0,z2,z3,z4,z10,z65]),(0,[z0,z31,z2,z723,z5,z6])]],
   [[(0,[z0,z2,z337,z4,z1112,z6]),(0,[z0,z2,z3,z4,z5,z1113]),(0,[z0,z2,z3,z1114,z5,z6]),(0,[z0,z2,z3,z4,z10,z1115]),(1,[z0,z2,z4,z5,z713]),(0,[z0,z2,z3,z4,z823,z85])],[(0,[z0,z2,z3,z4,z1116,z6]),(0,[z0,z595,z3,z52,z5,z6]),(0,[z0,z2,z483,z4,z23,z6]),(0,[z0,z2,z138,z4,z5,z127])],[(0,[z59,z2,z3,z4,z7,z6]),(0,[z0,z2,z340,z4,z5,z196]),(0,[z0,z2,z340,z4,z5,z6])],[(0,[z0,z2,z3,z255,z23,z6]),(0,[z0,z2,z3,z1117,z10,z6]),(0,[z0,z15,z2,z3,z5,z45]),(0,[z0,z97,z2,z3,z498,z6]),(0,[z0,z2,z3,z1118,z5,z6])],[(0,[z239,z2,z3,z4,z5,z489]),(0,[z0,z2,z3,z174,z347,z6]),(0,[z0,z2,z3,z272,z54,z6]),(0,[z0,z2,z3,z4,z98,z488])],[(0,[z0,z2,z3,z4,z478,z6]),(0,[z0,z2,z3,z4,z1119,z6]),(0,[z0,z2,z3,z375,z23,z6]),(0,[z0,z2,z3,z4,z5,z1120]),(0,[z0,z2,z3,z179,z347,z6]),(0,[z0,z2,z1121,z4,z5,z6]),(0,[z0,z2,z340,z17,z4,z6])],[(0,[z0,z2,z3,z1122,z5,z6]),(0,[z0,z2,z3,z36,z5,z489]),(0,[z0,z2,z3,z1123,z5,z6]),(0,[z0,z2,z3,z1124,z5,z6]),(0,[z0,z175,z2,z3,z4,z85]),(0,[z0,z71,z2,z4,z5,z119])],[(0,[z0,z2,z3,z4,z1125,z6]),(0,[z0,z2,z3,z4,z5,z1126]),(0,[z466,z2,z3,z36,z5,z6]),(0,[z217,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z111,z10,z6]),(0,[z0,z112,z2,z3,z213,z6]),(0,[z0,z2,z3,z4,z1127,z6]),(0,[z200,z0,z2,z4,z308,z6]),(0,[z0,z2,z55,z4,z132,z6]),(0,[z1128,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1129,z6])]],
   [[(0,[z156,z2,z3,z111,z5,z88]),(0,[z156,z112,z2,z3,z4,z88]),(0,[z0,z2,z3,z1106,z23,z6]),(0,[z0,z2,z4,z5,z713,z119])],[(0,[z0,z2,z3,z4,z1130,z6]),(0,[z21,z2,z3,z4,z383,z6]),(0,[z0,z2,z3,z4,z1131,z6])],[(0,[z0,z2,z1132,z4,z5,z6]),(0,[z74,z0,z9,z4,z5,z75]),(0,[z0,z945,z2,z3,z4,z5]),(0,[z0,z97,z2,z3,z4,z85])],[(0,[z0,z2,z3,z4,z5,z1133]),(0,[z0,z2,z3,z4,z1134,z6]),(0,[z0,z2,z3,z180,z5,z123]),(0,[z0,z15,z2,z3,z5,z667]),(0,[z0,z2,z3,z1135,z5,z6])],[(0,[z0,z2,z3,z130,z10,z6]),(0,[z0,z2,z3,z4,z1136,z6])],[(0,[z0,z2,z3,z4,z578,z6]),(0,[z0,z2,z3,z4,z578,z232]),(0,[z0,z2,z4,z5,z6,z1137]),(0,[z0,z2,z3,z4,z5,z489]),(0,[z0,z2,z3,z1138,z5,z6]),(0,[z0,z2,z3,z4,z5,z516]),(0,[z0,z2,z3,z1139,z5,z6]),(0,[z120,z0,z3,z4,z413,z6])],[(0,[z0,z2,z1140,z4,z5,z6]),(0,[z0,z107,z3,z18,z23,z6]),(0,[z0,z24,z3,z4,z10,z30]),(0,[z0,z2,z55,z116,z23,z6])],[(0,[z0,z2,z3,z252,z5,z6]),(0,[z2,z101,z753,z4,z5,z6]),(0,[z0,z1141,z2,z3,z5,z6]),(0,[z0,z15,z2,z3,z23,z45])]],
   [[(0,[z0,z2,z3,z5,z95,z489]),(0,[z0,z2,z3,z284,z4,z88]),(0,[z0,z175,z2,z4,z23,z119])],[(0,[z0,z2,z1142,z4,z5,z6]),(0,[z0,z1143,z2,z3,z4,z5]),(0,[z152,z2,z106,z4,z209,z6]),(0,[z152,z2,z106,z4,z10,z6]),(0,[z0,z2,z509,z4,z23,z6]),(0,[z140,z2,z3,z87,z10,z6]),(0,[z0,z2,z3,z4,z23,z1120]),(0,[z339,z2,z3,z164,z5,z6]),(0,[z0,z15,z2,z3,z242,z5])],[(0,[z0,z2,z381,z4,z5,z6]),(0,[z0,z2,z337,z299,z5,z6]),(0,[z0,z2,z3,z1144,z5,z6]),(0,[z300,z0,z9,z4,z5,z6]),(0,[z0,z993,z2,z3,z4,z489]),(0,[z0,z2,z55,z4,z308,z127])],[(0,[z0,z2,z3,z4,z1145,z6]),(0,[z0,z2,z3,z4,z5,z1146]),(0,[z223,z139,z3,z4,z5,z6]),(0,[z566,z0,z2,z4,z10,z6]),(0,[z0,z154,z2,z3,z164,z5])],[(0,[z0,z2,z1147,z4,z5,z6]),(0,[z0,z2,z3,z4,z1148,z6]),(0,[z0,z2,z3,z1149,z5,z6]),(0,[z0,z1150,z2,z3,z4,z5]),(0,[z0,z2,z4,z23,z264,z119]),(0,[z0,z2,z3,z174,z10,z6]),(0,[z0,z2,z3,z1151,z5,z6])],[(0,[z0,z2,z3,z164,z508,z6]),(0,[z0,z2,z3,z4,z145,z417]),(0,[z0,z2,z3,z4,z1152,z6]),(0,[z0,z3,z4,z746,z13,z6]),(0,[z0,z2,z3,z4,z577,z145]),(0,[z0,z2,z3,z179,z10,z6])],[(0,[z0,z2,z3,z274,z5,z6]),(0,[z0,z181,z3,z4,z10,z6]),(0,[z0,z181,z3,z4,z209,z6]),(0,[z177,z2,z101,z4,z5,z6]),(0,[z0,z3,z783,z4,z5,z6]),(0,[z0,z2,z3,z93,z5,z123]),(0,[z0,z2,z706,z4,z23,z6])],[(0,[z74,z0,z9,z4,z38,z6]),(0,[z0,z2,z3,z4,z1153,z6]),(0,[z0,z2,z3,z164,z960,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z1154]),(0,[z0,z2,z3,z4,z5,z1155]),(0,[z0,z2,z3,z5,z1156,z6]),(0,[z0,z2,z3,z1157,z5,z6]),(0,[z0,z2,z55,z4,z322,z127])],[(0,[z0,z2,z3,z4,z23,z489]),(0,[z21,z2,z3,z303,z7,z6]),(0,[z0,z436,z3,z4,z5,z30]),(0,[z0,z2,z3,z4,z1158,z6]),(0,[z0,z387,z3,z52,z5,z6]),(0,[z0,z2,z338,z4,z5,z127]),(0,[z0,z1159,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1160,z6]),(0,[z0,z2,z3,z255,z5,z119]),(0,[z339,z97,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z1112,z6]),(0,[z0,z2,z3,z4,z1161,z6]),(0,[z0,z2,z3,z4,z1162,z6]),(0,[z0,z2,z3,z4,z1163,z6]),(0,[z0,z2,z3,z1164,z5,z6]),(0,[z0,z2,z32,z180,z203,z6])],[(0,[z0,z2,z3,z1165,z5,z6]),(0,[z0,z2,z3,z4,z1166,z6]),(0,[z0,z2,z3,z4,z6,z1167]),(0,[z0,z430,z3,z4,z13,z6]),(0,[z0,z2,z3,z1168,z5,z6])],[(0,[z0,z2,z381,z252,z5,z6]),(0,[z0,z2,z3,z4,z5,z1169]),(0,[z0,z2,z3,z1170,z5,z6]),(0,[z0,z2,z3,z1171,z5,z6]),(0,[z0,z933,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z6,z1172]),(0,[z339,z2,z3,z4,z5,z45])],[(0,[z0,z1173,z2,z3,z5,z6]),(1,[z2,z3,z4,z860,z6]),(0,[z0,z2,z3,z135,z10,z6]),(1,[z2,z3,z316,z5,z88]),(0,[z314,z2,z47,z4,z5,z6]),(0,[z0,z2,z1174,z4,z5,z6]),(0,[z0,z2,z1175,z4,z5,z6])],[],[(0,[z0,z2,z3,z4,z1176,z6])]],
   [[(0,[z0,z570,z3,z4,z23,z6]),(0,[z0,z3,z4,z5,z6,z1177]),(0,[z0,z2,z3,z4,z1178,z6]),(0,[z0,z2,z3,z44,z5,z352]),(0,[z0,z2,z3,z1179,z5,z6]),(0,[z0,z2,z3,z4,z5,z1180]),(0,[z0,z2,z3,z5,z6,z1181]),(0,[z0,z2,z3,z4,z5,z713])],[(0,[z0,z2,z3,z4,z1182,z6]),(0,[z0,z2,z3,z4,z5,z1183]),(0,[z2,z3,z4,z5,z793,z88]),(0,[z0,z2,z3,z4,z5,z1184]),(0,[z0,z2,z302,z180,z5,z6])],[(0,[z0,z224,z381,z4,z5,z6]),(0,[z0,z2,z3,z1185,z5,z6])],[(0,[z290,z2,z3,z4,z5,z196])],[(0,[z0,z2,z3,z375,z5,z293]),(0,[z0,z15,z2,z3,z5,z489]),(0,[z1186,z2,z3,z4,z5,z6]),(0,[z0,z229,z2,z93,z5,z6]),(0,[z0,z2,z3,z40,z173,z6]),(0,[z0,z2,z138,z93,z5,z6]),(0,[z0,z2,z3,z1157,z23,z6])],[(0,[z0,z2,z3,z4,z1187,z6]),(0,[z280,z0,z2,z4,z23,z6]),(0,[z0,z2,z3,z5,z1188,z6]),(0,[z560,z2,z3,z4,z5,z196]),(0,[z0,z2,z3,z4,z5,z1189]),(0,[z1083,z2,z3,z4,z5,z6]),(0,[z0,z96,z3,z4,z173,z6]),(0,[z0,z2,z3,z4,z5,z1190]),(0,[z0,z2,z1191,z3,z4,z6])],[(0,[z0,z2,z3,z316,z5,z6]),(0,[z0,z2,z3,z4,z1192,z6]),(0,[z0,z2,z687,z4,z10,z6]),(0,[z0,z2,z3,z316,z5,z196]),(0,[z0,z2,z340,z4,z98,z6]),(0,[z0,z2,z3,z498,z145,z6])],[(0,[z0,z2,z3,z1193,z5,z6]),(0,[z0,z118,z2,z4,z5,z119]),(0,[z172,z0,z3,z52,z10,z6])]],
   [[(0,[z0,z2,z3,z4,z23,z75]),(0,[z0,z2,z1194,z4,z5,z6]),(0,[z0,z2,z3,z4,z1195,z6]),(0,[z117,z2,z3,z4,z354,z6]),(0,[z0,z2,z3,z4,z5,z791])],[(0,[z0,z2,z3,z4,z1196,z6]),(0,[z0,z2,z3,z135,z5,z378]),(0,[z0,z2,z3,z40,z5,z6]),(0,[z0,z2,z3,z4,z5,z1197]),(0,[z48,z0,z3,z4,z746,z6]),(0,[z0,z2,z3,z174,z25,z6]),(0,[z0,z2,z3,z4,z1198,z6]),(0,[z0,z2,z3,z902,z10,z6]),(0,[z0,z154,z2,z3,z4,z10])],[(0,[z74,z0,z9,z130,z5,z6]),(0,[z0,z2,z3,z4,z1199,z6]),(0,[z0,z2,z3,z179,z25,z6])],[(0,[z0,z570,z101,z4,z5,z6]),(1,[z0,z15,z2,z3,z284]),(0,[z0,z2,z3,z5,z95,z791])],[(0,[z0,z2,z3,z4,z1200,z6]),(0,[z0,z15,z2,z3,z5,z586]),(0,[z0,z2,z3,z1095,z5,z6])],[(0,[z0,z2,z3,z4,z1201,z6]),(0,[z0,z2,z3,z4,z1202,z6]),(0,[z0,z2,z3,z4,z1203,z6]),(0,[z0,z2,z3,z5,z95,z636])],[(0,[z19,z86,z3,z4,z10,z6]),(0,[z0,z2,z3,z5,z1204,z6]),(0,[z557,z2,z3,z87,z5,z6]),(0,[z2,z3,z4,z7,z860,z6]),(0,[z0,z2,z3,z1205,z5,z6]),(0,[z0,z2,z3,z1206,z4,z6])],[(0,[z0,z2,z3,z4,z5,z65]),(0,[z0,z2,z3,z1207,z5,z6]),(0,[z290,z2,z3,z4,z23,z196]),(0,[z0,z2,z3,z4,z5,z1208]),(0,[z0,z2,z3,z4,z10,z251])]],
   [[(0,[z0,z2,z3,z4,z1209,z6]),(0,[z0,z2,z3,z4,z1210,z6]),(0,[z344,z0,z3,z4,z173,z6]),(0,[z0,z2,z3,z4,z1211,z6]),(0,[z0,z2,z3,z4,z5,z1115])],[(0,[z0,z2,z1212,z4,z5,z6]),(0,[z0,z2,z3,z4,z1213,z6]),(0,[z0,z3,z743,z4,z5,z6]),(1,[z0,z3,z4,z5,z717]),(0,[z0,z2,z32,z723,z5,z6]),(0,[z0,z2,z3,z4,z927,z23])],[(0,[z0,z2,z3,z4,z5,z1214]),(0,[z0,z2,z3,z4,z23,z20]),(0,[z0,z3,z52,z783,z5,z6]),(1,[z0,z3,z4,z746,z6])],[(0,[z0,z2,z3,z4,z10,z266]),(0,[z0,z2,z3,z4,z1215,z6]),(0,[z0,z2,z1216,z3,z4,z6]),(0,[z0,z2,z3,z1117,z5,z6]),(0,[z0,z2,z3,z5,z960,z6])],[(0,[z0,z2,z3,z4,z5,z1217]),(0,[z0,z2,z3,z299,z578,z6]),(0,[z0,z2,z3,z4,z5,z1218]),(0,[z0,z1219,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1220,z6]),(0,[z0,z2,z3,z40,z23,z6])],[(0,[z0,z2,z337,z4,z578,z6]),(0,[z224,z784,z3,z4,z5,z6]),(0,[z494,z2,z3,z36,z5,z6]),(0,[z0,z2,z3,z1221,z5,z6]),(0,[z0,z2,z3,z135,z5,z417]),(0,[z0,z2,z3,z386,z5,z95])],[(0,[z0,z2,z3,z4,z1222,z6]),(0,[z0,z2,z3,z111,z5,z6]),(0,[z0,z112,z2,z3,z4,z6]),(0,[z0,z2,z3,z1223,z4,z6]),(0,[z0,z2,z3,z4,z145,z574])]],
   [[(0,[z0,z2,z1224,z3,z5,z6]),(0,[z0,z2,z3,z4,z1225,z6]),(0,[z0,z283,z97,z2,z3,z5]),(0,[z0,z2,z3,z4,z520,z6]),(0,[z50,z2,z3,z4,z590,z6])],[(0,[z0,z2,z3,z252,z5,z65]),(0,[z0,z2,z3,z4,z1226,z6]),(0,[z0,z2,z600,z4,z23,z6]),(0,[z0,z3,z4,z5,z717,z264]),(0,[z0,z2,z4,z23,z6,z119])],[(0,[z0,z2,z381,z4,z1201,z6]),(0,[z0,z2,z3,z87,z5,z489]),(0,[z140,z2,z3,z826,z5,z6]),(0,[z0,z2,z3,z4,z5,z1227]),(0,[z0,z2,z153,z4,z23,z6]),(0,[z0,z15,z2,z3,z284,z6])],[(0,[z0,z2,z3,z4,z23,z65]),(0,[z0,z2,z4,z23,z88,z119]),(1,[z0,z2,z4,z767,z6]),(0,[z0,z947,z2,z3,z4,z23]),(0,[z0,z2,z3,z164,z251,z185])],[(0,[z0,z2,z3,z1228,z5,z6]),(0,[z0,z2,z3,z375,z5,z6]),(0,[z0,z2,z3,z4,z5,z1229]),(0,[z0,z2,z3,z4,z5,z1230]),(0,[z48,z0,z3,z4,z70,z6])],[(0,[z0,z2,z3,z4,z1231,z6]),(0,[z548,z2,z3,z4,z5,z196]),(0,[z74,z0,z9,z4,z10,z6]),(0,[z0,z2,z3,z4,z5,z1232]),(0,[z0,z2,z64,z4,z10,z6])],[(0,[z0,z2,z3,z4,z98,z410]),(0,[z74,z0,z9,z4,z5,z393]),(0,[z0,z2,z55,z116,z5,z127]),(0,[z0,z2,z4,z5,z127,z713])],[(0,[z0,z570,z3,z4,z5,z293]),(1,[z2,z3,z4,z5,z793]),(0,[z0,z2,z4,z540,z23,z119]),(0,[z0,z2,z3,z952,z10,z6]),(0,[z0,z2,z3,z4,z1233,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 522) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 522).take 520) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1042).take 218) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1260)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [522, 520, 218] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 83).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 83).take 80).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 163).take 75).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 238).take 18).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [83, 80, 75, 18] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_37869

theorem PEqualNP.Outside.L_meta_37869 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4276157088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4276157088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37869.solve