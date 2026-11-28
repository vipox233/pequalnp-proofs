import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39143

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
  Nat.testBit (4277071594 * 2 ^ 32 + 4205494400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00000c215214ae1a#64 ++ 0x200001842a4295c3#64 ++ 0xf0245c63f23ffe3f#64 ++ 0xde048b8c7e47ffc7#64 : BitVec 256),
   (0x0849858ccc3262ed#64 ++ 0x410930b199864c5d#64 ++ 0xf8dba79ccc3267ff#64 ++ 0xbf1b74f399864cff#64 : BitVec 256),
   (0x131c381706c38571#64 ++ 0x82638702e0d870ae#64 ++ 0x9f1c381f0fc387ff#64 ++ 0x73e38703e1f870ff#64 : BitVec 256),
   (0x25e03ee00b7c0786#64 ++ 0x04bc07dc016f80f0#64 ++ 0xafe03fe00ffc07c6#64 ++ 0xf5fc07fc01ff80f8#64 : BitVec 256),
   (0x06fec0000dab5000#64 ++ 0x00dfd80001b56a00#64 ++ 0xcfffc0000ffff805#64 ++ 0xf9fff80001ffff00#64 : BitVec 256),
   (0x07b7735aa0000000#64 ++ 0x00f6ee6b54000000#64 ++ 0xf7fffffff0000003#64 ++ 0xfefffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [9, 7]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [13, 5]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0xf0245c63f23ffe3f 0xde048b8c7e47ffc7

def z1 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0xcfffc0000ffff805 0xf9fff80001ffff00

def z2 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0xf7fffffff0000003 0xfefffffffe000000

def z3 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xf8dba79ccc3267ff 0xbf1b74f399864cff

def z4 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x9f1c381f0fc387ff 0x73e38703e1f870ff

def z5 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xefe47fe00fffffc7 0xfdfc8ffc01fffff8

def z6 : W := mkw 0x0101335aa0000000 0x0020266b54000000 0x0000239c00000000 0x0000047380000000

def z7 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xafe03fe00ffc07c6 0xf5fc07fc01ff80f8

def z8 : W := mkw 0x08488ca55e36eeff 0x61091194abc6dddf 0x080000000e3ffffc 0x0100000001c7ffff

def z9 : W := mkw 0x08498dadde36eeff 0x610931b5bbc6dddf 0xf8fffffffe3fffff 0xff1fffffffc7ffff

def z10 : W := mkw 0x0040048008300284 0x0008009001060050 0xa8c027800c3007c6 0xb51804f0018600f8

def z11 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0x0fc023800dc001c0 0x21f8047001b80038

def z12 : W := mkw 0x04a0000001080000 0x0094000000210000 0x0720000003cc0000 0x40e4000000798000

def z13 : W := mkw 0x0009010c84020061 0x000120219080400c 0xf8dba79ccc0207ff 0xbf1b74f3998040ff

def z14 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0x07dba39c00000000 0x20fb747380000000

def z15 : W := mkw 0x0008000404020061 0x000100008080400c 0x9818201c0c0207ff 0x33030403818040ff

def z16 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0x00245863323ffe3c 0x40048b0c6647ffc7

def z17 : W := mkw 0x0314301200000000 0x0062860240000000 0x971c381f00000003 0x72e38703e0000000

def z18 : W := mkw 0x04a34348a0000000 0x0094686914000000 0x60e3c7e0f0000000 0x8c1c78fc1e000000

def z19 : W := mkw 0x06bec00004835000 0x00d7d80000906a00 0xc7ffc0000003f801 0xf8fff80000007f00

def z20 : W := mkw 0x131c301604c30161 0x82638602c098602c 0x8f1c201c0fc381c5 0x71e3840381f87038

def z21 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x0f18201c0fc387fc 0x21e3040381f870ff

def z22 : W := mkw 0x25e03ee11b7c8f96 0x24bc07dc236f91f2 0xafe47fe33ffd9fc6 0xf5fc8ffc67ffb3f8

def z23 : W := mkw 0x0849818c8c2240e5 0x410930319184481c 0x08dba39c0c0001c0 0x211b747381800038

def z24 : W := mkw 0x0801058cc01022ed 0x410020b19802045d 0x3000279cc00007fa 0x060004f3980000ff

def z25 : W := mkw 0x07b7735aa1891000 0x00f6ee6b54312200 0xf7fffffff3cd9803 0xfefffffffe79b300

def z26 : W := mkw 0x05a0324000000000 0x00b4064800000000 0xa7e03fe000000002 0xf4fc07fc00000000

def z27 : W := mkw 0x121c001704838071 0x82438002e090700e 0x101c001f00038039 0x02038003e0007007

def z28 : W := mkw 0x18488c854ef3e7fd 0xc3091190a9de7cff 0x080000000ff3e7fc 0x0100000001fe7cff

def z29 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0x90041803023ffe3f 0x520083006047ffc7

def z30 : W := mkw 0x0000042050142a0a 0x200000840a028541 0x60204460f03c7800 0x8c04088c1e078f00

def z31 : W := mkw 0x0849818c8c2240e5 0x410930319184481c 0x98dba39c0c0207ff 0x331b7473818040ff

def z32 : W := mkw 0x0000000000000000 0x0000000000000000 0xf0245c63f23ff807 0xde048b8c7e47ff00

def z33 : W := mkw 0x0100380002400500 0x00200700004800a0 0x8f0038000fc007c6 0x71e0070001f800f8

def z34 : W := mkw 0x37fc3ef70fff87f7 0x86ff87dee1fff0fe 0xbffc3fff0fff87ff 0xf7ff87ffe1fff0ff

def z35 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0x3800279ccc3267fe 0x070004f399864cff

def z36 : W := mkw 0x07b6725220000000 0x00f6ce4a44000000 0x0724586330000000 0x40e48b0c66000000

def z37 : W := mkw 0x1314381302c18510 0x82628702605830a2 0x0704180303c18000 0x40e0830060783000

def z38 : W := mkw 0x1314381302c18510 0x82628702605830a2 0x9704180303c3863f 0x52e08300607870c7

def z39 : W := mkw 0x131c301604c30161 0x82638602c098602c 0x0f18201c0dc001c0 0x21e3040381b80038

def z40 : W := mkw 0x131c3c3756d7af7b 0xa2638786eadaf5ef 0xff3c7c7fffffffff 0xffe78f8fffffffff

def z41 : W := mkw 0x04e2c00009285000 0x009c580001250a00 0x40e3c000003c7800 0x881c780000078f00

def z42 : W := mkw 0x0809850cc4126269 0x410130a198824c4d 0xf01b841cc032663f 0x9e03708398064cc7

def z43 : W := mkw 0x004880000dab5000 0x0009100001b56a00 0x080000000ffff804 0x0100000001ffff00

def z44 : W := mkw 0x0101335aa0000000 0x0020266b54000000 0x30003ffff0000002 0x060007fffe000000

def z45 : W := mkw 0x1008080506c38571 0x82010100a0d870ae 0x080000000fc387fc 0x0100000001f870ff

def z46 : W := mkw 0x07b6725220000000 0x00f6ce4a44000000 0xa7e47fe330000002 0xf4fc8ffc66000000

def z47 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0x68dba79ccc3061c0 0xad1b74f399860c38

def z48 : W := mkw 0x0101335aa0000000 0x0020266b54000000 0xf0dbbffff0000003 0xbe1b77fffe000000

def z49 : W := mkw 0x06b6400001891000 0x00d6c80000312200 0x0724400003cd9800 0x40e488000079b300

def z50 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0x68c38780cc3267fc 0x8d1870f019864cff

def z51 : W := mkw 0x0809810cc4026069 0x4101302198804c0d 0xf0dba79cc002603b 0xbe1b74f398004c07

def z52 : W := mkw 0x0000000000000000 0x0000000000000000 0xf0245c63f0000003 0xde048b8c7e000000

def z53 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x0fdb80000ffff804 0x21fb700001ffff00

def z54 : W := mkw 0x25e03ee05b7c2f8e 0x24bc07dc0b6f85f1 0xefe07fe0fffc7fc6 0xfdfc0ffc1fff8ff8

def z55 : W := mkw 0x17fc38170feb8571 0x82ff8702e1fd70ae 0x9ffc381f0fff87ff 0xf3ff8703e1fff0ff

def z56 : W := mkw 0x000000015000a818 0x200000002a001503 0xd0244003f23ff83d 0xda0488007e47ff07

def z57 : W := mkw 0x084884844c3262ed 0x4109109089864c5d 0x080000000c3267fc 0x0100000001864cff

def z58 : W := mkw 0x0ffff7deec3262ed 0x41fffefbdd864c5d 0xfffffffffc3267ff 0xffffffffff864cff

def z59 : W := mkw 0x0008000404020061 0x000100008080400c 0x080000000c0207fc 0x01000000018040ff

def z60 : W := mkw 0x1100381702408571 0x82200702e04810ae 0x1000381f000007fa 0x02000703e00000ff

def z61 : W := mkw 0x000000015000a818 0x200000002a001503 0x50044003f003f839 0x0a0088007e007f07

def z62 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0xffe47fe3ffffffff 0xfffc8ffc7fffffff

def z63 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x8ffb80000ffc0004 0xf1ff700001ff8000

def z64 : W := mkw 0x004981088c224000 0x0009302111844800 0xf8dba79ccc326007 0xbf1b74f399864c00

def z65 : W := mkw 0x1100381302408510 0x82200702604810a2 0x0000180300000000 0x0000030060000000

def z66 : W := mkw 0x004880000dab5000 0x0009100001b56a00 0x080000000dc00000 0x0100000001b80000

def z67 : W := mkw 0x07b6725220000000 0x00f6ce4a44000000 0x0700000000000000 0x00e0000000000000

def z68 : W := mkw 0x0000040040102208 0x0000008008020441 0xf0000400c032663f 0x9e00008018064cc7

def z69 : W := mkw 0x021c000004830000 0x0043800000906000 0x8f1c00000fc38005 0x71e3800001f87000

def z70 : W := mkw 0x17fef8170febd571 0x82ffdf02e1fd7aae 0xdffff81f0fffffff 0xfbffff03e1ffffff

def z71 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0x37dbbffff0000002 0x26fb77fffe000000

def z72 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0244000023ff805 0xd80488000047ff00

def z73 : W := mkw 0x04e2c420593c7a0a 0x209c58840b278f41 0x60e3c460f03c7800 0x8c1c788c1e078f00

def z74 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0x38dba79ccc0007fa 0x271b74f3998000ff

def z75 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0xdf3c781f0fffffff 0xfbe78f03e1ffffff

def z76 : W := mkw 0x021c000004830000 0x0043800000906000 0x0f1800000dc00000 0x21e3000001b80000

def z77 : W := mkw 0x00010508c0102208 0x000020a118020441 0xf0dba79cc032663f 0xbe1b74f398064cc7

def z78 : W := mkw 0x0000080102008410 0x0000010020401082 0x900418030203863f 0x52008300604070c7

def z79 : W := mkw 0x0808800444026069 0x4101100088804c0d 0x0000000000026038 0x0000000000004c07

def z80 : W := mkw 0x24e006e0093c0286 0x049c00dc01278050 0x20e007e0003c0000 0x841c00fc00078000

def z81 : W := mkw 0x27fefee00fff5786 0x04ffdfdc01ffeaf0 0xefffffe00fffffc7 0xfdfffffc01fffff8

def z82 : W := mkw 0x24e347e8a93c0286 0x049c68fd15278050 0x60e3c7e0f03c0000 0x8c1c78fc1e078000

def z83 : W := mkw 0x0effc588cdbb728c 0x41dff8b119b76e51 0xefffc780cffff805 0xfdfff8f019ffff00

def z84 : W := mkw 0x06bec000058b5000 0x00d7d80000b16a00 0x473fc00003cff801 0x48e7f8000079ff00

def z85 : W := mkw 0x01403c800a700784 0x00280790014e00f0 0xafc03f800ff007c6 0xf5f807f001fe00f8

def z86 : W := mkw 0x1b5dbd9fcef3e7fd 0xc36bb7b3f9de7cff 0xffdfbf9fcff3e7ff 0xfffbf7f3f9fe7cff

def z87 : W := mkw 0x07b4325200000000 0x00f6864a40000000 0xb7fc3fff00000003 0xf6ff87ffe0000000

def z88 : W := mkw 0x25e03ee10b7c8796 0x04bc07dc216f90f2 0xbfe43fe30fff87ff 0xf7fc87fc61fff0ff

def z89 : W := mkw 0x1949bd9fce72e7fd 0xc32937b3f9ce5cff 0xf8dbbf9fcc3267ff 0xbf1b77f3f9864cff

def z90 : W := mkw 0x3ffdbfffcfffe7ff 0xc7ffb7fff9fffcff 0xffffbfffcfffe7ff 0xfffff7fff9fffcff

def z91 : W := mkw 0x08418588c830628c 0x410830b119060c51 0x60c38780c0306000 0x8c1870f018060c00

def z92 : W := mkw 0x0317711aa0000000 0x0062ee2354000000 0xd71ff81ff0000003 0x7ae3ff03fe000000

def z93 : W := mkw 0x0315311a80000000 0x0062a62350000000 0xf7dfbf9fc0000003 0xfefbf7f3f8000000

def z94 : W := mkw 0x07b77f7aa2140602 0x00f6efef544280c0 0xf7fffffff23c0607 0xfefffffffe4780c0

def z95 : W := mkw 0x004880000c224000 0x0009100001844800 0x080000000c326004 0x0100000001864c00

def z96 : W := mkw 0x25e2fee00b7c5786 0x04bc5fdc016f8af0 0xefe3ffe00ffc7fc6 0xfdfc7ffc01ff8ff8

def z97 : W := mkw 0x0214001200000000 0x0042800240000000 0x101c001f00000001 0x02038003e0000000

def z98 : W := mkw 0x04e00c200b3c0602 0x009c0184016780c0 0xafe01c600ffc0606 0xf5fc038c01ff80c0

def z99 : W := mkw 0x004880000c224000 0x0009100001844800 0xc8db80000c326005 0xb91b700001864c00

def z100 : W := mkw 0x08498588cc32628c 0x410930b119864c51 0xe8db8780cc326005 0xbd1b70f019864c00

def z101 : W := mkw 0x1314381702408571 0x82628702e04810ae 0x971c381f000007fb 0x72e38703e00000ff

def z102 : W := mkw 0x1008080506c38571 0x82010100a0d870ae 0x9818201c0fc387ff 0x3303040381f870ff

def z103 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0x8fe023800ffc01c4 0xf1fc047001ff8038

def z104 : W := mkw 0x25e03ee04b7c278e 0x04bc07dc096f84f1 0xffe03fe0cffe67ff 0xfffc07fc19ffccff

def z105 : W := mkw 0x0001010880000000 0x0000202110000000 0xf0dba79cc0000003 0xbe1b74f398000000

def z106 : W := mkw 0x18498d8dcef3e7fd 0xc30931b1b9de7cff 0xf8dba79ccff3e7ff 0xbf1b74f399fe7cff

def z107 : W := mkw 0x000008215204ac1a 0x200001042a409583 0x50245863f20ff839 0x4a048b0c7e41ff07

def z108 : W := mkw 0x0809810dd402e879 0x61013021ba805d0f 0x501fc01ff003f839 0x0a03f803fe007f07

def z109 : W := mkw 0x17bf735ea4c30161 0x82f7ee6bd498602c 0xfffffffffdc001c3 0xffffffffffb80038

def z110 : W := mkw 0x21003ee002540786 0x042007dc004a80f0 0x20003fe0000007c2 0x040007fc000000f8

def z111 : W := mkw 0x06b6400000000000 0x00d6c80000000000 0xc7ffc00000000001 0xf8fff80000000000

def z112 : W := mkw 0x04e3c348a9285000 0x009c786915250a00 0x60e3c7e0f03c7800 0x8c1c78fc1e078f00

def z113 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0x70045c63f003fe3b 0x0e008b8c7e007fc7

def z114 : W := mkw 0x090137dee01022ed 0x412026fbdc02045d 0x30003ffff00007fa 0x060007fffe0000ff

def z115 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x1f18381f0dc007fa 0x23e30703e1b800ff

def z116 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0xbfe03fe3fffc07fe 0xf7fc07fc7fff80ff

def z117 : W := mkw 0x0849818c8c2240e5 0x410930319184481c 0xf8dba79ccc0001c3 0xbf1b74f399800038

def z118 : W := mkw 0x08010dadd214aeff 0x610021b5ba4295df 0x30003ffff00007fa 0x060007fffe0000ff

def z119 : W := mkw 0x07fff35aadab5000 0x00fffe6b55b56a00 0xfffffffffffff807 0xffffffffffffff00

def z120 : W := mkw 0x0000000000000000 0x0000000000000000 0x00244000020d9800 0x400488000041b300

def z121 : W := mkw 0x06b6400000000000 0x00d6c80000000000 0xf7ffdc63f0000003 0xfefffb8c7e000000

def z122 : W := mkw 0x08498dadde36eeff 0x610931b5bbc6dddf 0xf8dbbffffc3267ff 0xbf1b77ffff864cff

def z123 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x0fffc0000fcd9800 0x61fff80001f9b300

def z124 : W := mkw 0x05a0324000000000 0x00b4064800000000 0xf7e47fe3f0000003 0xfefc8ffc7e000000

def z125 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0db800000000001 0xb81b700000000000

def z126 : W := mkw 0x0801058cc01022ed 0x410020b19802045d 0xf0dba79cc00007fb 0xbe1b74f3980000ff

def z127 : W := mkw 0x0000000000000000 0x0000000000000000 0x9018201c00000003 0x3203040380000000

def z128 : W := mkw 0x0314301200000000 0x0062860240000000 0x0704180300000000 0x40e0830060000000

def z129 : W := mkw 0x2ce187e8c93c628e 0x459c30fd19278c51 0x60e387e0c03c6000 0x8c1c70fc18078c00

def z130 : W := mkw 0x27f777faa93c0286 0x04feeeff55278050 0xf7fffffff03c0003 0xfefffffffe078000

def z131 : W := mkw 0x08488ca55e36eeff 0x61091194abc6dddf 0xf8245c63fe3fffff 0xdf048b8c7fc7ffff

def z132 : W := mkw 0x1b5db19e8ce341e5 0xc36bb633d19c683c 0x0fdba39c0dc001c0 0x21fb747381b80038

def z133 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0x30001c63f000063a 0x0600038c7e0000c7

def z134 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x0fdb80000dc00000 0x21fb700001b80000

def z135 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0x08dba39c0c3267fc 0x211b747381864cff

def z136 : W := mkw 0x0effc58ccdbb72ed 0x41dff8b199b76e5d 0xffffe79ccfffffff 0xfffffcf399ffffff

def z137 : W := mkw 0x0040048008300284 0x0008009001060050 0x20c0078000300000 0x841800f000060000

def z138 : W := mkw 0x25e8bee00fff5786 0x04bd17dc01ffeaf0 0xafe03fe00fffffc6 0xf5fc07fc01fffff8

def z139 : W := mkw 0x0008000404020061 0x000100008080400c 0x1018001c00020039 0x0203000380004007

def z140 : W := mkw 0x24e006e0593c2a8e 0x249c00dc0b278551 0x60e047e0f03c7800 0x8c1c08fc1e078f00

def z141 : W := mkw 0x1314381302c18510 0x82628702605830a2 0x971c381f03c18003 0x72e38703e0783000

def z142 : W := mkw 0x06fc00000dab0000 0x00df800001b56000 0x8ffc00000fff8005 0xf1ff800001fff000

def z143 : W := mkw 0x04e2c00009285000 0x009c580001250a00 0x00c3800000000000 0x0018700000000000

def z144 : W := mkw 0x084880840c2240e5 0x410910108184481c 0x080000000c0001c0 0x0100000001800038

def z145 : W := mkw 0x004880040c224061 0x000910008184480c 0xd8dba01c0c3267ff 0xbb1b740381864cff

def z146 : W := mkw 0x0217411aa0000000 0x0042e82354000000 0x501fc01ff0000001 0x0a03f803fe000000

def z147 : W := mkw 0x27f77ffaab7c0786 0x04feefff556f80f0 0xfffffffffffc07c7 0xffffffffffff80f8

def z148 : W := mkw 0x00000c204214260a 0x00000184084284c1 0xf0201c60c23e663f 0xde04038c1847ccc7

def z149 : W := mkw 0x27fefee15fffff9e 0x24ffdfdc2bfffff3 0xffffffe3ffffffff 0xfffffffc7fffffff

def z150 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0xcfffc0000dc00001 0xf9fff80001b80000

def z151 : W := mkw 0x25e13fe88b7c0786 0x04bc27fd116f80f0 0xfffbbffccffc07c7 0xffff77ff99ff80f8

def z152 : W := mkw 0x0effcdaddfbffeff 0x61dff9b5bbf7ffdf 0xffffffffffffffff 0xffffffffffffffff

def z153 : W := mkw 0x2fffffeccfff77ef 0x45fffffd99ffeefd 0xfffffffccfffffff 0xffffffff99ffffff

def z154 : W := mkw 0x0000080102008410 0x0000010020401082 0xf0245c63f203863f 0xde048b8c7e4070c7

def z155 : W := mkw 0x0108380406420561 0x0021070080c840ac 0x9f18381c0fc207ff 0x73e3070381f840ff

def z156 : W := mkw 0x2de9bfeccf7e67ef 0x45bd37fd99efccfd 0xfffbbffccffe67ff 0xffff77ff99ffccff

def z157 : W := mkw 0x06b6400001891000 0x00d6c80000312200 0xc724400003fff805 0xd8e48800007fff00

def z158 : W := mkw 0x25e03ac00b680584 0x04bc0758016d00b0 0x8fc03b800fc007c6 0x71f8077001f800f8

def z159 : W := mkw 0x0000000000000000 0x0000000000000000 0xc024400000000001 0xd804880000000000

def z160 : W := mkw 0x131c301604c30161 0x82638602c098602c 0x9f1c381f0dc001c3 0x73e38703e1b80038

def z161 : W := mkw 0x0ffff7deec3262ed 0x41fffefbdd864c5d 0xffdba79ccc3267ff 0xbffb74f399864cff

def z162 : W := mkw 0x37fc3ef75fffafff 0xa6ff87deebfff5ff 0xfffc7fffffffffff 0xffff8fffffffffff

def z163 : W := mkw 0x24e2c6e0093c5286 0x049c58dc01278a50 0x60e3c7e0003c7800 0x8c1c78fc00078f00

def z164 : W := mkw 0x0315335aa0000000 0x0062a66b54000000 0xb71c3ffff0000003 0x76e387fffe000000

def z165 : W := mkw 0x04e0000009280000 0x009c000001250000 0x00e00000003c0000 0x801c000000078000

def z166 : W := mkw 0x04e0000009280000 0x009c000001250000 0x8fe000000ffc0004 0xf1fc000001ff8000

def z167 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0xa7fbbffc00000002 0xf4ff77ff80000000

def z168 : W := mkw 0x0001010880000000 0x0000202110000000 0xf0fffffff0000003 0xfe1ffffffe000000

def z169 : W := mkw 0x04e00c215b3cae1a 0x209c01842b6795c3 0xffe45c63fffffe3f 0xfffc8b8c7fffffc7

def z170 : W := mkw 0x0849810ccc226069 0x4109302199844c0d 0xd8db801ccc32603d 0xbb1b700399864c07

def z171 : W := mkw 0x03143c335214ae1a 0x206287866a4295c3 0xf73c7c7ff23ffe3f 0xfee78f8ffe47ffc7

def z172 : W := mkw 0x25a03a60034c0502 0x04b4074c006980a0 0x0720186003cc0000 0x40e4030c00798000

def z173 : W := mkw 0x0849818c8c2240e5 0x410930319184481c 0xc8dba39c0c3261c5 0xb91b747381864c38

def z174 : W := mkw 0x0801058cc01022ed 0x410020b19802045d 0xf000279cc03267ff 0x9e0004f398064cff

def z175 : W := mkw 0x27f77ffaab7c0786 0x04feefff556f80f0 0xaffbbffc0ffc07c6 0xf5ff77ff81ff80f8

def z176 : W := mkw 0x06fec0000c224000 0x00dfd80001844800 0xcfffc0000c326005 0xf9fff80001864c00

def z177 : W := mkw 0x004880000c224000 0x0009100001844800 0x08db80000c000000 0x211b700001800000

def z178 : W := mkw 0x004880000dab5000 0x0009100001b56a00 0xc82440000ffff805 0xd904880001ffff00

def z179 : W := mkw 0x25e13ffaab7c0786 0x04bc27ff556f80f0 0xbfe03ffffffc07c6 0xf7fc07ffffff80f8

def z180 : W := mkw 0x021ecc215697fe1a 0x2043d9842ad2ffc3 0xf03fdc63f23ffe3f 0xde07fb8c7e47ffc7

def z181 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0xff3c7c7fffc387ff 0xffe78f8ffff870ff

def z182 : W := mkw 0x0ce3c588c938728c 0x419c78b119270e51 0x60e3c780c03c7800 0x8c1c78f018078f00

def z183 : W := mkw 0x0809810cc4026069 0x4101302198804c0d 0xd81ba01ccc0267ff 0x3b03740399804cff

def z184 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xf8ffe79cce3fffff 0xff1ffcf399c7ffff

def z185 : W := mkw 0x021c000004830000 0x0043800000906000 0xcf3c40000ffff805 0xf9e7880001ffff00

def z186 : W := mkw 0x24e00ee00b7c0786 0x049c01dc016f80f0 0x28e007e00ffc07c4 0x851c00fc01ff80f8

def z187 : W := mkw 0x00400ca00a340686 0x00080194014680d0 0xa8e03fe00e3c07c6 0xf51c07fc01c780f8

def z188 : W := mkw 0x27f773daa9680184 0x04feee7b552d0030 0xfffffffffdc001c3 0xffffffffffb80038

def z189 : W := mkw 0x0216400000000000 0x0042c80000000000 0x401fc00000000001 0x0803f80000000000

def z190 : W := mkw 0x200006e000140286 0x040000dc00028050 0x200007e000000000 0x040000fc00000000

def z191 : W := mkw 0x0002c00000005000 0x0000580000000a00 0x4003c00000007800 0x0800780000000f00

def z192 : W := mkw 0x21003ee002540786 0x042007dc004a80f0 0xaf003fe00fc007c6 0x75e007fc01f800f8

def z193 : W := mkw 0x16fec0170dabd071 0x82dfd802e1b57a0e 0xdfffc01f0ffff83d 0xfbfff803e1ffff07

def z194 : W := mkw 0x031c301204830000 0x0063860240906000 0x9f1c381f0fc38007 0x73e38703e1f87000

def z195 : W := mkw 0x335c3cb70fff87f7 0x866b8796e1fff0fe 0x9f1c381f0fff87ff 0x73e38703e1fff0ff

def z196 : W := mkw 0x06f6400009a91000 0x00dec80001352200 0x8fe440000ffd9804 0xf1fc880001ffb300

def z197 : W := mkw 0x1a1d811fc483e079 0xc343b023f8907c0f 0x501f801fc003e039 0x0a03f003f8007c07

def z198 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0x0fc023800ffc07c4 0x21f8047001ff80f8

def z199 : W := mkw 0x000000015000a818 0x200000002a001503 0xf0245c63f003f83b 0xde048b8c7e007f07

def z200 : W := mkw 0x1b5db59eccf363ed 0xc36bb6b3d99e6c7d 0xffdba79ccdf267ff 0xbffb74f399be4cff

def z201 : W := mkw 0x27fffffaafff5786 0x04ffffff55ffeaf0 0xffffffffffffffc7 0xfffffffffffffff8

def z202 : W := mkw 0x021ec00004835000 0x0043d80000906a00 0x401fc0000003f801 0x0803f80000007f00

def z203 : W := mkw 0x21003a6002440502 0x0420074c004880a0 0x0000186000000000 0x0000030c00000000

def z204 : W := mkw 0x121c081706c38571 0x82438102e0d870ae 0x181c001f0fc387fd 0x03038003e1f870ff

def z205 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xffe47fe3fffc07c7 0xfffc8ffc7fff80f8

def z206 : W := mkw 0x01013f7bf214ae1a 0x202027ef7e4295c3 0x30003ffff000063a 0x060007fffe0000c7

def z207 : W := mkw 0x00000c2002140602 0x00000184004280c0 0x00000000023c0604 0x00000000004780c0

def z208 : W := mkw 0x131c3c1746d3a779 0x82638782e8da74ef 0xff1c3c1fcff3e7ff 0xffe38783f9fe7cff

def z209 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x40ffc000003ff801 0x881ff8000007ff00

def z210 : W := mkw 0x17fef8170febd571 0x82ffdf02e1fd7aae 0x9fdfb81f0fc387ff 0x73fbf703e1f870ff

def z211 : W := mkw 0x0100301200000000 0x0020060240000000 0x1000381f00000002 0x02000703e0000000

def z212 : W := mkw 0x27b77b7aa34c0502 0x04f6ef6f546980a0 0xf7fffffff3cc0003 0xfefffffffe798000

def z213 : W := mkw 0x121f411fa4838071 0x8243e823f490700e 0x501fc01ff0038039 0x0a03f803fe007007

def z214 : W := mkw 0x06fec0040dab5061 0x00dfd80081b56a0c 0xdfffe01c0fffffff 0xfbfffc0381ffffff

def z215 : W := mkw 0x0fbff35ee4026069 0x41f7fe6bdc804c0d 0xf7fffffff002603b 0xfefffffffe004c07

def z216 : W := mkw 0x00000c2002140602 0x00000184004280c0 0xa0201c60023c0606 0xd404038c004780c0

def z217 : W := mkw 0x0849858c8c3242e5 0x410930b19186485c 0xa8dba79c0c3007c6 0xb51b74f3818600f8

def z218 : W := mkw 0x06fecc215fbffe1a 0x20dfd9842bf7ffc3 0xffffdc63fffffe3f 0xfffffb8c7fffffc7

def z219 : W := mkw 0x1000080502408571 0x82000100a04810ae 0x00000000000007f8 0x00000000000000ff

def z220 : W := mkw 0x07fff35aadab5000 0x00fffe6b55b56a00 0xfffffffffdc00003 0xffffffffffb80000

def z221 : W := mkw 0x0314381302008410 0x0062870260401082 0x971c381f0203863f 0x72e38703e04070c7

def z222 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0xafe03fe00ffffffe 0xf5fc07fc01ffffff

def z223 : W := mkw 0x131ef81706c3d571 0x8263df02e0d87aae 0xdf1ff81f0fc3ffff 0x7be3ff03e1f87fff

def z224 : W := mkw 0x25e03ae00b6c0586 0x04bc075c016d80b0 0x0fe03be00fcc01c0 0x61fc077c01f98038

def z225 : W := mkw 0x25e036e0097c0386 0x04bc06dc012f8070 0x2fe027e00dfc01c0 0xa5fc04fc01bf8038

def z226 : W := mkw 0x27fef2c00deb5184 0x04ffde5801bd6a30 0x0fdba3800dc001c0 0x21fb747001b80038

def z227 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xf8fffffffc3267ff 0xff1fffffff864cff

def z228 : W := mkw 0x11003c375254af7b 0xa2200786ea4a95ef 0x30003c7ff00007fa 0x0600078ffe0000ff

def z229 : W := mkw 0x25e83ee40f7e07e7 0x04bd07dc81efc0fc 0xbff83ffc0ffe07ff 0xf7ff07ff81ffc0ff

def z230 : W := mkw 0x0809810cc4026069 0x4101302198804c0d 0x501b801cc0026039 0x0a03700398004c07

def z231 : W := mkw 0x20400ca00b7c0786 0x04080194016f80f0 0x080000000ffc07c4 0x0100000001ff80f8

def z232 : W := mkw 0x37f43ef30bfd8796 0x86fe87de617fb0f2 0xafe43fe30ffd87c6 0xf5fc87fc61ffb0f8

def z233 : W := mkw 0x04e2c00009285000 0x009c580001250a00 0xc0e7c000023ff805 0xd81cf8000047ff00

def z234 : W := mkw 0x131c301704c38171 0x82638602e098702e 0x1f1c201f0dc381f9 0x23e38403e1b8703f

def z235 : W := mkw 0x131d391f86c38571 0x8263a723f0d870ae 0xffdfbf9fcfc387ff 0xfffbf7f3f9f870ff

def z236 : W := mkw 0x1fffffdfeef3e7fd 0xc3fffffbfdde7cff 0xfffffffffff3e7ff 0xfffffffffffe7cff

def z237 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0x30001c63f23ffe3e 0x0600038c7e47ffc7

def z238 : W := mkw 0x1108380506c38571 0x82210700a0d870ae 0x8f0038000fc387fe 0x71e0070001f870ff

def z239 : W := mkw 0x24e006e0093c0286 0x049c00dc01278050 0xa8e027e00c3c07c6 0xb51c04fc018780f8

def z240 : W := mkw 0x04e0048009380284 0x009c009001270050 0xafe027800ffc07c6 0xf5fc04f001ff80f8

def z241 : W := mkw 0x1000080102c18510 0x82000100205830a2 0x0000000003c18000 0x0000000000783000

def z242 : W := mkw 0x0000042050142a0a 0x200000840a028541 0x00000000003c7800 0x0000000000078f00

def z243 : W := mkw 0x20400ca15b7caf9e 0x240801942b6f95f3 0x080000000ffffffc 0x0100000001ffffff

def z244 : W := mkw 0x0000000000000000 0x0000000000000000 0x880020000c0007c6 0x31000400018000f8

def z245 : W := mkw 0x0000082112048c12 0x2000010422409182 0x00245863320d9800 0x40048b0c6641b300

def z246 : W := mkw 0x17bf7b5fa6c38571 0x82f7ef6bf4d870ae 0xffffffffffc387ff 0xfffffffffff870ff

def z247 : W := mkw 0x0000000110008810 0x2000000022001102 0x0004400330019800 0x0000880066003300

def z248 : W := mkw 0x135cb8170febd571 0x826b9702e1fd7aae 0x9f1c381f0fffffff 0x73e38703e1ffffff

def z249 : W := mkw 0x2de1bfe8cb7c678e 0x45bc37fd196f8cf1 0xefe3bfe0cffc67c6 0xfdfc77fc19ff8cf8

def z250 : W := mkw 0x04a34348a0000000 0x0094686914000000 0xf0e7dfe3f0000003 0xde1cfbfc7e000000

def z251 : W := mkw 0x1008000404c30161 0x820100008098602c 0x080000000dc001c0 0x0100000001b80038

def z252 : W := mkw 0x27b77ffaa2540786 0x04f6efff544a80f0 0xf7fffffff00007c3 0xfefffffffe0000f8

def z253 : W := mkw 0x004880000c224000 0x0009100001844800 0xc8ffc0000e3ff805 0xf91ff80001c7ff00

def z254 : W := mkw 0x0809810c84024061 0x410130219080480c 0x001b801c00000000 0x0003700380000000

def z255 : W := mkw 0x17fef0160deb5161 0x82ffde02c1bd6a2c 0x0fdba01c0dc001c0 0x21fb740381b80038

def z256 : W := mkw 0x1214001300818010 0x8242800260103002 0x0004000300018000 0x0000800060003000

def z257 : W := mkw 0x084185a8d8346a8e 0x610830b51b068d51 0x60e3c7e0f03c7800 0x8c1c78fc1e078f00

def z258 : W := mkw 0x2de9bfeddf7eefff 0x65bd37fdbbefddff 0xffffffffffffffff 0xffffffffffffffff

def z259 : W := mkw 0x0000000001891000 0x0000000000312200 0x0000000003cd9800 0x000000000079b300

def z260 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0xf0001c63f032663f 0x9e00038c7e064cc7

def z261 : W := mkw 0x06b6400001891000 0x00d6c80000312200 0x0700000001c00000 0x00e0000000380000

def z262 : W := mkw 0x0100325220000000 0x0020064a44000000 0x0000186330000000 0x0000030c66000000

def z263 : W := mkw 0x1000001700008071 0x82000002e000100e 0x1000001f00000038 0x02000003e0000007

def z264 : W := mkw 0x135c3c970ef387f5 0x826b8792e1de70fe 0xbfdc3f9f0ff387ff 0xf7fb87f3e1fe70ff

def z265 : W := mkw 0x28488ca44f7e67ef 0x4509119489efccfd 0x080000000ffe67fc 0x0100000001ffccff

def z266 : W := mkw 0x0000000000000000 0x0000000000000000 0x80200000023c0004 0xd004000000478000

def z267 : W := mkw 0x05a03a4002400500 0x00b40748004800a0 0xafe03fe00fc007c6 0xf5fc07fc01f800f8

def z268 : W := mkw 0x025ec0000ca35000 0x004bd80001946a00 0xc8dfc0000c33f805 0xb91bf80001867f00

def z269 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z270 : W := mkw 0x0000040000100200 0x0000008000020040 0xa000040000300606 0x94000080000600c0

def z271 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0x67fbe7fcf0000000 0xacff7cff9e000000

def z272 : W := mkw 0x27f77ffbfb7caf9e 0x24feefff7f6f95f3 0xffffffffffffffff 0xffffffffffffffff

def z273 : W := mkw 0x0314301200000000 0x0062860240000000 0xf73c7c7ff0000003 0xfee78f8ffe000000

def z274 : W := mkw 0x27f67ee00bfd1786 0x04fecfdc017fa2f0 0xafe47fe00ffd9fc6 0xf5fc8ffc01ffb3f8

def z275 : W := mkw 0x13143c3352d5af1a 0xa26287866a5ab5e3 0xf7245c63f3fffe3f 0xdee48b8c7e7fffc7

def z276 : W := mkw 0x0100300000400100 0x0020060000080020 0x0f0020000dc001c0 0x21e0040001b80038

def z277 : W := mkw 0x0a5fc58cccb372ed 0x414bf8b199966e5d 0xf8dfe79ccc33ffff 0xbf1bfcf399867fff

def z278 : W := mkw 0x27f67ee00b7c0786 0x04fecfdc016f80f0 0xefffffe00ffc07c7 0xfdfffffc01ff80f8

def z279 : W := mkw 0x0a1fc10cc4837069 0x4143f82198906e0d 0x501fc01cc003f839 0x0a03f80398007f07

def z280 : W := mkw 0x1100301600400161 0x82200602c008002c 0x0000201c000001c0 0x0000040380000038

def z281 : W := mkw 0x0849858ccdbb72ed 0x410930b199b76e5d 0xf8dba79ccfffffff 0xbf1b74f399ffffff

def z282 : W := mkw 0x0008000404020061 0x000100008080400c 0x0818201c0c0001c0 0x2103040381800038

def z283 : W := mkw 0x01013f7bf214ae1a 0x202027ef7e4295c3 0xf0247ffff23ffe3f 0xde048ffffe47ffc7

def z284 : W := mkw 0x02174d3bf214ae1a 0x2042e9a77e4295c3 0xf03fdc7ff23ffe3f 0xde07fb8ffe47ffc7

def z285 : W := mkw 0x00000c2112148e12 0x20000184224291c2 0xa0245c63323d9e06 0xd4048b8c6647b3c0

def z286 : W := mkw 0x06fec4205dbf7a0a 0x20dfd8840bb7ef41 0xefffc460fffff805 0xfdfff88c1fffff00

def z287 : W := mkw 0x17be7a5726c38571 0x82f7cf4ae4d870ae 0x9f3c787f3fc387ff 0x73e78f0fe7f870ff

def z288 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x4ffbc0000dfc7800 0xa9ff780001bf8f00

def z289 : W := mkw 0x21403ca00b7c0786 0x04280794016f80f0 0x8f0038000ffc07c6 0x71e0070001ff80f8

def z290 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0x573fd87ff0000001 0x4ae7fb0ffe000000

def z291 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0x00000000023ffe3c 0x000000000047ffc7

def z292 : W := mkw 0x0cebc7ccec3262ed 0x419d78f99d864c5d 0xf8fbe7fcfc3267ff 0xbf1f7cff9f864cff

def z293 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0x2fc03fe00dc007c2 0x25f807fc01b800f8

def z294 : W := mkw 0x0effc58ccc3262ed 0x41dff8b199864c5d 0xffffe79ccc3267ff 0xfffffcf399864cff

def z295 : W := mkw 0x07b77f7bf214ae1a 0x20f6efef7e4295c3 0xf7fffffff23ffe3f 0xfefffffffe47ffc7

def z296 : W := mkw 0x0000000040002008 0x0000000008000401 0x50000000c0026039 0x0a00000018004c07

def z297 : W := mkw 0x06fec0015dabf818 0x20dfd8002bb57f03 0xdfffc003fffff83d 0xfbfff8007fffff07

def z298 : W := mkw 0x27f67ef22b7c0786 0x04fecfde456f80f0 0xafe47fe33ffc07c6 0xf5fc8ffc67ff80f8

def z299 : W := mkw 0x025ec0000dab5000 0x004bd80001b56a00 0x481fc0000ffff805 0x0903f80001ffff00

def z300 : W := mkw 0x0841858cc83062ed 0x410830b199060c5d 0x70c3a79cc03067fa 0x8e1874f398060cff

def z301 : W := mkw 0x0a5fc59eec3262ed 0x414bf8b3dd864c5d 0xf8dfe79ffc3267ff 0xbf1bfcf3ff864cff

def z302 : W := mkw 0x00000c2002140602 0x00000184004280c0 0x20001c6000000602 0x0400038c000000c0

def z303 : W := mkw 0x1ffffd9fcffbf7fd 0xc3ffffb3f9ff7eff 0xffffff9fcfffffff 0xfffffff3f9ffffff

def z304 : W := mkw 0x37bc3a7707cf8573 0x86f7874ee0f9f0ae 0x9f3c387f0fcf87ff 0x73e7870fe1f9f0ff

def z305 : W := mkw 0x20400ca00b7c0786 0x04080194016f80f0 0xa8201c600ffc07c6 0xd504038c01ff80f8

def z306 : W := mkw 0x031c301604020061 0x00638602c080400c 0x9f1c381f0c0207ff 0x73e38703e18040ff

def z307 : W := mkw 0x21003ee002540786 0x042007dc004a80f0 0xa0203fe0023c07c6 0xd40407fc004780f8

def z308 : W := mkw 0x00488c215fbffe1a 0x200911842bf7ffc3 0xf8245c63fffffe3f 0xdf048b8c7fffffc7

def z309 : W := mkw 0x021c000404830061 0x004380008090600c 0x9f1c201c0fc387ff 0x73e3840381f870ff

def z310 : W := mkw 0x0fb777dee01022ed 0x41f6eefbdc02045d 0xf7fffffff00007fb 0xfefffffffe0000ff

def z311 : W := mkw 0x07bf735aa4830000 0x00f7ee6b54906000 0xffffffffffc38007 0xfffffffffff87000

def z312 : W := mkw 0x17b67a5322c18510 0x82f6cf4a645830a2 0x0724586333c18000 0x40e48b0c66783000

def z313 : W := mkw 0x004804840c3202e5 0x000900908186405c 0xb8d8279c0c3207ff 0xb71b04f3818640ff

def z314 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0x0000000000000638 0x00000000000000c7

def z315 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x8fdf80000fc38005 0x71fbf00001f87000

def z316 : W := mkw 0x2de8bee44f7e67ef 0x45bd17dc89efccfd 0xafe03fe00ffe67fe 0xf5fc07fc01ffccff

def z317 : W := mkw 0x06f6400009280000 0x00dec80001250000 0xcfffc0000ffc0005 0xf9fff80001ff8000

def z318 : W := mkw 0x07b7735bf000a818 0x20f6ee6b7e001503 0xf7fffffff003f83b 0xfefffffffe007f07

def z319 : W := mkw 0x2de13feccb7c27ef 0x45bc27fd996f84fd 0xbfe03ffccffc07fe 0xf7fc07ff99ff80ff

def z320 : W := mkw 0x20000820034c0502 0x04000104006980a0 0x0000000003cc0000 0x0000000000798000

def z321 : W := mkw 0x06b64821138d9c12 0x20d6c9042271b382 0x0724586333cd9800 0x40e48b0c6679b300

def z322 : W := mkw 0x1b5dbdbfdef7efff 0xe36bb7b7fbdefdff 0xffffffffffffffff 0xffffffffffffffff

def z323 : W := mkw 0x27fef2c00deb5184 0x04ffde5801bd6a30 0xcfffe3800ffff9c5 0xf9fffc7001ffff38

def z324 : W := mkw 0x0100324000000000 0x0020064800000000 0x20003fe000000002 0x040007fc00000000

def z325 : W := mkw 0x2949bfecce7667ef 0x452937fd99ceccfd 0xf8dbbffccc3267ff 0xbf1b77ff99864cff

def z326 : W := mkw 0x0000000000000000 0x0000000000000000 0xf0000400c0000003 0x9e00008018000000

def z327 : W := mkw 0x06fec4800dbb5284 0x00dfd89001b76a50 0xefffe7800fffffc7 0xfdfffcf001fffff8

def z328 : W := mkw 0x004884004c326208 0x0009108009864c41 0xf8db8400cc32663f 0xbf1b708019864cc7

def z329 : W := mkw 0x0008800004024000 0x0001100000804800 0x401b800000026001 0x0803700000004c00

def z330 : W := mkw 0x0100380002400500 0x00200700004800a0 0x0700180003c00000 0x40e0030000780000

def z331 : W := mkw 0x08098d2dd616ee7b 0x610131a5bac2ddcf 0xf03fdc7ff23ffe3f 0xde07fb8ffe47ffc7

def z332 : W := mkw 0x0000000000000000 0x0000000000000000 0x40204000003c7800 0x8804080000078f00

def z333 : W := mkw 0x2040008009680184 0x04080010012d0030 0x080000000dc001c0 0x0100000001b80038

def z334 : W := mkw 0x1b1d3d9fc6d3a7fd 0xc363a7b3f8da74ff 0xbf1c3f9fcfc387ff 0x77e387f3f9f870ff

def z335 : W := mkw 0x0ffff3deac2240e5 0x41fffe7bd584481c 0x0fdba39c0c0001c0 0x21fb747381800038

def z336 : W := mkw 0x04e880000dab5000 0x009d100001b56a00 0x8fe000000ffff804 0xf1fc000001ffff00

def z337 : W := mkw 0x210032c000400184 0x0420065800080030 0x00002380000001c0 0x0000047000000038

def z338 : W := mkw 0x25e8bee00f7e4786 0x04bd17dc01efc8f0 0xeffbbfe00ffe67c7 0xfdff77fc01ffccf8

def z339 : W := mkw 0x06fec8211fafdc12 0x20dfd90423f5fb82 0xcfffd8633ffff805 0xf9fffb0c67ffff00

def z340 : W := mkw 0x121c001604830061 0x82438002c090600c 0x0018001c00000000 0x0003000380000000

def z341 : W := mkw 0x000004215014aa1a 0x200000842a029543 0x70244463f03ff839 0x8e04888c7e07ff07

def z342 : W := mkw 0x06b6400000000000 0x00d6c80000000000 0x07db800000000000 0x20fb700000000000

def z343 : W := mkw 0x05a0324000000000 0x00b4064800000000 0x07c0238000000000 0x20f8047000000000

def z344 : W := mkw 0x0000042050142a0a 0x200000840a028541 0xe0244460f23ff805 0xdc04888c1e47ff00

def z345 : W := mkw 0x0000082112048c12 0x2000010422409182 0xf0245c63f20d9803 0xde048b8c7e41b300

def z346 : W := mkw 0x08418588c830628c 0x410830b119060c51 0xf0dba79cc0306003 0xbe1b74f398060c00

def z347 : W := mkw 0x27f773daa9680184 0x04feee7b552d0030 0x0fdba39c0dc001c0 0x21fb747381b80038

def z348 : W := mkw 0x25e036c009780384 0x04bc06d8012f0070 0xafc027800df007c6 0xb5f804f001be00f8

def z349 : W := mkw 0x2de9bfec8f7e47e7 0x45bd37fd91efc8fc 0xaffbbffc0ffc07c6 0xf5ff77ff81ff80f8

def z350 : W := mkw 0x084985acdc366aef 0x610930b59b86cd5d 0xf8fbe7fcfc3e7fff 0xbf1f7cff9f87cfff

def z351 : W := mkw 0x0001010880000000 0x0000202110000000 0x501b801cc0000001 0x0a03700398000000

def z352 : W := mkw 0x00010d29d214ae1a 0x200021a53a4295c3 0xf0fffffff23ffe3f 0xfe1ffffffe47ffc7

def z353 : W := mkw 0x00000c2102148612 0x00000184204290c2 0xb0241c63023f863f 0xd604838c6047f0c7

def z354 : W := mkw 0x331c3ef706d787f7 0x866387dee0daf0fe 0xbf1c3fff0fc387ff 0x77e387ffe1f870ff

def z355 : W := mkw 0x05a1334880000000 0x00b4266910000000 0xf7fbbffcc0000003 0xfeff77ff98000000

def z356 : W := mkw 0x0217411aa0000000 0x0042e82354000000 0xf0dfe79ff0000003 0xbe1bfcf3fe000000

def z357 : W := mkw 0x37b43a7303cd8512 0x86f6874e6079b0a2 0x0724186303cd8000 0x40e4830c6079b000

def z358 : W := mkw 0x10080c2556d7af7b 0xa2010184aadaf5ef 0x080000000ffffffc 0x0100000001ffffff

def z359 : W := mkw 0x0000040040102208 0x0000008008020441 0xf0245c63f032663f 0xde048b8c7e064cc7

def z360 : W := mkw 0x0a1fc11ee4026069 0x4143f823dc804c0d 0x501fc01ff0026039 0x0a03f803fe004c07

def z361 : W := mkw 0x0000042050142a0a 0x200000840a028541 0xf0245c63f03c7803 0xde048b8c7e078f00

def z362 : W := mkw 0x021ec00004835000 0x0043d80000906a00 0xcf1fc0000fc3f805 0x79e3f80001f87f00

def z363 : W := mkw 0x084084804830628c 0x4108109009060c51 0x0000000000306000 0x0000000000060c00

def z364 : W := mkw 0x06be4000058b1000 0x00d7c80000b16200 0x8f3c40000fcf9805 0x71e7880001f9f300

def z365 : W := mkw 0x131c301604c30161 0x82638602c098602c 0x9f18201c0dc207ff 0x33e3040381b840ff

def z366 : W := mkw 0x17be781707cb9571 0x82f7cf02e0f972ae 0x9f3c781f0fcf9fff 0x73e78f03e1f9f3ff

def z367 : W := mkw 0x06f6c00009a95000 0x00ded80001352a00 0x47e7c00003fdf800 0xc8fcf800007fbf00

def z368 : W := mkw 0x1008080506c38571 0x82010100a0d870ae 0x980418030fc387ff 0x5300830061f870ff

def z369 : W := mkw 0x0214000000000000 0x0042800000000000 0x871c000000000001 0x70e3800000000000

def z370 : W := mkw 0x08010588c010228c 0x410020b118020451 0x20000780c0000000 0x040000f018000000

def z371 : W := mkw 0x05a3735aa0000000 0x00b46e6b54000000 0x70e3fffff0000002 0x8e1c7ffffe000000

def z372 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0201c6000000002 0xd404038c00000000

def z373 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0xafe03fe00dc001c2 0xf5fc07fc01b80038

def z374 : W := mkw 0x25a03ee0035c0786 0x04b407dc006b80f0 0x27203fe003cc07c2 0x44e407fc007980f8

def z375 : W := mkw 0x2ffffffeef7e67ef 0x45ffffffddefccfd 0xfffffffffffe67ff 0xffffffffffffccff

def z376 : W := mkw 0x07fef2522dab5000 0x00ffde4a45b56a00 0xcfffd8633ffff805 0xf9fffb0c67ffff00

def z377 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x0f1c381f0fc181c0 0x61e38703e1f83038

def z378 : W := mkw 0x04a2400001081000 0x0094480000210200 0x00204000000c1800 0x0004080000018300

def z379 : W := mkw 0x031c380006c30500 0x0063870000d860a0 0x8f1c38000fc387c7 0x71e3870001f870f8

def z380 : W := mkw 0x05a0324000000000 0x00b4064800000000 0x0720186000000000 0x40e4030c00000000

def z381 : W := mkw 0x0216401220000000 0x0042c80244000000 0x0004400330000000 0x0000880066000000

def z382 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0xf7fffffff23ff807 0xfefffffffe47ff00

def z383 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0xffffdc63fffff807 0xfffffb8c7fffff00

def z384 : W := mkw 0x131c383716c78d73 0xa2638706e2d8f1ae 0x9f3c787f3fcf9fff 0x73e78f0fe7f9f3ff

def z385 : W := mkw 0x37fc3ad70feb85f5 0x86ff875ae1fd70be 0x9fdc3b9f0fc387ff 0x73fb8773e1f870ff

def z386 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0x97dfbb9f00000003 0x72fbf773e0000000

def z387 : W := mkw 0x0000042050142a0a 0x200000840a028541 0xf0204460f03e7e3f 0x9e04088c1e07cfc7

def z388 : W := mkw 0x0000000000000000 0x0000000000000000 0x400440000003f801 0x0800880000007f00

def z389 : W := mkw 0x0101335aa0000000 0x0020266b54000000 0xf0247ffff0000003 0xde048ffffe000000

def z390 : W := mkw 0x0217411aa0000000 0x0042e82354000000 0xf03fdc7ff0000003 0xde07fb8ffe000000

def z391 : W := mkw 0x00000c014210a618 0x00000180284214c3 0xf0041c03c233e63f 0xde00838078467cc7

def z392 : W := mkw 0x1100381702408571 0x82200702e04810ae 0x9004381f020387ff 0x52008703e04070ff

def z393 : W := mkw 0x0100380002400500 0x00200700004800a0 0x00003800000007c2 0x00000700000000f8

def z394 : W := mkw 0x07ffff7bffbffe1a 0x20ffffef7ff7ffc3 0xfffffffffffffe3f 0xffffffffffffffc7

def z395 : W := mkw 0x0effc58ccdbb72ed 0x41dff8b199b76e5d 0xffdba79ccdf267ff 0xbffb74f399be4cff

def z396 : W := mkw 0x0effc18c8dab50e5 0x41dff83191b56a1c 0xcfffe39c0ffff9c5 0xf9fffc7381ffff38

def z397 : W := mkw 0x27b67a6003cd1502 0x04f6cf4c0079a2a0 0x0724586003cd9800 0x40e48b0c0079b300

def z398 : W := mkw 0x17b77b5ba2c18510 0x82f6ef6b745830a2 0xf7fffffff3c18003 0xfefffffffe783000

def z399 : W := mkw 0x021ec00004835000 0x0043d80000906a00 0x001b800000000000 0x0003700000000000

def z400 : W := mkw 0x08010dadd214aeff 0x610021b5ba4295df 0xf0247ffff23fffff 0xde048ffffe47ffff

def z401 : W := mkw 0x0000048000100284 0x0000009000020050 0x20002780000007c2 0x040004f0000000f8

def z402 : W := mkw 0x06b6400001891000 0x00d6c80000312200 0xc7ffc00003cd9801 0xf8fff8000079b300

def z403 : W := mkw 0x0949bd8cce7267ed 0x412937b199ce4cfd 0xffdbbf9ccff267ff 0xfffb77f399fe4cff

def z404 : W := mkw 0x04a34768f0142a0a 0x209468ed1e028541 0x60e3c7e0f03c7800 0x8c1c78fc1e078f00

def z405 : W := mkw 0x07fff35aadab5000 0x00fffe6b55b56a00 0x0fdba39c0dc00000 0x21fb747381b80000

def z406 : W := mkw 0x07fef2400dab5000 0x00ffde4801b56a00 0xefffffe00ffff807 0xfdfffffc01ffff00

def z407 : W := mkw 0x000008015200ac18 0x200001002a401583 0xd0045803f203fe3f 0x5a008b007e407fc7

def z408 : W := mkw 0x0001010880000000 0x0000202110000000 0x3000279cc0000002 0x060004f398000000

def z409 : W := mkw 0x0de9b7cccc3262ed 0x41bd36f999864c5d 0xfffbbffccc3267ff 0xffff77ff99864cff

def z410 : W := mkw 0x17fef0160deb5161 0x82ffde02c1bd6a2c 0xcfffe01c0ffff9c5 0xf9fffc0381ffff38

def z411 : W := mkw 0x131c381306c38510 0x8263870260d870a2 0x8f1c18030fc38005 0x71e3830061f87000

def z412 : W := mkw 0x0801018c800000e5 0x410020319000001c 0x0000239c000001c0 0x0000047380000038

def z413 : W := mkw 0x06fecc215fbffe1a 0x20dfd9842bf7ffc3 0xcfffc0000ffffe3d 0xf9fff80001ffffc7

def z414 : W := mkw 0x0040000008200000 0x0008000001040000 0x88c000000c300004 0xb118000001860000

def z415 : W := mkw 0x0000042050142a0a 0x200000840a028541 0x20000460f0000000 0x0400008c1e000000

def z416 : W := mkw 0x0949b7deec3262ed 0x412936fbdd864c5d 0xf8dbbffffc3267ff 0xbf1b77ffff864cff

def z417 : W := mkw 0x17b6781303c99510 0x82f6cf02607932a2 0x0724580303cd9800 0x40e48b006079b300

def z418 : W := mkw 0x1a5d859fccb3e2fd 0xc34bb0b3f9967c5f 0xf8dfa79fcc33e7ff 0xbf1bf4f3f9867cff

def z419 : W := mkw 0x00000c2002140602 0x00000184004280c0 0xe0245c60023ffe07 0xdc048b8c0047ffc0

def z420 : W := mkw 0x0b5db59ecc3262ed 0x416bb6b3d9864c5d 0xffdfbf9fcc3267ff 0xfffbf7f3f9864cff

def z421 : W := mkw 0x06b6400000000000 0x00d6c80000000000 0xc7ffc000023ff805 0xf8fff8000047ff00

def z422 : W := mkw 0x07b6725220000000 0x00f6ce4a44000000 0xf7245c63f0000003 0xdee48b8c7e000000

def z423 : W := mkw 0x17fffb5fafebd571 0x82ffff6bf5fd7aae 0xffffffffffffffff 0xffffffffffffffff

def z424 : W := mkw 0x31003ef7025487f7 0x862007dee04a90fe 0x30003fff000007fa 0x060007ffe00000ff

def z425 : W := mkw 0x21403ee00a740786 0x042807dc014e80f0 0xa8c03fe00c3007c6 0xb51807fc018600f8

def z426 : W := mkw 0x07bf735ea4020061 0x00f7ee6bd480400c 0xfffffffffc0207ff 0xffffffffff8040ff

def z427 : W := mkw 0x1108381706c38571 0x82210702e0d870ae 0x1800381f0fc387fe 0x03000703e1f870ff

def z428 : W := mkw 0x24e00ca00b7c0786 0x049c0194016f80f0 0x8fe000000ffc07c4 0xf1fc000001ff80f8

def z429 : W := mkw 0x2de9b7cccd7a63ed 0x45bd36f999af4c7d 0xffdba79ccdf267ff 0xbffb74f399be4cff

def z430 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0xc0244000023ffe3d 0xd80488000047ffc7

def z431 : W := mkw 0x25a03e60035c0702 0x04b407cc006b80e0 0xa7201c6003fc0606 0xd4e4038c007f80c0

def z432 : W := mkw 0x24e002c009280084 0x049c005801250010 0x00c0038000000000 0x0018007000000000

def z433 : W := mkw 0x0ffff7deedbb72ed 0x41fffefbddb76e5d 0xffffffffffffffff 0xffffffffffffffff

def z434 : W := mkw 0x25a03a60034c0502 0x04b4074c006980a0 0xa7e03fe003cc0002 0xf4fc07fc00798000

def z435 : W := mkw 0x0008040444122269 0x000100808882444d 0xf818241ccc3267ff 0xbf03048399864cff

def z436 : W := mkw 0x17fefc375fffff7b 0xa2ffdf86ebffffef 0xfffffc7fffffffff 0xffffff8fffffffff

def z437 : W := mkw 0x25a0324001480100 0x04b4064800290020 0x0700000001c00000 0x00e0000000380000

def z438 : W := mkw 0x26fecca00fff5786 0x04dfd99401ffeaf0 0xcfffc0000fffffc5 0xf9fff80001fffff8

def z439 : W := mkw 0x1314383312c58d12 0xa26287066258b1a2 0x0724586333cd9800 0x40e48b0c6679b300

def z440 : W := mkw 0x0040000009280000 0x0008000001250000 0x080000000ffc0004 0x0100000001ff8000

def z441 : W := mkw 0x0100300000000000 0x0020060000000000 0x8700380000000002 0x70e0070000000000

def z442 : W := mkw 0x07fef0120dab5000 0x00ffde0241b56a00 0xdffff81f0ffff807 0xfbffff03e1ffff00

def z443 : W := mkw 0x17bf735fa4838071 0x82f7ee6bf490700e 0xf7fffffff003803b 0xfefffffffe007007

def z444 : W := mkw 0x04a34348a0000000 0x0094686914000000 0x00c3838000000000 0x0018707000000000

def z445 : W := mkw 0x07b6725221891000 0x00f6ce4a44312200 0x0724586333cd9800 0x40e48b0c6679b300

def z446 : W := mkw 0x05e0324009280000 0x00bc064801250000 0xafe03fe00ffc0006 0xf5fc07fc01ff8000

def z447 : W := mkw 0x0214000000810000 0x0042800000102000 0x0704000003c18000 0x40e0800000783000

def z448 : W := mkw 0x01003c2002540702 0x00200784004a80e0 0xaf203c600ffc07c6 0xf5e4078c01ff80f8

def z449 : W := mkw 0x1100381702408571 0x82200702e04810ae 0x9f00381f0fc007fe 0x73e00703e1f800ff

def z450 : W := mkw 0x06b7410880000000 0x00d6e82110000000 0xf7ffe79cc0000003 0xfefffcf398000000

def z451 : W := mkw 0x27fc3ee00fff0786 0x04ff87dc01ffe0f0 0xaffc3fe00fff87c7 0xf5ff87fc01fff0f8

def z452 : W := mkw 0x04e880000d2a4000 0x009d100001a54800 0xcffb80000ffe6005 0xf9ff700001ffcc00

def z453 : W := mkw 0x06b7435aa0000000 0x00d6e86b54000000 0x70ffc7fff0000001 0x8e1ff8fffe000000

def z454 : W := mkw 0x0000000000000000 0x0000000000000000 0x50044003f0000001 0x0a0088007e000000

def z455 : W := mkw 0x21003ee15254af9e 0x242007dc2a4a95f3 0x30003fe3f00007fa 0x060007fc7e0000ff

def z456 : W := mkw 0x0841058cc83022ed 0x410820b19906045d 0xb8c0279ccc3007fe 0xb71804f3998600ff

def z457 : W := mkw 0x04e0000009280000 0x009c000001250000 0xcfe440000ffff805 0xf9fc880001ffff00

def z458 : W := mkw 0x0100380102408510 0x00200700204810a2 0x9f0438030fc387ff 0x73e0870061f870ff

def z459 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0xcfdb80000df26005 0xb9fb700001be4c00

def z460 : W := mkw 0x0849858ddc32eafd 0x610930b1bb865d5f 0xf8dfe79ffc33ffff 0xbf1bfcf3ff867fff

def z461 : W := mkw 0x08498dadde36eeff 0x610931b5bbc6dddf 0xf8dba79cce3fffff 0xbf1b74f399c7ffff

def z462 : W := mkw 0x0314301200000000 0x0062860240000000 0x0718201c00000000 0x20e3040380000000

def z463 : W := mkw 0x27f43ef20b7c0786 0x04fe87de416f80f0 0xbffc3fff0ffc07c7 0xf7ff87ffe1ff80f8

def z464 : W := mkw 0x06b64c21539dbe1a 0x20d6c9842a73b7c3 0xf7245c63f3fffe3f 0xdee48b8c7e7fffc7

def z465 : W := mkw 0x025c80000dab5000 0x004b900001b56a00 0x8f1c00000ffff805 0x71e3800001ffff00

def z466 : W := mkw 0x0314381202400500 0x00628702404800a0 0x9f1c381f0fc007c7 0x73e38703e1f800f8

def z467 : W := mkw 0x17fef8130febd510 0x82ffdf0261fd7aa2 0xcfffd8030ffff805 0xf9fffb0061ffff00

def z468 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0x57dfe39ff0000001 0x2afbfc73fe000000

def z469 : W := mkw 0x135cb8170ee3c571 0x826b9702e1dc78ae 0xdfdfb81f0ff3e7ff 0xfbfbf703e1fe7cff

def z470 : W := mkw 0x17b77b5fa2408571 0x82f6ef6bf44810ae 0xf7fffffff00007fb 0xfefffffffe0000ff

def z471 : W := mkw 0x06b6400000000000 0x00d6c80000000000 0x0724400000000000 0x40e4880000000000

def z472 : W := mkw 0x0effc10ccdab7069 0x41dff82199b56e0d 0xdfffc01ccffff83d 0xfbfff80399ffff07

def z473 : W := mkw 0x0ce9858ccd3a62ed 0x419d30b199a74c5d 0xfffba79ccffe67ff 0xffff74f399ffccff

def z474 : W := mkw 0x084884844c3262ed 0x4109109089864c5d 0x9818201c0c3267ff 0x3303040381864cff

def z475 : W := mkw 0x26fec6e00dbf5286 0x04dfd8dc01b7ea50 0xefffc7e00ffff805 0xfdfff8fc01ffff00

def z476 : W := mkw 0x0000082002040402 0x0000010400408080 0x00201860020c0000 0x4004030c00418000

def z477 : W := mkw 0x07b6724000000000 0x00f6ce4800000000 0xe7ffffe000000003 0xfcfffffc00000000

def z478 : W := mkw 0x084884844c3262ed 0x4109109089864c5d 0xc8db80000c3267fd 0xb91b700001864cff

def z479 : W := mkw 0x0040800009285000 0x0008100001250a00 0x00000000003c7800 0x0000000000078f00

def z480 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x0f0418030fc387fc 0x41e0830061f870ff

def z481 : W := mkw 0x0000000100008010 0x0000000020001002 0x1004000300038039 0x0200800060007007

def z482 : W := mkw 0x25a03a61134c8d12 0x24b4074c226991a2 0x0724586333cd9800 0x40e48b0c6679b300

def z483 : W := mkw 0x00080c255616ae7b 0x20010184aac2d5cf 0xf83c7c7ffe3fffff 0xff078f8fffc7ffff

def z484 : W := mkw 0x0000000000000000 0x0000000000000000 0x8004000002038005 0x5000800000407000

def z485 : W := mkw 0x004884800c324284 0x0009109001864850 0xe8dba7800c3267c7 0xbd1b74f001864cf8

def z486 : W := mkw 0x06ffc348adab5000 0x00dff86915b56a00 0xefffc7e0fffff805 0xfdfff8fc1fffff00

def z487 : W := mkw 0x00000c2002140602 0x00000184004280c0 0xf0245c63f23c0607 0xde048b8c7e4780c0

def z488 : W := mkw 0x0ff7f7dae830628c 0x41fefefb5d060c51 0xf7fffffff0306003 0xfefffffffe060c00

def z489 : W := mkw 0x0217411aa0000000 0x0042e82354000000 0x001b801c00000000 0x0003700380000000

def z490 : W := mkw 0x0000040040102208 0x0000008008020441 0xf0244400c23ffe3f 0xde0488801847ffc7

def z491 : W := mkw 0x1108381706428571 0x82210702e0c850ae 0x9818381f0c0207ff 0x33030703e18040ff

def z492 : W := mkw 0x021c0c215697ae1a 0x204381842ad2f5c3 0xff3c5c63fffffe3f 0xffe78b8c7fffffc7

def z493 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0x70db879cc0326039 0x8e1b70f398064c07

def z494 : W := mkw 0x04e2c00009285000 0x009c580001250a00 0xcfe3c0000ffc7804 0xf9fc780001ff8f00

def z495 : W := mkw 0x0000000000000000 0x0000000000000000 0x60204460f0000000 0x8c04088c1e000000

def z496 : W := mkw 0x07b6725220000000 0x00f6ce4a44000000 0xc7ffd86330000001 0xf8fffb0c66000000

def z497 : W := mkw 0x01003c215254af1a 0x202007842a4a95e3 0xff247c63ffffffff 0xffe48f8c7fffffff

def z498 : W := mkw 0x0000000000000000 0x0000000000000000 0x0024586330000000 0x40048b0c66000000

def z499 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0xf7dba79cc0000003 0xbefb74f398000000

def z500 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000000326005 0x9800000000064c00

def z501 : W := mkw 0x17bf7b5fa6c38571 0x82f7ef6bf4d870ae 0x9fdfbb9f0fc387ff 0x73fbf773e1f870ff

def z502 : W := mkw 0x07f7f35aa9285000 0x00fefe6b55250a00 0xf7fffffff03c7803 0xfefffffffe078f00

def z503 : W := mkw 0x2de9b3cc8d6a41e5 0x45bd367991ad483c 0x0fdba39c0dc001c0 0x21fb747381b80038

def z504 : W := mkw 0x0000000000000000 0x0000000000000000 0x9004180300000003 0x5200830060000000

def z505 : W := mkw 0x07b77b7bb2048c12 0x20f6ef6f76409182 0xf7fffffff20d9803 0xfefffffffe41b300

def z506 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x4fdfc0000dc3f801 0x29fbf80001b87f00

def z507 : W := mkw 0x0809858cc41262ed 0x410130b198824c5d 0x701ba79cc00267fb 0x0e0374f398004cff

def z508 : W := mkw 0x0041058888300284 0x000820b111060050 0xf8dba79ccc3007c7 0xbf1b74f3998600f8

def z509 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0x27e01fe003fc0000 0xc4fc03fc007f8000

def z510 : W := mkw 0x20400ca15b7caf9e 0x240801942b6f95f3 0xf8245c63ffffffff 0xdf048b8c7fffffff

def z511 : W := mkw 0x104888050febd571 0x82091100a1fd7aae 0x080000000ffffffc 0x0100000001ffffff

def z512 : W := mkw 0x21003ee15254af9e 0x242007dc2a4a95f3 0xf0247fe3f23fffff 0xde048ffc7e47ffff

def z513 : W := mkw 0x07b6725220000000 0x00f6ce4a44000000 0x973c787f30000003 0x72e78f0fe6000000

def z514 : W := mkw 0x05e038000b680500 0x00bc0700016d00a0 0x8fe038000ffc07c6 0xf1fc070001ff80f8

def z515 : W := mkw 0x08418588c830628c 0x410830b119060c51 0xf0c38780c032663f 0x9e1870f018064cc7

def z516 : W := mkw 0x0000082112048c12 0x2000010422409182 0xc0245863323ff805 0xd8048b0c6647ff00

def z517 : W := mkw 0x17bc3a5706c38571 0x82f7874ae0d870ae 0xbffc3fff0fc387ff 0xf7ff87ffe1f870ff

def z518 : W := mkw 0x021ec0015483f818 0x2043d8002a907f03 0x501fc003f003f839 0x0a03f8007e007f07

def z519 : W := mkw 0x0001011aa0000000 0x0000202354000000 0x1000001ff0000000 0x02000003fe000000

def z520 : W := mkw 0x37fefef70fffd7f7 0x86ffdfdee1fffafe 0xffffffff0fffffff 0xffffffffe1ffffff

def z521 : W := mkw 0x0000080002400500 0x00000100004800a0 0x080000000fc007c4 0x0100000001f800f8

def z522 : W := mkw 0x121c081706838471 0x82438102e0d0708e 0x901c181f0203863f 0x52038303e04070c7

def z523 : W := mkw 0x07b77f7bf214ae1a 0x20f6efef7e4295c3 0xf7fffffff000063b 0xfefffffffe0000c7

def z524 : W := mkw 0x07b67a7332048c12 0x20f6cf4e66409182 0x07245863320d9800 0x40e48b0c6641b300

def z525 : W := mkw 0x0040048008300284 0x0008009001060050 0x080000000c3007c4 0x01000000018600f8

def z526 : W := mkw 0x0000000000000000 0x0000000000000000 0x900000000002063f 0x12000000000040c7

def z527 : W := mkw 0x0040008008200084 0x0008001001040010 0x08c023800c0001c0 0x2118047001800038

def z528 : W := mkw 0x05a1335aa0000000 0x00b4266b54000000 0xb7e03ffff0000002 0xf6fc07fffe000000

def z529 : W := mkw 0x1314381302c18510 0x82628702605830a2 0x8f0438030fc187c6 0x71e0870061f830f8

def z530 : W := mkw 0x05e036c008300284 0x00bc06d801060050 0xafe03fe00c3007c6 0xf5fc07fc018600f8

def z531 : W := mkw 0x20400ca00b7c0786 0x04080194016f80f0 0xa8c027800ffc07c6 0xb51804f001ff80f8

def z532 : W := mkw 0x06be400004830000 0x00d7c80000906000 0xcfffc0000fc38005 0xf9fff80001f87000

def z533 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0xc7ffe39c00000001 0xf8fffc7380000000

def z534 : W := mkw 0x0008080506028471 0x00010100a0c0508e 0x981c381f0e0387ff 0x73038703e1c070ff

def z535 : W := mkw 0x131c3c3706d78773 0x82638786e0daf0ee 0xbf3c3c7f0fff87ff 0xf7e7878fe1fff0ff

def z536 : W := mkw 0x0000040040102208 0x0000008008020441 0x60000400c0306000 0x8c00008018060c00

def z537 : W := mkw 0x07b77b5ba2008410 0x00f6ef6b74401082 0xf7fffffff203863f 0xfefffffffe4070c7

def z538 : W := mkw 0x04e2cc215b3cfe1a 0x209c59842b679fc3 0xf0e7dc63f23ffe3f 0xde1cfb8c7e47ffc7

def z539 : W := mkw 0x37ff7fffafff87f7 0x86ffeffff5fff0fe 0xffffffffffff87ff 0xfffffffffffff0ff

def z540 : W := mkw 0x10080c2556d7af7b 0xa2010184aadaf5ef 0xf8245c63ffffffff 0xdf048b8c7fffffff

def z541 : W := mkw 0x06f6c00009285000 0x00ded80001250a00 0xc7ffc000003c7801 0xf8fff80000078f00

def z542 : W := mkw 0x021c080106838410 0x0043810020d07082 0x9f1c18030fc3863f 0x73e3830061f870c7

def z543 : W := mkw 0x0000082112048c12 0x2000010422409182 0x90245863320f9e3f 0x52048b0c6641f3c7

def z544 : W := mkw 0x06b64c215214ae1a 0x20d6c9842a4295c3 0xf7ffdc63f23ffe3f 0xfefffb8c7e47ffc7

def z545 : W := mkw 0x25a03a60034c0502 0x04b4074c006980a0 0x8f2038600fcc07c6 0x71e4070c01f980f8

def z546 : W := mkw 0x04a2400000000000 0x0094480000000000 0x40e3c00000000000 0x881c780000000000

def z547 : W := mkw 0x0a5d858cccb362ed 0x414bb0b199966c5d 0xffdfa79ccff3e7ff 0xfffbf4f399fe7cff

def z548 : W := mkw 0x17bf735ea4c30161 0x82f7ee6bd498602c 0x0fdba39c0dc001c0 0x21fb747381b80038

def z549 : W := mkw 0x021ec00004835000 0x0043d80000906a00 0xc03fc000023ff805 0xd807f8000047ff00

def z550 : W := mkw 0x131c301704838071 0x82638602e090700e 0x971c381f0003803b 0x72e38703e0007007

def z551 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0x60245c63f23df800 0xcc048b8c7e47bf00

def z552 : W := mkw 0x21403ee00b7c0786 0x042807dc016f80f0 0x28003fe00ffc07c6 0x050007fc01ff80f8

def z553 : W := mkw 0x021fc11aa4835000 0x0043f82354906a00 0x501fc01ff003f801 0x0a03f803fe007f00

def z554 : W := mkw 0x131c3c3756d7af7b 0xa2638786eadaf5ef 0x9f1c381f0fffffff 0x73e38703e1ffffff

def z555 : W := mkw 0x08018108c0006008 0x4100302118000c01 0x40038000c0006000 0x0800700018000c00

def z556 : W := mkw 0x00488c215e36ee1a 0x200911842bc6ddc3 0xf8ffdc63fe3ffe3f 0xff1ffb8c7fc7ffc7

def z557 : W := mkw 0x0000040040102208 0x0000008008020441 0x30000400c000063a 0x06000080180000c7

def z558 : W := mkw 0x11003c375254af7b 0xa2200786ea4a95ef 0xf0247c7ff23fffff 0xde048f8ffe47ffff

def z559 : W := mkw 0x0008000004020000 0x0001000000804000 0x881800000c020005 0x3103000001804000

def z560 : W := mkw 0x16fec8050febd571 0x82dfd900a1fd7aae 0xcfffc0000ffffffd 0xf9fff80001ffffff

def z561 : W := mkw 0x06b7411aa0000000 0x00d6e82354000000 0xd7ffc01ff0000001 0xfafff803fe000000

def z562 : W := mkw 0x084884844dbb72ed 0x4109109089b76e5d 0x080000000ffffffc 0x0100000001ffffff

def z563 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0x60204460f23ffe3c 0x8c04088c1e47ffc7

def z564 : W := mkw 0x04a34348a0000000 0x0094686914000000 0xf0fbe7fcf0000003 0xbe1f7cff9e000000

def z565 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0x30245c63f20d9e3a 0x46048b8c7e41b3c7

def z566 : W := mkw 0x121ec0170483d071 0x8243d802e0907a0e 0x501fc01f0003f839 0x0a03f803e0007f07

def z567 : W := mkw 0x0ce3c7c8e830628c 0x419c78f91d060c51 0x60e3c7e0f0306000 0x8c1c78fc1e060c00

def z568 : W := mkw 0x07b7777af0142a0a 0x20f6eeef5e028541 0xf7fffffff03c7803 0xfefffffffe078f00

def z569 : W := mkw 0x17be781706c38571 0x82f7cf02e0d870ae 0xdffff81f0fc387ff 0xfbffff03e1f870ff

def z570 : W := mkw 0x0801010cc0002069 0x410020219800040d 0x1000001cc0000038 0x0200000398000007

def z571 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0xf0000400c23ffe3f 0x9e0000801847ffc7

def z572 : W := mkw 0x07fef8000feb5500 0x00ffdf0001fd6aa0 0xcffff8000fffffc7 0xf9ffff0001fffff8

def z573 : W := mkw 0x24e00ee00b3c0686 0x049c01dc016780d0 0xa0e01fe0023c0606 0xd41c03fc004780c0

def z574 : W := mkw 0x00034108a0000000 0x0000682114000000 0x4003c000f0000000 0x080078001e000000

def z575 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0x581b801ccc3267fd 0x0b03700399864cff

def z576 : W := mkw 0x0000082112048c12 0x2000010422409182 0x0000186330000000 0x0000030c66000000

def z577 : W := mkw 0x121c00175483a879 0xa2438002ea90750f 0x501c401ff003f839 0x0a038803fe007f07

def z578 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x0f2440000ffff804 0x41e4880001ffff00

def z579 : W := mkw 0x0001010880000000 0x0000202110000000 0x60c38780c0000000 0x8c1870f018000000

def z580 : W := mkw 0x000000015000a818 0x200000002a001503 0x000000000003f838 0x0000000000007f07

def z581 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0x70205c63f03c7e3a 0x8e040b8c7e078fc7

def z582 : W := mkw 0x00000c2052142e0a 0x200001840a4285c1 0xe0205c60f23c7e06 0xdc040b8c1e478fc0

def z583 : W := mkw 0x05a37348a0000000 0x00b46e6914000000 0xe7e3ffe0f0000002 0xfcfc7ffc1e000000

def z584 : W := mkw 0x004004804830228c 0x0008009009060451 0xf8c02780cc3267ff 0xbf1804f019864cff

def z585 : W := mkw 0x1b5db99f8ee3c5f5 0xc36bb733f1dc78be 0x9fdfbb9f0fc387ff 0x73fbf773e1f870ff

def z586 : W := mkw 0x04a2424020000000 0x0094484804000000 0x0020406030000000 0x0004080c06000000

def z587 : W := mkw 0x27b67a72234c0502 0x04f6cf4e446980a0 0x0724586333cc0000 0x40e48b0c66798000

def z588 : W := mkw 0x04a0024000000000 0x0094004800000000 0x20e007e000000000 0x841c00fc00000000

def z589 : W := mkw 0x000004015010aa18 0x200000802a021543 0xf0044403f033fe3f 0x9e0088807e067fc7

def z590 : W := mkw 0x2ce987eccd3e62ef 0x459d30fd99a7cc5d 0xf8fba7fccc3e67ff 0xbf1f74ff9987ccff

def z591 : W := mkw 0x084884844c3262ed 0x4109109089864c5d 0xf8000400cc3267ff 0x9f00008019864cff

def z592 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0xf0245c63f000063b 0xde048b8c7e0000c7

def z593 : W := mkw 0x24e00ee15b3cae9e 0x249c01dc2b6795d3 0xf0e45fe3f23ffe3f 0xde1c8bfc7e47ffc7

def z594 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x171c181f03c38039 0x42e38303e0787007

def z595 : W := mkw 0x07b77b5aa2400500 0x00f6ef6b544800a0 0xffffffffffc007c7 0xfffffffffff800f8

def z596 : W := mkw 0x30480ca50fff87f7 0x86090194a1fff0fe 0x080000000fff87fc 0x0100000001fff0ff

def z597 : W := mkw 0x0ffffffffe36eeff 0x61ffffffffc6dddf 0xfffffffffe3fffff 0xffffffffffc7ffff

def z598 : W := mkw 0x07b7775ae0102208 0x00f6eeeb5c020441 0xf7fffffff032663f 0xfefffffffe064cc7

def z599 : W := mkw 0x131d3b5fa6c38571 0x8263a76bf4d870ae 0xbf1c3fffffc387ff 0x77e387fffff870ff

def z600 : W := mkw 0x08418588c830628c 0x410830b119060c51 0xe8c3a780cc3067c6 0xbd1874f019860cf8

def z601 : W := mkw 0x20000ca002540786 0x04000194004a80f0 0x00000000000007c0 0x00000000000000f8

def z602 : W := mkw 0x0217411bf000a818 0x2042e8237e001503 0x501fc01ff003f839 0x0a03f803fe007f07

def z603 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0x0f2018600ffc07c4 0x41e4030c01ff80f8

def z604 : W := mkw 0x204004a0093c0286 0x0408009401278050 0x00000000003c0000 0x0000000000078000

def z605 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0xa0201c60023ffe3e 0xd404038c0047ffc7

def z606 : W := mkw 0x07f7735aa9280000 0x00feee6b55250000 0xfffffffffffc0007 0xffffffffffff8000

def z607 : W := mkw 0x25a03e61535caf1a 0x24b407cc2a6b95e3 0xf7245c63f3fffe3f 0xdee48b8c7e7fffc7

def z608 : W := mkw 0x04e0000009280000 0x009c000001250000 0x0fc000000dc00000 0x21f8000001b80000

def z609 : W := mkw 0x131c3c3756d7af7b 0xa2638786eadaf5ef 0xbf1c3c7fffc387ff 0x77e3878ffff870ff

def z610 : W := mkw 0x00010348a0000000 0x0000206914000000 0x200007e0f0000000 0x040000fc1e000000

def z611 : W := mkw 0x0001010880000000 0x0000202110000000 0x00dba39c00000000 0x201b747380000000

def z612 : W := mkw 0x1008000504838071 0x82010000a090700e 0x0000000000038038 0x0000000000007007

def z613 : W := mkw 0x21013ffaa2540786 0x042027ff544a80f0 0x30003ffff00007c2 0x060007fffe0000f8

def z614 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0x07fffbff30000000 0x60ffff7fe6000000

def z615 : W := mkw 0x121c001704838071 0x82438002e090700e 0x981c201f0c0387ff 0x33038403e18070ff

def z616 : W := mkw 0x025c80000ca34000 0x004b900001946800 0xcfdf80000ff3e005 0xf9fbf00001fe7c00

def z617 : W := mkw 0x11013b5fa2408571 0x8220276bf44810ae 0x30003ffff00007fa 0x060007fffe0000ff

def z618 : W := mkw 0x04a34f69f214ae1a 0x209469ed3e4295c3 0xf0e7dfe3f23ffe3f 0xde1cfbfc7e47ffc7

def z619 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000023ff804 0x000000000047ff00

def z620 : W := mkw 0x07fff35aadab5000 0x00fffe6b55b56a00 0xcfffe39c0ffff805 0xf9fffc7381ffff00

def z621 : W := mkw 0x0000000000000000 0x0000000000000000 0x30001c63f0000002 0x0600038c7e000000

def z622 : W := mkw 0x0008000004830000 0x0001000000906000 0x080000000fc38004 0x0100000001f87000

def z623 : W := mkw 0x27fefa600fef5502 0x04ffdf4c01fdeaa0 0xcfffd8600ffff805 0xf9fffb0c01ffff00

def z624 : W := mkw 0x0809058cc41222ed 0x410120b19882445d 0xb818279ccc0207ff 0x370304f3998040ff

def z625 : W := mkw 0x06ffc1088dab5000 0x00dff82111b56a00 0xffffe79ccffff807 0xfffffcf399ffff00

def z626 : W := mkw 0x04eac0000dab5000 0x009d580001b56a00 0x48e3c0000ffff804 0x891c780001ffff00

def z627 : W := mkw 0x07f777daa8300284 0x00feeefb55060050 0xfffffffffc3007c7 0xffffffffff8600f8

def z628 : W := mkw 0x1314301200c10100 0x8262860240182020 0x0700000001c00000 0x00e0000000380000

def z629 : W := mkw 0x08498d8dce32e6fd 0x410931b1b9c65cdf 0xf8dfbf9fce33e7ff 0xff1bf7f3f9c67cff

def z630 : W := mkw 0x0040800008204000 0x0008100001040800 0x40c3800000306000 0x8818700000060c00

def z631 : W := mkw 0x07b6701200000000 0x00f6ce0240000000 0xd7fff81f00000003 0xfaffff03e0000000

def z632 : W := mkw 0x35e83ee50fff87f7 0x86bd07dca1fff0fe 0xafe03fe00fff87fe 0xf5fc07fc01fff0ff

def z633 : W := mkw 0x084884844c3262ed 0x4109109089864c5d 0xa8c027800c3267fe 0xb51804f001864cff

def z634 : W := mkw 0x000000015000a818 0x200000002a001503 0x10000003f0000038 0x020000007e000007

def z635 : W := mkw 0x24e006e0093c0286 0x049c00dc01278050 0xafe007e00ffc0004 0xf5fc00fc01ff8000

def z636 : W := mkw 0x25e37fe8ab7c0786 0x04bc6ffd156f80f0 0xefe3ffe0fffc07c6 0xfdfc7ffc1fff80f8

def z637 : W := mkw 0x0000080102008410 0x0000010020401082 0xd0245803023ffe3f 0xda048b006047ffc7

def z638 : W := mkw 0x0efec4844dbb72ed 0x41dfd89089b76e5d 0xcfffc0000ffffffd 0xf9fff80001ffffff

def z639 : W := mkw 0x05a03e6002140602 0x00b407cc004280c0 0xa7e03fe0023c0606 0xf4fc07fc004780c0

def z640 : W := mkw 0x0317735aa0000000 0x0062ee6b54000000 0x701ffffff0000003 0x0e03fffffe000000

def z641 : W := mkw 0x06ffc11aadab5000 0x00dff82355b56a00 0xdfffc01ffffff805 0xfbfff803ffffff00

def z642 : W := mkw 0x35e03ef70b7c87f7 0x86bc07dee16f90fe 0xbfe03fff0ffc07fe 0xf7fc07ffe1ff80ff

def z643 : W := mkw 0x131f791fa6c38571 0x8263ef23f4d870ae 0xdf1ff81fffc387ff 0x7be3ff03fff870ff

def z644 : W := mkw 0x0000042000140202 0x0000008400028040 0x20200460003c0000 0x8404008c00078000

def z645 : W := mkw 0x25e03a600b6c0502 0x04bc074c016d80a0 0x8fe018600ffc0004 0xf1fc030c01ff8000

def z646 : W := mkw 0x00488c215fbffe1a 0x200911842bf7ffc3 0x080000000ffffe3c 0x0100000001ffffc7

def z647 : W := mkw 0x06b74348a0000000 0x00d6e86914000000 0xe7ffc7e0f0000001 0xfcfff8fc1e000000

def z648 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x101c381f000387fb 0x02038703e00070ff

def z649 : W := mkw 0x07bff35aa4835000 0x00f7fe6b54906a00 0xf7fffffff003f803 0xfefffffffe007f00

def z650 : W := mkw 0x06fec4004dbb7208 0x00dfd88009b76e41 0xffffc400cffffe3f 0xfffff88019ffffc7

def z651 : W := mkw 0x131c381606c30561 0x82638702c0d860ac 0x8f18381c0fc007c6 0x71e3070381f800f8

def z652 : W := mkw 0x0ffff3deac2240e5 0x41fffe7bd584481c 0xfffffffffc0001c3 0xffffffffff800038

def z653 : W := mkw 0x121c080506c38571 0x82438100a0d870ae 0x8f1c00000fc387fd 0x71e3800001f870ff

def z654 : W := mkw 0x0000002010040802 0x2000000402008100 0x00204060300c1800 0x0004080c06018300

def z655 : W := mkw 0x24a00260010c0002 0x0494004c00218000 0x00200060000c0000 0x0004000c00018000

def z656 : W := mkw 0x0008800004835000 0x0001100000906a00 0x000000000003f800 0x0000000000007f00

def z657 : W := mkw 0x0000000400000061 0x000000008000000c 0x1000201c000007fa 0x02000403800000ff

def z658 : W := mkw 0x021c000004830000 0x0043800000906000 0x001c000000038001 0x0003800000007000

def z659 : W := mkw 0x0cebc58ccd3a72ed 0x419d78b199a74e5d 0xf8fbe79ccc3e7fff 0xbf1f7cf39987cfff

def z660 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0xb0201c63f23c063e 0xd604038c7e4780c7

def z661 : W := mkw 0x121c0c375697ae7b 0xa2438186ead2f5cf 0xf03c5c7ff23ffe3f 0xde078b8ffe47ffc7

def z662 : W := mkw 0x0000080102008410 0x0000010020401082 0x0004180302018000 0x4000830060403000

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0x8f0000000fc00004 0x71e0000001f80000

def z664 : W := mkw 0x37fc32d60deb01e5 0x86ff865ac1bd603c 0x0fd8239c0dc001c0 0x21fb047381b80038

def z665 : W := mkw 0x08000484401022ed 0x410000908802045d 0x00000000000007f8 0x00000000000000ff

def z666 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0x50044003f23ffe3d 0x0a0088007e47ffc7

def z667 : W := mkw 0x1b1db91fc6c3e579 0xc363b723f8d87caf 0xdf1fb81fcfc3e7ff 0x7be3f703f9f87cff

def z668 : W := mkw 0x08498dacce3666ef 0x410931b599c6ccdd 0xf8fbbffcce3e67ff 0xff1f77ff99c7ccff

def z669 : W := mkw 0x131c381756c3ad79 0xa2638702ead875af 0xdf1c781fffc3ffff 0x7be38f03fff87fff

def z670 : W := mkw 0x04a0000000000000 0x0094000000000000 0x87e0000000000000 0xf0fc000000000000

def z671 : W := mkw 0x004880000dab5000 0x0009100001b56a00 0xc8db80000ffff805 0xb91b700001ffff00

def z672 : W := mkw 0x05a03e615214ae1a 0x20b407cc2a4295c3 0xf7e47fe3f23ffe3f 0xfefc8ffc7e47ffc7

def z673 : W := mkw 0x17bf7f7ff6d7af7b 0xa2f7efeffedaf5ef 0xffffffffffffffff 0xffffffffffffffff

def z674 : W := mkw 0x37fc3ef60fff07e7 0x86ff87dec1ffe0fc 0xaff83ffc0ffc07c6 0xf5ff07ff81ff80f8

def z675 : W := mkw 0x25a03ee002540786 0x04b407dc004a80f0 0xa7e03fe0000007c2 0xf4fc07fc000000f8

def z676 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0x67e7dfe3f0000000 0xccfcfbfc7e000000

def z677 : W := mkw 0x0000082112048c12 0x2000010422409182 0x00000000020d9800 0x000000000041b300

def z678 : W := mkw 0x0000080102008410 0x0000010020401082 0x000000000203863c 0x00000000004070c7

def z679 : W := mkw 0x06fecc200fbf5602 0x00dfd98401f7eac0 0xefffdc600ffffe07 0xfdfffb8c01ffffc0

def z680 : W := mkw 0x0effc18c8dab50e5 0x41dff83191b56a1c 0x0fdba39c0dc001c0 0x21fb747381b80038

def z681 : W := mkw 0x28498daccf7e67ef 0x450931b599efccfd 0xf8dba79ccffe67ff 0xbf1b74f399ffccff

def z682 : W := mkw 0x25e036e0093c0286 0x04bc06dc01278050 0xa7e03fe0003c0002 0xf4fc07fc00078000

def z683 : W := mkw 0x29013fecc25427ef 0x452027fd984a84fd 0x30003ffcc00007fa 0x060007ff980000ff

def z684 : W := mkw 0x0000000050002808 0x200000000a000501 0x40004000f0007800 0x080008001e000f00

def z685 : W := mkw 0x07fff35aac224000 0x00fffe6b55844800 0xfffffffffc326007 0xffffffffff864c00

def z686 : W := mkw 0x1314381702c18571 0x82628702e05830ae 0x1704381f03c187fa 0x42e08703e07830ff

def z687 : W := mkw 0x19013d9fc250a7fd 0xc32027b3f84a14ff 0x30003f9fc00007fa 0x060007f3f80000ff

def z688 : W := mkw 0x08418da9da34ee9e 0x610831b53b469dd3 0xf0e7dfe3f23ffe3f 0xde1cfbfc7e47ffc7

def z689 : W := mkw 0x00400ca15a34ae9e 0x200801942b4695d3 0xf8e47fe3fe3fffff 0xff1c8ffc7fc7ffff

def z690 : W := mkw 0x20488ca00fff5786 0x0409119401ffeaf0 0x080000000fffffc4 0x0100000001fffff8

def z691 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0c0278000000002 0xb41804f000000000

def z692 : W := mkw 0x27fefee00fff5786 0x04ffdfdc01ffeaf0 0xaffbbfe00ffc07c6 0xf5ff77fc01ff80f8

def z693 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0x37247ffff0000002 0x46e48ffffe000000

def z694 : W := mkw 0x0000080102008410 0x0000010020401082 0x100018030000063a 0x02000300600000c7

def z695 : W := mkw 0x0000040040102208 0x0000008008020441 0x000000000032663c 0x0000000000064cc7

def z696 : W := mkw 0x06fec8010fabd410 0x00dfd90021f57a82 0xdfffd8030ffffe3f 0xfbfffb0061ffffc7

def z697 : W := mkw 0x0216400000811000 0x0042c80000102200 0x0004400000019800 0x0000880000003300

def z698 : W := mkw 0x121c001704838071 0x82438002e090700e 0x9f1c001f0fc3803d 0x73e38003e1f87007

def z699 : W := mkw 0x0841818888204084 0x4108303111040810 0x00c3838000000000 0x0018707000000000

def z700 : W := mkw 0x0000080002000400 0x0000010000400080 0x8000180002000606 0x50000300004000c0

def z701 : W := mkw 0x07b67e737214ae1a 0x20f6cfce6e4295c3 0xf7245c63f23ffe3f 0xdee48b8c7e47ffc7

def z702 : W := mkw 0x1b5cbc974ef3e7fd 0xc36b9792e9de7cff 0x9f1c381f0ff3e7ff 0x73e38703e1fe7cff

def z703 : W := mkw 0x0849818ccc2260ed 0x4109303199844c1d 0x58dba39ccc0261f9 0x2b1b747399804c3f

def z704 : W := mkw 0x04eac0000d2a5000 0x009d580001a54a00 0xc8fbc0000c3e7805 0xb91f78000187cf00

def z705 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0x20e03fe0003c07c2 0x841c07fc000780f8

def z706 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0xb0041c63f203863f 0x5600838c7e4070c7

def z707 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x0f1c381f0fc387fc 0x61e38703e1f870ff

def z708 : W := mkw 0x121f411ff483a879 0xa243e823fe90750f 0x501fc01ff003f839 0x0a03f803fe007f07

def z709 : W := mkw 0x04e2c00009285000 0x009c580001250a00 0xcfe7c0000ffff805 0xf9fcf80001ffff00

def z710 : W := mkw 0x121c001704838071 0x82438002e090700e 0x9f1c201f0fc387ff 0x73e38403e1f870ff

def z711 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0xbf3c3c7f0fc387ff 0xf7e7878fe1f870ff

def z712 : W := mkw 0x27b67a73334c8d12 0x24f6cf4e666991a2 0x0724586333cd9800 0x40e48b0c6679b300

def z713 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xf8dfe79ffc3267ff 0xbf1bfcf3ff864cff

def z714 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xefe07fe00ffc7fc6 0xfdfc0ffc01ff8ff8

def z715 : W := mkw 0x0ffef6d66c3262ed 0x41ffdedacd864c5d 0x0f2458633c3267fc 0x41e48b0c67864cff

def z716 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xf8dba79ccc0007fb 0xbf1b74f3998000ff

def z717 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xc8dba39c0c3267fd 0xb91b747381864cff

def z718 : W := mkw 0x25e03ac10b688594 0x04bc0758216d10b2 0x9fc43b830fc387ff 0x73f8877061f870ff

def z719 : W := mkw 0x0eb7458cc19932ed 0x41d6e8b19833265d 0x3724679cc3cd9ffa 0x46e48cf39879b3ff

def z720 : W := mkw 0x22574dbaab7c0786 0x044ae9b7556f80f0 0x581fc01ffffc07c5 0x0b03f803ffff80f8

def z721 : W := mkw 0x25e03ee05b7c2f8e 0x24bc07dc0b6f85f1 0xafe03fe0fffc07c6 0xf5fc07fc1fff80f8

def z722 : W := mkw 0x06b7435aa0000000 0x00d6e86b54000000 0xf0ffdffff0000003 0xde1ffbfffe000000

def z723 : W := mkw 0x231efee006d75786 0x0463dfdc00daeaf0 0x601fffe00003ffc3 0x0c03fffc00007ff8

def z724 : W := mkw 0x131c301604c30161 0x82638602c098602c 0x9f1c201c0fc387ff 0x73e3840381f870ff

def z725 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0xff1c3c1fcfc387ff 0xffe38783f9f870ff

def z726 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0x38dba79ccc3267fe 0x271b74f399864cff

def z727 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xf8dba79cce3fffff 0xbf1b74f399c7ffff

def z728 : W := mkw 0x25e03ae11b6c8d96 0x24bc075c236d91b2 0x0fe47be33fcd99c0 0x61fc8f7c67f9b338

def z729 : W := mkw 0x084985acdc366aef 0x610930b59b86cd5d 0xf8fffffffc3e7fff 0xff1fffffff87cfff

def z730 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x8f1c201c0fc387fd 0x71e3840381f870ff

def z731 : W := mkw 0x0a1fc11ee4837069 0x4143f823dc906e0d 0x501fc01ff003f839 0x0a03f803fe007f07

def z732 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x1f1c201f0fc387fd 0x23e38403e1f870ff

def z733 : W := mkw 0x36fc06f70dbf82f7 0x86df80dee1b7f05e 0x30fc07ff003f8039 0x861f80ffe007f007

def z734 : W := mkw 0x07b7735aa1891000 0x00f6ee6b54312200 0xf7fffffff3fff807 0xfefffffffe7fff00

def z735 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xafe47fe33ffc07c6 0xf5fc8ffc67ff80f8

def z736 : W := mkw 0x25e032e0096c0186 0x04bc065c012d8030 0x0fe023e00dcc01c0 0x21fc047c01b98038

def z737 : W := mkw 0x25e03ee10b7c8796 0x04bc07dc216f90f2 0xbfe03fe30ffc07fe 0xf7fc07fc61ff80ff

def z738 : W := mkw 0x21013ffbf254af9e 0x242027ff7e4a95f3 0x30003ffff00007fa 0x060007fffe0000ff

def z739 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0x2fe03fe00ffc01c0 0xe5fc07fc01ff8038

def z740 : W := mkw 0x0ce3c7c8e938728c 0x419c78f91d270e51 0x60e3c7e0f03c7800 0x8c1c78fc1e078f00

def z741 : W := mkw 0x07b77f7bf214ae1a 0x20f6efef7e4295c3 0x07dba39c023ffe3c 0x20fb74738047ffc7

def z742 : W := mkw 0x15e2f8170b68d571 0x82bc5f02e16d1aae 0x50e3f81f003c7ffa 0x8a1c7f03e0078fff

def z743 : W := mkw 0x05a0324000400100 0x00b4064800080020 0xafe03fe00dc001c2 0xf5fc07fc01b80038

def z744 : W := mkw 0x01003a4002400500 0x00200748004800a0 0xaf003fe00fc007c6 0x75e007fc01f800f8

def z745 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xafc027800ffc07c6 0xb5f804f001ff80f8

def z746 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0x8fc023800fc001c4 0x71f8047001f80038

def z747 : W := mkw 0x21003ac002400584 0x04200758004800b0 0x8f003b800fc007c6 0x71e0077001f800f8

def z748 : W := mkw 0x25e03ae00b6c0586 0x04bc075c016d80b0 0x8fe03be00ffc01c4 0xf1fc077c01ff8038

def z749 : W := mkw 0x25e2fee00b7c5786 0x04bc5fdc016f8af0 0xafe3bfe00ffc07c6 0xf5fc77fc01ff80f8

def z750 : W := mkw 0x084989ad9e26ccf7 0x61093135b3c4d99e 0x08fffbff3e0d99c0 0x611fff7fe7c1b338

def z751 : W := mkw 0x06fec0800dab5084 0x00dfd81001b56a10 0xcfffe3800ffff9c5 0xf9fffc7001ffff38

def z752 : W := mkw 0x24e00ee00b7c0786 0x049c01dc016f80f0 0xafe007e00ffc07c4 0xf5fc00fc01ff80f8

def z753 : W := mkw 0x25e03ef22b7c0786 0x04bc07de456f80f0 0xafe03fe33ffc07c6 0xf5fc07fc67ff80f8

def z754 : W := mkw 0x0849818c8c2240e5 0x410930319184481c 0x18dba39c0c0007fa 0x231b7473818000ff

def z755 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x4f3fc0000ffff805 0x49e7f80001ffff00

def z756 : W := mkw 0x131c343654d72b6b 0xa2638686ca9ae56d 0x6f38647cfdfc79c0 0xade70c8f9fbf8f38

def z757 : W := mkw 0x121d011fa4838071 0x8243a023f490700e 0x101c001ff0038039 0x02038003fe007007

def z758 : W := mkw 0x131cb81706c3c571 0x82639702e0d878ae 0xdf1fb81f0fc3e7ff 0x7be3f703e1f87cff

def z759 : W := mkw 0x025ec0000dab5000 0x004bd80001b56a00 0xcf1fc0000ffff805 0x79e3f80001ffff00

def z760 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0xcfffe0000fffffc7 0xf9fffc0001fffff8

def z761 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0x98dba39c0c3267ff 0x331b747381864cff

def z762 : W := mkw 0x06bec000058b5000 0x00d7d80000b16a00 0xc73fc00003fff805 0xd8e7f800007fff00

def z763 : W := mkw 0x29013fedd254afff 0x652027fdba4a95ff 0x30003ffff00007fa 0x060007fffe0000ff

def z764 : W := mkw 0x05a03a4102408510 0x00b40748204810a2 0xffe47fe3ffc387ff 0xfffc8ffc7ff870ff

def z765 : W := mkw 0x25e032c15968a99c 0x24bc06582b2d1533 0x5fc46383fdc3f9f9 0x2bf88c707fb87f3f

def z766 : W := mkw 0x121d011f84838071 0x8243a023f090700e 0x501f801fc0038039 0x0a03f003f8007007

def z767 : W := mkw 0x2ce187e8d93c6a8e 0x659c30fd1b278d51 0x60e3c7e0f03c7800 0x8c1c78fc1e078f00

def z768 : W := mkw 0x25e03ac00b680584 0x04bc0758016d00b0 0xafe03fe00fc007c6 0xf5fc07fc01f800f8

def z769 : W := mkw 0x06f6400009280000 0x00dec80001250000 0xcfffc0000ffff805 0xf9fff80001ffff00

def z770 : W := mkw 0x35e03ef30b7c8796 0x86bc07de616f90f2 0xafe03fe30ffc07c6 0xf5fc07fc61ff80f8

def z771 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x1f18381f0fc387fe 0x23e30703e1f870ff

def z772 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0xdfffc0000ffffe3f 0xfbfff80001ffffc7

def z773 : W := mkw 0x121f411ea4830061 0x8243e823d490600c 0x501fc01ff0000001 0x0a03f803fe000000

def z774 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0xffffffffffc00007 0xfffffffffff80000

def z775 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0xf7fffffff2038007 0xfefffffffe407000

def z776 : W := mkw 0x26fec2c00dab5084 0x04dfd85801b56a10 0xcfffc3800ffff805 0xf9fff87001ffff00

def z777 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0x77ffdffff0000001 0xcefffbfffe000000

def z778 : W := mkw 0x07b7735aa0400100 0x00f6ee6b54080020 0xfffffffffdc001c3 0xffffffffffb80038

def z779 : W := mkw 0x2ce3c7e8c93c728e 0x459c78fd19278e51 0x60e3c7e0c03c7800 0x8c1c78fc18078f00

def z780 : W := mkw 0x00000ca15214ae9e 0x200001942a4295d3 0xf0247fe3f23fffff 0xde048ffc7e47ffff

def z781 : W := mkw 0x05a03e615254af1a 0x20b407cc2a4a95e3 0xffe47fe3ffffffff 0xfffc8ffc7fffffff

def z782 : W := mkw 0x284985accd3e62ef 0x450930b599a7cc5d 0xf8dba79ccc3e67ff 0xbf1b74f39987ccff

def z783 : W := mkw 0x06f6c00009a95000 0x00ded80001352a00 0xcfe7c0000ffdf804 0xf9fcf80001ffbf00

def z784 : W := mkw 0x25e036c009780384 0x04bc06d8012f0070 0x2fc027800df001c0 0xa5f804f001be0038

def z785 : W := mkw 0x21003ee15254af9e 0x242007dc2a4a95f3 0xff247fe3ffffffff 0xffe48ffc7fffffff

def z786 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0xdfffe01c0ffff807 0xfbfffc0381ffff00

def z787 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xefe03fe00ffe67c7 0xfdfc07fc01ffccf8

def z788 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xf8dfa79cce33e7ff 0xff1bf4f399c67cff

def z789 : W := mkw 0x05a03e6002540702 0x00b407cc004a80e0 0xafe03fe00ffc07c6 0xf5fc07fc01ff80f8

def z790 : W := mkw 0x0ce18588c938628c 0x419c30b119270c51 0x60e38780c03c6000 0x8c1c70f018078c00

def z791 : W := mkw 0x25e03ee11b7c8f96 0x24bc07dc236f91f2 0xafe03fe33ffc07c6 0xf5fc07fc67ff80f8

def z792 : W := mkw 0x1a1d011fc483a079 0xc343a023f890740f 0x101c001fc0038039 0x02038003f8007007

def z793 : W := mkw 0x25e036e0097c0386 0x04bc06dc012f8070 0xafe03fe00dfc01c2 0xf5fc07fc01bf8038

def z794 : W := mkw 0x1a1d811fd483e879 0xe343b023fa907d0f 0x501fc01ff003f839 0x0a03f803fe007f07

def z795 : W := mkw 0x28488ca55f7eefff 0x65091194abefddff 0x080000000ffffffc 0x0100000001ffffff

def z796 : W := mkw 0x25e03ee01b7c0f86 0x24bc07dc036f81f0 0xafe07fe03ffc1fc6 0xf5fc0ffc07ff83f8

def z797 : W := mkw 0x121f411fa4838071 0x8243e823f490700e 0x101f801f00038039 0x0203f003e0007007

def z798 : W := mkw 0x0849858c8c3242e5 0x410930b19186485c 0xb8dba79c0c3207ff 0xb71b74f3818640ff

def z799 : W := mkw 0x121fc11fa483d071 0x8243f823f4907a0e 0x501fc01ff003f839 0x0a03f803fe007f07

def z800 : W := mkw 0x131c3a5726c38571 0x8263874ae4d870ae 0x9f1c387f3fc387ff 0x73e3870fe7f870ff

def z801 : W := mkw 0x0a1d810cc4836069 0x4143b02198906c0d 0x501f801cc003e039 0x0a03f00398007c07

def z802 : W := mkw 0x1b55bd9bcaf1e79c 0xc36ab7b3795e3cf3 0x67c79f83c3f1e000 0xccf8f3f0787e3c00

def z803 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0xb7dfbffff0000003 0x76fbf7fffe000000

def z804 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xa8dba79c0c3267fe 0xb51b74f381864cff

def z805 : W := mkw 0x0101335aa0000000 0x0020266b54000000 0x30dbbffff0000002 0x261b77fffe000000

def z806 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0x0fe03be00ffc07c4 0x61fc077c01ff80f8

def z807 : W := mkw 0x05a03a4002400500 0x00b40748004800a0 0x8fc03b800fc007c6 0x71f8077001f800f8

def z808 : W := mkw 0x1a1fc11fc483f079 0xc343f823f8907e0f 0x501fc01fc003f839 0x0a03f803f8007f07

def z809 : W := mkw 0x25e27ee00b7c1786 0x04bc4fdc016f82f0 0xafe07fe00ffc1fc6 0xf5fc0ffc01ff83f8

def z810 : W := mkw 0x2da9bb6cc74e656b 0x45b5376d98e9ccad 0x573b987cc3ce6039 0x4ae7730f9879cc07

def z811 : W := mkw 0x05a0324000400100 0x00b4064800080020 0x0fc023800dc001c0 0x21f8047001b80038

def z812 : W := mkw 0x1a1d8d3fd697ee7b 0xe343b1a7fad2fdcf 0xf03fdc7ff23ffe3f 0xde07fb8ffe47ffc7

def z813 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0x50245863f23ffe3d 0x4a048b0c7e47ffc7

def z814 : W := mkw 0x031c381606420561 0x00638702c0c840ac 0x9f1c381f0fc207ff 0x73e38703e1f840ff

def z815 : W := mkw 0x0ce3c588c938728c 0x419c78b119270e51 0x60c38780c0306000 0x8c1870f018060c00

def z816 : W := mkw 0x131c381606c30561 0x82638702c0d860ac 0x9f18381c0fc207ff 0x73e3070381f840ff

def z817 : W := mkw 0x121f4d3ff697ae7b 0xa243e9a7fed2f5cf 0xf03fdc7ff23ffe3f 0xde07fb8ffe47ffc7

def z818 : W := mkw 0x17b67a5322c18510 0x82f6cf4a645830a2 0x0704180303c18000 0x40e0830060783000

def z819 : W := mkw 0x14ab4b4da6c38571 0x82956969b4d870ae 0x68e3c7e0ffc387fc 0x8d1c78fc1ff870ff

def z820 : W := mkw 0x0841858cc83062ed 0x410830b199060c5d 0xf0dba79cc03067fb 0xbe1b74f398060cff

def z821 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0x2fc03fe00dc001c2 0x25f807fc01b80038

def z822 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xffe03fe0cffc07c7 0xfffc07fc19ff80f8

def z823 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xbfe03fe00ffe07ff 0xf7fc07fc01ffc0ff

def z824 : W := mkw 0x25e0bee00b7c5786 0x04bc17dc016f8af0 0xafe03fe00ffc7fc6 0xf5fc07fc01ff8ff8

def z825 : W := mkw 0x25e03ae00b6c0586 0x04bc075c016d80b0 0x0fc023800fcc01c0 0x21f8047001f98038

def z826 : W := mkw 0x0001010880000000 0x0000202110000000 0xf0dbbffff0000003 0xbe1b77fffe000000

def z827 : W := mkw 0x0801058cc01022ed 0x410020b19802045d 0xf0dba79cc03267ff 0xbe1b74f398064cff

def z828 : W := mkw 0x25e03ee10b7c8796 0x04bc07dc216f90f2 0xafe43fe30ffd87c6 0xf5fc87fc61ffb0f8

def z829 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0x0fc023800ffc01c4 0x21f8047001ff8038

def z830 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0x08dba39c0c0007f8 0x211b7473818000ff

def z831 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0xefffe7800ffff807 0xfdfffcf001ffff00

def z832 : W := mkw 0x00000c215254af1a 0x200001842a4a95e3 0xf8245c63ffffffff 0xdf048b8c7fffffff

def z833 : W := mkw 0x17b67a5323c99510 0x82f6cf4a647932a2 0x0724586333cd9800 0x40e48b0c6679b300

def z834 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0x8fc03b800dc001c2 0x71f8077001b80038

def z835 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0xdf1c381f0ff3e7ff 0xfbe38703e1fe7cff

def z836 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xafe47fe00ffd9fc6 0xf5fc8ffc01ffb3f8

def z837 : W := mkw 0x121c081706c38571 0x82438102e0d870ae 0x9f1c001f0fc387fd 0x73e38003e1f870ff

def z838 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0xff245c63fffffe3f 0xffe48b8c7fffffc7

def z839 : W := mkw 0x25e03ee05b7c2f8e 0x24bc07dc0b6f85f1 0xafe03fe00ffc7fc6 0xf5fc07fc01ff8ff8

def z840 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xbfe03fe3fffc07c6 0xf7fc07fc7fff80f8

def z841 : W := mkw 0x0a1fc50cc4937269 0x4143f8a198926e4d 0xf03fc41cc23ffe3f 0xde07f8839847ffc7

def z842 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0xffffc400cffff807 0xfffff88019ffff00

def z843 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0xf7fffffff003f803 0xfefffffffe007f00

def z844 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0x3fc03fe3fdc007fa 0x27f807fc7fb800ff

def z845 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xbfe43fe30ffc07c7 0xf7fc87fc61ff80f8

def z846 : W := mkw 0x25e036e0097c0386 0x04bc06dc012f8070 0xafe027e00ffc01c4 0xf5fc04fc01ff8038

def z847 : W := mkw 0x07b7735aa1891000 0x00f6ee6b54312200 0xf7fffffff1c00003 0xfefffffffe380000

def z848 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0x77fbfffff0000002 0xaeff7ffffe000000

def z849 : W := mkw 0x06b7410880000000 0x00d6e82110000000 0xf7fffffff0000003 0xfefffffffe000000

def z850 : W := mkw 0x21003ee002540786 0x042007dc004a80f0 0xaf203fe00ffc07c6 0xf5e407fc01ff80f8

def z851 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0x0fc023800dc007c0 0x21f8047001b800f8

def z852 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0xffe07fe3fffc7ffe 0xfffc0ffc7fff8fff

def z853 : W := mkw 0x0809058cc41222ed 0x410120b19882445d 0xf8dba79ccc0207ff 0xbf1b74f3998040ff

def z854 : W := mkw 0x27b7735aa1480100 0x04f6ee6b54290020 0xf7fffffff1c00003 0xfefffffffe380000

def z855 : W := mkw 0x25e036c009780384 0x04bc06d8012f0070 0x0fc023800df007c4 0x21f8047001be00f8

def z856 : W := mkw 0x0149b35aadab5000 0x0029366b55b56a00 0x38003ffffffff806 0x070007ffffffff00

def z857 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xf8fffffffe3fffff 0xff1fffffffc7ffff

def z858 : W := mkw 0x131c383716c78d73 0xa2638706e2d8f1ae 0x9f1c381f0fcf9fff 0x73e38703e1f9f3ff

def z859 : W := mkw 0x0849858cccb362ed 0x410930b199966c5d 0xf8dba79ccff3e7ff 0xbf1b74f399fe7cff

def z860 : W := mkw 0x1a1d811e84834061 0xc343b023d090680c 0x001b801c00000000 0x0003700380000000

def z861 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0x2fe027e00dc001c0 0xa5fc04fc01b80038

def z862 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xafc03fe00fc007c6 0x75f807fc01f800f8

def z863 : W := mkw 0x25e2fee05b7c7f8e 0x24bc5fdc0b6f8ff1 0xefe3ffe0fffc7fc6 0xfdfc7ffc1fff8ff8

def z864 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0xffe47fe3fffc07ff 0xfffc8ffc7fff80ff

def z865 : W := mkw 0x0008000404020061 0x000100008080400c 0x9f18201c0fc207ff 0x73e3040381f840ff

def z866 : W := mkw 0x0849858cccb372ed 0x410930b199966e5d 0xf8dba79ccc33ffff 0xbf1b74f399867fff

def z867 : W := mkw 0x25e03ac00b680584 0x04bc0758016d00b0 0x8fe03b800ffc07c6 0xf1fc077001ff80f8

def z868 : W := mkw 0x05a1334880000000 0x00b4266910000000 0xf7fffffff0000003 0xfefffffffe000000

def z869 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0xf7fffffff002063f 0xfefffffffe0040c7

def z870 : W := mkw 0x04a34348a0000000 0x0094686914000000 0xf0fffffff0000003 0xfe1ffffffe000000

def z871 : W := mkw 0x0a1fc10c84835061 0x4143f82190906a0c 0x401fc01c0003f801 0x0803f80380007f00

def z872 : W := mkw 0x0849818ccc2260ed 0x4109303199844c1d 0xd8dba39ccc0267ff 0x3b1b747399804cff

def z873 : W := mkw 0x1108381706c38571 0x82210702e0d870ae 0x9f00381f0fc387fe 0x73e00703e1f870ff

def z874 : W := mkw 0x06fecc215fbffe1a 0x20dfd9842bf7ffc3 0x3fdb9c63fdc0063a 0x27fb738c7fb800c7

def z875 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0x8fe023800dc001c0 0xf1fc047001b80038

def z876 : W := mkw 0x0100380402400561 0x00200700804800ac 0x9f00381c0fc007fe 0x73e0070381f800ff

def z877 : W := mkw 0x131c383716c78d73 0xa2638706e2d8f1ae 0xff3c7c7fffcf9fff 0xffe78f8ffff9f3ff

def z878 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xf8fbbffccc3267ff 0xff1f77ff99864cff

def z879 : W := mkw 0x25e03ee04b7c278e 0x04bc07dc096f84f1 0xffe47fe3fffe67ff 0xfffc8ffc7fffccff

def z880 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x1f1c381f0dc387fb 0x23e38703e1b870ff

def z881 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x8ffb80000ffff804 0xf1ff700001ffff00

def z882 : W := mkw 0x25e2f2c009685184 0x04bc5e58012d0a30 0x0fc3a3800dc001c0 0x21f8747001b80038

def z883 : W := mkw 0x0040048008300284 0x0008009001060050 0xafc027800ff007c6 0xf5f804f001fe00f8

def z884 : W := mkw 0x04e004804938228c 0x009c009009270451 0xffe46780cfffffff 0xfffc8cf019ffffff

def z885 : W := mkw 0x000000015000a818 0x200000002a001503 0xf0245c63f23ff83f 0xde048b8c7e47ff07

def z886 : W := mkw 0x004884840c3242e5 0x000910908186485c 0xf8dba79c0c3267ff 0xbf1b74f381864cff

def z887 : W := mkw 0x0809810cc4026069 0x4101302198804c0d 0xf8dba79ccc0267ff 0xbf1b74f399804cff

def z888 : W := mkw 0x25e03ee11b7c8f96 0x24bc07dc236f91f2 0xafe03fe00ffd9fc6 0xf5fc07fc01ffb3f8

def z889 : W := mkw 0x24e006e0093c0286 0x049c00dc01278050 0xafe027e00ffc07c6 0xf5fc04fc01ff80f8

def z890 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x9f1c381f0dc007fb 0x73e38703e1b800ff

def z891 : W := mkw 0x06be400004830000 0x00d7c80000906000 0xcfffc0000ffff805 0xf9fff80001ffff00

def z892 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xafe03fe00fffffc6 0xf5fc07fc01fffff8

def z893 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xf8fbe79ccc3e7fff 0xbf1f7cf39987cfff

def z894 : W := mkw 0x0849858ccd3a72ed 0x410930b199a74e5d 0xf8dba79ccc3e7fff 0xbf1b74f39987cfff

def z895 : W := mkw 0x05a1335aa0000000 0x00b4266b54000000 0xf7fbbffff0000003 0xfeff77fffe000000

def z896 : W := mkw 0x084985acdc366aef 0x610930b59b86cd5d 0xf8ffe7fcfe3fffff 0xff1ffcff9fc7ffff

def z897 : W := mkw 0x084985acdc366aef 0x610930b59b86cd5d 0xf8dba7fcfc3267ff 0xbf1b74ff9f864cff

def z898 : W := mkw 0x131ef81706c3d571 0x8263df02e0d87aae 0xdf3ff81f0fffffff 0xfbe7ff03e1ffffff

def z899 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0x37fffffff0000002 0x66fffffffe000000

def z900 : W := mkw 0x121f491fa6838471 0x8243e923f4d0708e 0xf03fdc7ff203863f 0xde07fb8ffe4070c7

def z901 : W := mkw 0x07b7735aa0811000 0x00f6ee6b54102200 0xf7fffffff0019803 0xfefffffffe003300

def z902 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x8f18381c0fc387fe 0x71e3070381f870ff

def z903 : W := mkw 0x0849818c8c2240e5 0x410930319184481c 0xf8dba79ccc0207ff 0xbf1b74f3998040ff

def z904 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x4fe7c0000ffff804 0xc9fcf80001ffff00

def z905 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xafc03fe00df007c6 0xb5f807fc01be00f8

def z906 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0x0fc023800ffffffc 0x21f8047001ffffff

def z907 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0x78dba79ccc3067fa 0xaf1b74f399860cff

def z908 : W := mkw 0x1314381702c18571 0x82628702e05830ae 0x9f04381f0fc187fe 0x73e08703e1f830ff

def z909 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0xf03c7c7ff23ffe3f 0xfe078f8ffe47ffc7

def z910 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xafe43fe00fff87c7 0xf5fc87fc01fff0f8

def z911 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0xefe07fe0fffffffe 0xfdfc0ffc1fffffff

def z912 : W := mkw 0x16fec0160dab5061 0x82dfd802c1b56a0c 0xcfffc01c0ffff805 0xf9fff80381ffff00

def z913 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0xefe47fe00fffffff 0xfdfc8ffc01ffffff

def z914 : W := mkw 0x0001010c80000061 0x000020219000000c 0xf0dba79cc00007fb 0xbe1b74f3980000ff

def z915 : W := mkw 0x05e03a400b680500 0x00bc0748016d00a0 0xafe03fe00ffc07c6 0xf5fc07fc01ff80f8

def z916 : W := mkw 0x07b7735aa0810000 0x00f6ee6b54102000 0xf7fffffff3c18003 0xfefffffffe783000

def z917 : W := mkw 0x25e03ee10b7c8796 0x04bc07dc216f90f2 0xffe47fe3ffff87ff 0xfffc8ffc7ffff0ff

def z918 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0xffe03fe3fffe67ff 0xfffc07fc7fffccff

def z919 : W := mkw 0x37b67a7303cd9512 0x86f6cf4e6079b2a2 0x0724586303cd9800 0x40e48b0c6079b300

def z920 : W := mkw 0x06f6c00009a95000 0x00ded80001352a00 0xc7ffc00003fdf801 0xf8fff800007fbf00

def z921 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x9f18381f0fc007fe 0x73e30703e1f800ff

def z922 : W := mkw 0x05e036c009380284 0x00bc06d801270050 0xafe03fe00ffc07c6 0xf5fc07fc01ff80f8

def z923 : W := mkw 0x131c381716c38d71 0xa2638702e2d871ae 0x9f1c781f3fc39fff 0x73e38f03e7f873ff

def z924 : W := mkw 0x25e03ee05b7c2f8e 0x24bc07dc0b6f85f1 0xffe07fe0fffe7fff 0xfffc0ffc1fffcfff

def z925 : W := mkw 0x06b6400001891000 0x00d6c80000312200 0xc7ffc00003fff805 0xf8fff800007fff00

def z926 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0xafe47fe33ffffffe 0xf5fc8ffc67ffffff

def z927 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0xefe47fe3fffdffc6 0xfdfc8ffc7fffbff8

def z928 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x9f18201c0fc387ff 0x33e3040381f870ff

def z929 : W := mkw 0x0ffff3deadab50e5 0x41fffe7bd5b56a1c 0x0fdba39c0dc001c0 0x21fb747381b80038

def z930 : W := mkw 0x131c301604c30161 0x82638602c098602c 0x9f1c381f0dc207ff 0x73e38703e1b840ff

def z931 : W := mkw 0x0849858cdc326aed 0x610930b19b864d5d 0xf8dbe79cfc327fff 0xbf1b7cf39f864fff

def z932 : W := mkw 0x0100380002400500 0x00200700004800a0 0xafc03f800fc007c6 0xf5f807f001f800f8

def z933 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0x2fc03fe00ffc07c6 0x25f807fc01ff80f8

def z934 : W := mkw 0x17b7735aa0c10100 0x82f6ee6b54182020 0xf7fffffff1c00003 0xfefffffffe380000

def z935 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0x70fffffff0000003 0x8e1ffffffe000000

def z936 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x4ffbc0000ffff804 0xa9ff780001ffff00

def z937 : W := mkw 0x06f6c00009a95000 0x00ded80001352a00 0xc7e7c00003fff805 0xd8fcf800007fff00

def z938 : W := mkw 0x0108380506428571 0x00210700a0c850ae 0x9f1c381f0fc387ff 0x73e38703e1f870ff

def z939 : W := mkw 0x1100381702408571 0x82200702e04810ae 0x1f00381f0dc007fa 0x23e00703e1b800ff

def z940 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x9f3c781f0fcf9fff 0x73e78f03e1f9f3ff

def z941 : W := mkw 0x06fec0040dab5061 0x00dfd80081b56a0c 0xcfffe01c0ffff9c5 0xf9fffc0381ffff38

def z942 : W := mkw 0x05a3735aa0000000 0x00b46e6b54000000 0xf0fbfffff0000003 0xbe1f7ffffe000000

def z943 : W := mkw 0x0315335aa0000000 0x0062a66b54000000 0xf7dfbffff0000003 0xfefbf7fffe000000

def z944 : W := mkw 0x0108300404420161 0x002106008088402c 0x9f18201c0dc207ff 0x33e3040381b840ff

def z945 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0x0fe023800dfc01c0 0xa1fc047001bf8038

def z946 : W := mkw 0x2ce3c7e8e93c628e 0x459c78fd1d278c51 0x60e3c7e0f03c6000 0x8c1c78fc1e078c00

def z947 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0x8fc03b800ffc07c6 0x71f8077001ff80f8

def z948 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0xcfdb80000ffff805 0xb9fb700001ffff00

def z949 : W := mkw 0x25e036c009780384 0x04bc06d8012f0070 0xafe027800ffc07c6 0xf5fc04f001ff80f8

def z950 : W := mkw 0x0ce3c5a8d93c7a8e 0x619c78b51b278f51 0x60e3c7e0f03c7800 0x8c1c78fc1e078f00

def z951 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0x77dffffff0000003 0x2efbfffffe000000

def z952 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xf8fbe7fcfc3267ff 0xbf1f7cff9f864cff

def z953 : W := mkw 0x25e03ee14b7ca79e 0x04bc07dc296f94f3 0xffe43fe3cfffe7ff 0xfffc87fc79fffcff

def z954 : W := mkw 0x17b67a7332c58d12 0xa2f6cf4e6658b1a2 0x0724586333cd9800 0x40e48b0c6679b300

def z955 : W := mkw 0x0140348008700384 0x00280690010e0070 0xafc027800df007c6 0xb5f804f001be00f8

def z956 : W := mkw 0x00410588c830228c 0x000820b119060451 0xf8dba79ccc3267ff 0xbf1b74f399864cff

def z957 : W := mkw 0x0009050cc4122269 0x000120a19882444d 0xf8dba79ccc3267ff 0xbf1b74f399864cff

def z958 : W := mkw 0x210032c000400184 0x0420065800080030 0x0f0023800dc001c0 0x21e0047001b80038

def z959 : W := mkw 0x25e03ee04b7c278e 0x04bc07dc096f84f1 0xffe47fe0cfffffff 0xfffc8ffc19ffffff

def z960 : W := mkw 0x05e03ec00a700784 0x00bc07d8014e00f0 0xafe03fe00ff007c6 0xf5fc07fc01fe00f8

def z961 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0xffe47fe3fdc001c3 0xfffc8ffc7fb80038

def z962 : W := mkw 0x084985acdc366aef 0x610930b59b86cd5d 0xf8dba79ccc3e7fff 0xbf1b74f39987cfff

def z963 : W := mkw 0x131e781706c39571 0x8263cf02e0d872ae 0x9f1c781f0fc39fff 0x73e38f03e1f873ff

def z964 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0xbfe47fe3fffd9ffe 0xf7fc8ffc7fffb3ff

def z965 : W := mkw 0x1a1fc11fe483e079 0xc343f823fc907c0f 0x501fc01ff003e039 0x0a03f803fe007c07

def z966 : W := mkw 0x25e27ee02b7c0786 0x04bc4fdc056f80f0 0xafe07fe03ffc07c6 0xf5fc0ffc07ff80f8

def z967 : W := mkw 0x06fec0122dab5000 0x00dfd80245b56a00 0xcfffc0033ffff805 0xf9fff80067ffff00

def z968 : W := mkw 0x0049058c8c3202e5 0x000920b19186405c 0xf8dba79ccc3207ff 0xbf1b74f3998640ff

def z969 : W := mkw 0x131c383716c78d73 0xa2638706e2d8f1ae 0xdf3c787f3fffffff 0xfbe78f0fe7ffffff

def z970 : W := mkw 0x21403ca00b7c0786 0x04280794016f80f0 0xafc03f800ffc07c6 0xf5f807f001ff80f8

def z971 : W := mkw 0x06fec2400dab5000 0x00dfd84801b56a00 0xefffc7e00ffff805 0xfdfff8fc01ffff00

def z972 : W := mkw 0x0841058cc83022ed 0x410820b19906045d 0xf8dba79ccc3007ff 0xbf1b74f3998600ff

def z973 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xf8dbbffffc3267ff 0xbf1b77ffff864cff

def z974 : W := mkw 0x25e03ae00b6c0586 0x04bc075c016d80b0 0x0fc03be00dc001c0 0x21f8077c01b80038

def z975 : W := mkw 0x0000080102008410 0x0000010020401082 0xf0245c63f23ffe3f 0xde048b8c7e47ffc7

def z976 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x9f3c381f0fff87ff 0xf3e78703e1fff0ff

def z977 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xb8dba79ccc3007fe 0xb71b74f3998600ff

def z978 : W := mkw 0x1a1d811ec4836069 0xc343b023d8906c0d 0x501b801cc0026039 0x0a03700398004c07

def z979 : W := mkw 0x131c3a5706c38571 0x8263874ae0d870ae 0xbf1c3fff0fc387ff 0x77e387ffe1f870ff

def z980 : W := mkw 0x0317735aa0000000 0x0062ee6b54000000 0xf0dffffff0000003 0xbe1bfffffe000000

def z981 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0xf0e47fe3f23ffe3f 0xfe1c8ffc7e47ffc7

def z982 : W := mkw 0x04eac0000dab5000 0x009d580001b56a00 0xcfe3c0000ffff804 0xf9fc780001ffff00

def z983 : W := mkw 0x084985accc3662ef 0x410930b59986cc5d 0xf8fba7fccc3e67ff 0xbf1f74ff9987ccff

def z984 : W := mkw 0x021ec00004835000 0x0043d80000906a00 0xcf3fc0000ffff805 0xf9e7f80001ffff00

def z985 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0xf7fffffff23c0007 0xfefffffffe478000

def z986 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0xcfffd8633ffff805 0xf9fffb0c67ffff00

def z987 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0xafc027800dc001c2 0xb5f804f001b80038

def z988 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0x58dba39ccc3267fd 0x2b1b747399864cff

def z989 : W := mkw 0x0a1fc10c84835061 0x4143f82190906a0c 0x001b801c00000000 0x0003700380000000

def z990 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0xff3c7c7fffffffff 0xffe78f8fffffffff

def z991 : W := mkw 0x25e27ee00b7c0786 0x04bc4fdc016f80f0 0xefe3ffe00ffc07c6 0xfdfc7ffc01ff80f8

def z992 : W := mkw 0x25e03ac00b680584 0x04bc0758016d00b0 0x0fc023800fc007c4 0x21f8047001f800f8

def z993 : W := mkw 0x131ef81706c3d571 0x8263df02e0d87aae 0x9f1fb81f0fc387ff 0x73e3f703e1f870ff

def z994 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0x2fe01fe00ffc07c4 0xc5fc03fc01ff80f8

def z995 : W := mkw 0x0314381302408510 0x00628702604810a2 0x9f1c381f0fc387ff 0x73e38703e1f870ff

def z996 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x4fffc0000ffdf800 0xe9fff80001ffbf00

def z997 : W := mkw 0x25e03ee05b7c2f8e 0x24bc07dc0b6f85f1 0xefe47fe0ffffffc7 0xfdfc8ffc1ffffff8

def z998 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x9f18381f0dc207ff 0x33e30703e1b840ff

def z999 : W := mkw 0x131c383716c78d73 0xa2638706e2d8f1ae 0x9f1c387f3fc387ff 0x73e3870fe7f870ff

def z1000 : W := mkw 0x11013f7ff254af7b 0xa22027effe4a95ef 0x30003ffff00007fa 0x060007fffe0000ff

def z1001 : W := mkw 0x25e036c04978238c 0x04bc06d8092f0471 0xffc02780cdf267ff 0xbff804f019be4cff

def z1002 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0xdfdfb81f0fc387ff 0xfbfbf703e1f870ff

def z1003 : W := mkw 0x25a03ee002540786 0x04b407dc004a80f0 0xafe03fe00fc007c6 0xf5fc07fc01f800f8

def z1004 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0xf8247c63fe3fffff 0xff048f8c7fc7ffff

def z1005 : W := mkw 0x08488ca55e36eeff 0x61091194abc6dddf 0x080000000c3267fc 0x0100000001864cff

def z1006 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0xdf3c781f0fc387ff 0xfbe78f03e1f870ff

def z1007 : W := mkw 0x0849858ccd3a62ed 0x410930b199a74c5d 0xf8dba79ccffe67ff 0xbf1b74f399ffccff

def z1008 : W := mkw 0x0849818c8c2240e5 0x410930319184481c 0x08dba39c0c0207fc 0x211b7473818040ff

def z1009 : W := mkw 0x01403ca15a74af9e 0x202807942b4e95f3 0xffe47fe3ffffffff 0xfffc8ffc7fffffff

def z1010 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xb8dba79ccc0207ff 0x371b74f3998040ff

def z1011 : W := mkw 0x031c380406c30561 0x0063870080d860ac 0x9f1c381c0fc387ff 0x73e3870381f870ff

def z1012 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x0fffc0000ffff804 0x61fff80001ffff00

def z1013 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0x0fe023800fcc01c0 0x61fc047001f98038

def z1014 : W := mkw 0x1108380506c38571 0x82210700a0d870ae 0x9f18381c0fc387ff 0x73e3070381f870ff

def z1015 : W := mkw 0x01403ca00a740786 0x00280794014e80f0 0xafe03fe00ffc07c6 0xf5fc07fc01ff80f8

def z1016 : W := mkw 0x131e781726c38571 0x8263cf02e4d870ae 0x9f1c781f3fc387ff 0x73e38f03e7f870ff

def z1017 : W := mkw 0x1314381702408571 0x82628702e04810ae 0x9f1c381f0fc007ff 0x73e38703e1f800ff

def z1018 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0xcfe463800ffff9c5 0xf9fc8c7001ffff38

def z1019 : W := mkw 0x131c383706c78573 0x82638706e0d8f0ae 0x9f3c387f0fcf87ff 0x73e7870fe1f9f0ff

def z1020 : W := mkw 0x0a1fc10cc4837069 0x4143f82198906e0d 0x501b801cc0026039 0x0a03700398004c07

def z1021 : W := mkw 0x131e781706c38571 0x8263cf02e0d870ae 0xdf1ff81f0fc387ff 0x7be3ff03e1f870ff

def z1022 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x8fdf80000ffff805 0x71fbf00001ffff00

def z1023 : W := mkw 0x07b7735aa1081000 0x00f6ee6b54210200 0xf7fffffff00c1803 0xfefffffffe018300

def z1024 : W := mkw 0x1100381702408571 0x82200702e04810ae 0x9f04381f0fc387ff 0x73e08703e1f870ff

def z1025 : W := mkw 0x2ce187c8c938628c 0x459c30f919270c51 0x60c38780c0306000 0x8c1870f018060c00

def z1026 : W := mkw 0x25e03ee10b7c8796 0x04bc07dc216f90f2 0xffe47fe30fffffff 0xfffc8ffc61ffffff

def z1027 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0x60245c63f23ffe3c 0xcc048b8c7e47ffc7

def z1028 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0x68dba79ccc3267fc 0xad1b74f399864cff

def z1029 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x47ffc00003fff801 0xc8fff800007fff00

def z1030 : W := mkw 0x014038800a600584 0x00280710014c00b0 0x8fc03b800fc007c6 0x71f8077001f800f8

def z1031 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0x70245c63f03ffe3b 0x8e048b8c7e07ffc7

def z1032 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0xbfe43fe3ffff87ff 0xf7fc87fc7ffff0ff

def z1033 : W := mkw 0x0140308008600184 0x00280610010c0030 0x0fc023800dc001c0 0x21f8047001b80038

def z1034 : W := mkw 0x21403ee00a740786 0x042807dc014e80f0 0xafc03fe00ff007c6 0xf5f807fc01fe00f8

def z1035 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0xfffffffffc0007c7 0xffffffffff8000f8

def z1036 : W := mkw 0x25e2fee00b7c5786 0x04bc5fdc016f8af0 0xefe7ffe00fffffc7 0xfdfcfffc01fffff8

def z1037 : W := mkw 0x04e00ca15b3cae9e 0x209c01942b6795d3 0xffe47fe3ffffffff 0xfffc8ffc7fffffff

def z1038 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0x2fe03fe00dfc07c2 0xa5fc07fc01bf80f8

def z1039 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0xb7fbbffff0000002 0xf6ff77fffe000000

def z1040 : W := mkw 0x131c301704c38171 0x82638602e098702e 0x9f1c201f0dc387ff 0x33e38403e1b870ff

def z1041 : W := mkw 0x121c080506c38571 0x82438100a0d870ae 0x9f1c201c0fc387ff 0x73e3840381f870ff

def z1042 : W := mkw 0x07b7735aa1080000 0x00f6ee6b54210000 0xf7fffffff3cc0003 0xfefffffffe798000

def z1043 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0xf7fffffff03c7803 0xfefffffffe078f00

def z1044 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0x70245c63f23ff839 0xce048b8c7e47ff07

def z1045 : W := mkw 0x0009010c84020061 0x000120219080400c 0x98dba39c0c0207ff 0x331b7473818040ff

def z1046 : W := mkw 0x25a03a60034c0502 0x04b4074c006980a0 0xafe03fe00fcc07c6 0xf5fc07fc01f980f8

def z1047 : W := mkw 0x0217411aa0000000 0x0042e82354000000 0xf0fffffff0000003 0xfe1ffffffe000000

def z1048 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x1f1c181f0fc387fd 0x43e38303e1f870ff

def z1049 : W := mkw 0x21003ee15254af9e 0x242007dc2a4a95f3 0xbf043fe3ffc387ff 0x77e087fc7ff870ff

def z1050 : W := mkw 0x06fec0040dab5061 0x00dfd80081b56a0c 0xcfffc0000ffffffd 0xf9fff80001ffffff

def z1051 : W := mkw 0x25e03ec00b780784 0x04bc07d8016f00f0 0xafc03f800ff007c6 0xf5f807f001fe00f8

def z1052 : W := mkw 0x24e00ca00b7c0786 0x049c0194016f80f0 0xafe027800ffc07c6 0xf5fc04f001ff80f8

def z1053 : W := mkw 0x131c301604c30161 0x82638602c098602c 0x1f18201c0dc007fa 0x23e3040381b800ff

def z1054 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0xbfdc3f9f0fc387ff 0xf7fb87f3e1f870ff

def z1055 : W := mkw 0x25e036e0097c0386 0x04bc06dc012f8070 0x2fc027e00dc001c0 0x25f804fc01b80038

def z1056 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0x78dba79ccc0267fb 0x2f1b74f399804cff

def z1057 : W := mkw 0x0801058cc01022ed 0x410020b19802045d 0x30dba79cc00007fa 0x261b74f3980000ff

def z1058 : W := mkw 0x21003ee002540786 0x042007dc004a80f0 0x2f003fe00dc007c2 0x25e007fc01b800f8

def z1059 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x0f18201c0dc007f8 0x21e3040381b800ff

def z1060 : W := mkw 0x25e03ee05b7c2f8e 0x24bc07dc0b6f85f1 0xffe47fe3fffc7fc7 0xfffc8ffc7fff8ff8

def z1061 : W := mkw 0x1a1d8d1fc693e679 0xc343b1a3f8d27ccf 0xf01f9c1fc233e63f 0xde03f383f8467cc7

def z1062 : W := mkw 0x021c000404830061 0x004380008090600c 0x9f18201c0dc207ff 0x33e3040381b840ff

def z1063 : W := mkw 0x04e0008009280084 0x009c001001250010 0x0fc023800dc001c0 0x21f8047001b80038

def z1064 : W := mkw 0x000004215014aa1a 0x200000842a029543 0xf0245c63f03ff83b 0xde048b8c7e07ff07

def z1065 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xefe07fe0fffc07c6 0xfdfc0ffc1fff80f8

def z1066 : W := mkw 0x25e03ae00b6c0586 0x04bc075c016d80b0 0xafe03fe00fcc01c2 0xf5fc07fc01f98038

def z1067 : W := mkw 0x37b67a7323cd8512 0x86f6cf4e6479b0a2 0x0724586333cd8000 0x40e48b0c6679b000

def z1068 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xf8ffe79ccc3267ff 0xff1ffcf399864cff

def z1069 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xefe47fe00ffc07c7 0xfdfc8ffc01ff80f8

def z1070 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0xf7fffffff0326007 0xfefffffffe064c00

def z1071 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0xafe03fe00ffc01c6 0xf5fc07fc01ff8038

def z1072 : W := mkw 0x25e2f2c009685184 0x04bc5e58012d0a30 0x4fe3e3800dfc79c0 0xa9fc7c7001bf8f38

def z1073 : W := mkw 0x031c301604830061 0x00638602c090600c 0x9f1c381f0fc387ff 0x73e38703e1f870ff

def z1074 : W := mkw 0x06fec0040dab5061 0x00dfd80081b56a0c 0xdfffc01c0ffff83d 0xfbfff80381ffff07

def z1075 : W := mkw 0x04e0008009280084 0x009c001001250010 0x8fe023800ffc01c4 0xf1fc047001ff8038

def z1076 : W := mkw 0x25e03ee11b7c8f96 0x24bc07dc236f91f2 0xefe47fe33fffffc7 0xfdfc8ffc67fffff8

def z1077 : W := mkw 0x25e03ac00b680584 0x04bc0758016d00b0 0x0fc03b800dc007c2 0x21f8077001b800f8

def z1078 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xbff83ffc0ffc07c7 0xf7ff07ff81ff80f8

def z1079 : W := mkw 0x0000040040102208 0x0000008008020441 0xf0245c63f23ffe3f 0xde048b8c7e47ffc7

def z1080 : W := mkw 0x04e880000d2a4000 0x009d100001a54800 0xcfffc0000ffff805 0xf9fff80001ffff00

def z1081 : W := mkw 0x0049810c8c224061 0x000930219184480c 0xf8dba79ccc3267ff 0xbf1b74f399864cff

def z1082 : W := mkw 0x04e880000dab5000 0x009d100001b56a00 0xcffb80000ffff805 0xf9ff700001ffff00

def z1083 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0x2fe027e00ffc07c4 0xa5fc04fc01ff80f8

def z1084 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0x4fdfc0000ffff805 0x29fbf80001ffff00

def z1085 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xafe03fe00dc007c2 0xf5fc07fc01b800f8

def z1086 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x9f3c787f3fc387ff 0x73e78f0fe7f870ff

def z1087 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xeffbbfe00ffc07c7 0xfdff77fc01ff80f8

def z1088 : W := mkw 0x25e036c009780384 0x04bc06d8012f0070 0xafe03fe00df007c6 0xf5fc07fc01be00f8

def z1089 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xffdba79ccff267ff 0xfffb74f399fe4cff

def z1090 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0x8fe023800ffc07c4 0xf1fc047001ff80f8

def z1091 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xf8dfbf9fcc3267ff 0xff1bf7f3f9864cff

def z1092 : W := mkw 0x24e347e8f93c2a8e 0x249c68fd1f278551 0x60e3c7e0f03c7800 0x8c1c78fc1e078f00

def z1093 : W := mkw 0x06fec0120dab5000 0x00dfd80241b56a00 0xdfffc01f0ffff805 0xfbfff803e1ffff00

def z1094 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0xf7fffffff20d9803 0xfefffffffe41b300

def z1095 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0xf7dbbffff0000003 0xbefb77fffe000000

def z1096 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0xafe03fe00ffc07fe 0xf5fc07fc01ff80ff

def z1097 : W := mkw 0x20000ca15254af9e 0x240001942a4a95f3 0xf0245c63f23fffff 0xde048b8c7e47ffff

def z1098 : W := mkw 0x1108381706428571 0x82210702e0c850ae 0x9f18381f0fc207ff 0x73e30703e1f840ff

def z1099 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x9f1c381f0fffffff 0x73e38703e1ffffff

def z1100 : W := mkw 0x0315311a80000000 0x0062a62350000000 0xf7fffffff0000003 0xfefffffffe000000

def z1101 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0x70dba79cc03267fb 0x8e1b74f398064cff

def z1102 : W := mkw 0x19013dbfd254afff 0xe32027b7fa4a95ff 0x30003ffff00007fa 0x060007fffe0000ff

def z1103 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x1f04381f0fc387fe 0x43e08703e1f870ff

def z1104 : W := mkw 0x131c301604c30161 0x82638602c098602c 0x0f18201c0dc207fc 0x21e3040381b840ff

def z1105 : W := mkw 0x04e0048009380284 0x009c009001270050 0xafc027800df007c6 0xb5f804f001be00f8

def z1106 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0xdf1c781fffc387ff 0x7be38f03fff870ff

def z1107 : W := mkw 0x25e03ee04b7c278e 0x04bc07dc096f84f1 0xafe03fe00ffe67fe 0xf5fc07fc01ffccff

def z1108 : W := mkw 0x25e03ee04b7c278e 0x04bc07dc096f84f1 0xefe03fe0cffc67c6 0xfdfc07fc19ff8cf8

def z1109 : W := mkw 0x18488ca55ef7efff 0xe3091194abdefdff 0x080000000ffffffc 0x0100000001ffffff

def z1110 : W := mkw 0x01003c8002500784 0x00200790004a00f0 0xaf003f800fc007c6 0x75e007f001f800f8

def z1111 : W := mkw 0x25e03ee11b7c8f96 0x24bc07dc236f91f2 0xffe47fe3fffd9fc7 0xfffc8ffc7fffb3f8

def z1112 : W := mkw 0x25e03ee11b7c8f96 0x24bc07dc236f91f2 0xbfe47fe33fff9fff 0xf7fc8ffc67fff3ff

def z1113 : W := mkw 0x025c80000ca34000 0x004b900001946800 0xcfffc0000ffff805 0xf9fff80001ffff00

def z1114 : W := mkw 0x0a1fcd2dd697fe7b 0x6143f9a5bad2ffcf 0xf03fdc7ff23ffe3f 0xde07fb8ffe47ffc7

def z1115 : W := mkw 0x021c080506838471 0x00438100a0d0708e 0x9f1c381f0fc387ff 0x73e38703e1f870ff

def z1116 : W := mkw 0x01403c814a70a79c 0x00280790294e14f3 0xffc43f83cff3e7ff 0xfff887f079fe7cff

def z1117 : W := mkw 0x2ce107e8c93c228e 0x459c20fd19278451 0x20e007e0c03c0000 0x841c00fc18078000

def z1118 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0x2fe03fe00fcc07c2 0x65fc07fc01f980f8

def z1119 : W := mkw 0x0849818c8c2240e5 0x410930319184481c 0xd8dba39c0c3267ff 0xbb1b747381864cff

def z1120 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0xffe47fe3ffffffc7 0xfffc8ffc7ffffff8

def z1121 : W := mkw 0x0101335aa0000000 0x0020266b54000000 0xf0fffffff0000003 0xfe1ffffffe000000

def z1122 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xf8dfe79ccc33ffff 0xbf1bfcf399867fff

def z1123 : W := mkw 0x000008215204ac1a 0x200001042a409583 0xd0245863f23ff83d 0xda048b0c7e47ff07

def z1124 : W := mkw 0x25e03ac00b680584 0x04bc0758016d00b0 0x0fc03b800fc001c0 0x61f8077001f80038

def z1125 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0x1f1c381f0fc187fa 0x63e38703e1f830ff

def z1126 : W := mkw 0x25e03ef20b7c0786 0x04bc07de416f80f0 0xbfe03fff0ffc07c6 0xf7fc07ffe1ff80f8

def z1127 : W := mkw 0x331c3a7706c78573 0x8663874ee0d8f0ae 0x9f1c387f0fc387ff 0x73e3870fe1f870ff

def z1128 : W := mkw 0x0a1fc10dd483f879 0x6143f821ba907f0f 0x501fc01ff003f839 0x0a03f803fe007f07

def z1129 : W := mkw 0x025c80000dab5000 0x004b900001b56a00 0xcfdf80000ffff805 0xf9fbf00001ffff00

def z1130 : W := mkw 0x25a03ee0035c0786 0x04b407dc006b80f0 0xaf203fe00fcc07c6 0x75e407fc01f980f8

def z1131 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0xffe03fe0cfffffff 0xfffc07fc19ffffff

def z1132 : W := mkw 0x25e03ae00b6c0586 0x04bc075c016d80b0 0x8fe03be00fcc07c6 0x71fc077c01f980f8

def z1133 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0xdf1c781f0fc3ffff 0x7be38f03e1f87fff

def z1134 : W := mkw 0x25e0bee00b7c4786 0x04bc17dc016f88f0 0xefe3bfe00ffc67c6 0xfdfc77fc01ff8cf8

def z1135 : W := mkw 0x17b67a5322408510 0x82f6cf4a644810a2 0x0724586330000000 0x40e48b0c66000000

def z1136 : W := mkw 0x0849858ccdbb72ed 0x410930b199b76e5d 0xf8ffe79ccfffffff 0xff1ffcf399ffffff

def z1137 : W := mkw 0x0849858ccdbb72ed 0x410930b199b76e5d 0xf8dba79ccdf267ff 0xbf1b74f399be4cff

def z1138 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0xdfffd8030ffff807 0xfbfffb0061ffff00

def z1139 : W := mkw 0x06fec2402dab5000 0x00dfd84805b56a00 0xcfffc0603ffff805 0xf9fff80c07ffff00

def z1140 : W := mkw 0x25e036e0097c0386 0x04bc06dc012f8070 0xafe027e00dfc07c6 0xb5fc04fc01bf80f8

def z1141 : W := mkw 0x2de0bee04b7c678e 0x45bc17dc096f8cf1 0xafe03fe00ffc67c6 0xf5fc07fc01ff8cf8

def z1142 : W := mkw 0x08488ca55fbffeff 0x61091194abf7ffdf 0x080000000ffffffc 0x0100000001ffffff

def z1143 : W := mkw 0x25e03ee04b7c278e 0x04bc07dc096f84f1 0xbfe03fe0cffc07fe 0xf7fc07fc19ff80ff

def z1144 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0xdfffc003fffff805 0xfbfff8007fffff00

def z1145 : W := mkw 0x07b7735aa0000000 0x00f6ee6b54000000 0x67fffffff0000000 0xecfffffffe000000

def z1146 : W := mkw 0x25e036e0597c2b8e 0x24bc06dc0b2f8571 0x6fe067e0fdfc79c0 0xadfc0cfc1fbf8f38

def z1147 : W := mkw 0x25e036e0097c0386 0x04bc06dc012f8070 0x0fc023800dfc01c0 0x21f8047001bf8038

def z1148 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0xbfe03fe3fffffffe 0xf7fc07fc7fffffff

def z1149 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0x8fc023800df001c4 0xb1f8047001be0038

def z1150 : W := mkw 0x0efec0840dab50e5 0x41dfd81081b56a1c 0xcfffc0000ffff9c5 0xf9fff80001ffff38

def z1151 : W := mkw 0x25e03ee00b7c0786 0x04bc07dc016f80f0 0x2f203fe00ffc07c6 0x45e407fc01ff80f8

def z1152 : W := mkw 0x25e03ee15b7caf9e 0x24bc07dc2b6f95f3 0xbfe43fe30fffffff 0xf7fc87fc61ffffff

def z1153 : W := mkw 0x0849858ccc3262ed 0x410930b199864c5d 0xf8fba79cce3e67ff 0xff1f74f399c7ccff

def z1154 : W := mkw 0x05e03c800b780784 0x00bc0790016f00f0 0xafe03f800ffc07c6 0xf5fc07f001ff80f8

def z1155 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0xefffdc600ffff807 0xfdfffb8c01ffff00

def z1156 : W := mkw 0x131c381706c38571 0x82638702e0d870ae 0xbf1c3c7fffc387ff 0x77e3878ffff870ff

def z1157 : W := mkw 0x06fec0000dab5000 0x00dfd80001b56a00 0xefffc460fffff805 0xfdfff88c1fffff00

def z1158 : W := mkw 0x25e03ee10b7c8796 0x04bc07dc216f90f2 0xafe03fe00fff87fe 0xf5fc07fc01fff0ff

def z1159 : W := mkw 0x25e036c009780384 0x04bc06d8012f0070 0x2fc027800dc007c2 0x25f804f001b800f8

def z1160 : W := mkw 0x121f411ea4830061 0x8243e823d490600c 0x001b801c00000000 0x0003700380000000

def z1161 : W := mkw 0x21403ee00b7c0786 0x042807dc016f80f0 0xaf003fe00ffc07c6 0x75e007fc01ff80f8

def z1162 : W := mkw 0x17fff35eadeb5161 0x82fffe6bd5bd6a2c 0x0fdba39c0dc001c0 0x21fb747381b80038

def z1163 : W := mkw 0x0809858cc41262ed 0x410130b198824c5d 0xf0dba79cc00267fb 0xbe1b74f398004cff

def z1164 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0x0fe03be00dc001c0 0x61fc077c01b80038

def z1165 : W := mkw 0x1a1d811f8483c071 0xc343b023f090780e 0x101f801f00038039 0x0203f003e0007007

def z1166 : W := mkw 0x131cb81706c3d571 0x82639702e0d87aae 0x9f1c381f0fc3ffff 0x73e38703e1f87fff

def z1167 : W := mkw 0x25e2fee15b7cff9e 0x24bc5fdc2b6f9ff3 0xffe7ffe3ffffffff 0xfffcfffc7fffffff

def z1168 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0x30245c63f23ffe3e 0x46048b8c7e47ffc7

def z1169 : W := mkw 0x04e00ca00b3c0686 0x009c0194016780d0 0xafe03fe00ffc07c6 0xf5fc07fc01ff80f8

def z1170 : W := mkw 0x00000c215214ae1a 0x200001842a4295c3 0xf0ffdc63f23ffe3f 0xfe1ffb8c7e47ffc7

def z1171 : W := mkw 0x25e032c009680184 0x04bc0658012d0030 0x8fc023800dc007c6 0x31f8047001b800f8

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z6,z1,z2,z3,z4,z7]),(0,[z0,z1,z8,z3,z9,z4,z7]),(0,[z0,z10,z1,z2,z3,z4,z11]),(0,[z0,z12,z1,z2,z3,z4,z7]),(0,[z0,z13,z1,z2,z3,z4,z7])],[(0,[z0,z1,z14,z2,z3,z4,z7]),(0,[z0,z15,z1,z2,z3,z4,z11]),(0,[z16,z0,z1,z2,z3,z4,z7]),(0,[z0,z17,z18,z1,z3,z4,z7]),(0,[z0,z18,z1,z2,z3,z4,z7]),(0,[z0,z19,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z20,z4,z7]),(0,[z0,z1,z2,z3,z21,z4,z7]),(1,[z0,z1,z2,z3,z4,z22]),(0,[z0,z1,z2,z23,z3,z4,z11]),(0,[z0,z15,z1,z2,z23,z4,z7]),(0,[z0,z1,z2,z24,z3,z4,z11]),(0,[z0,z1,z2,z25,z3,z4,z7]),(0,[z0,z26,z1,z2,z3,z27,z4]),(0,[z0,z1,z2,z3,z4,z28,z7])],[(0,[z0,z1,z2,z24,z23,z4,z7]),(0,[z29,z0,z1,z2,z3,z4,z7])],[(0,[z30,z0,z1,z2,z31,z4,z7]),(0,[z32,z0,z1,z2,z3,z4,z7]),(0,[z0,z33,z26,z1,z2,z3,z4]),(1,[z0,z33,z1,z2,z3,z34])],[(0,[z0,z1,z2,z35,z3,z4,z7]),(0,[z0,z1,z36,z2,z37,z4,z7])],[(0,[z0,z1,z2,z3,z38,z4,z7]),(0,[z1,z2,z3,z39,z4,z40,z7]),(0,[z0,z41,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z42,z3,z4,z11]),(1,[z0,z43,z44,z3,z4,z7]),(0,[z0,z18,z1,z2,z3,z45,z7]),(0,[z0,z1,z46,z2,z3,z4,z7])],[(0,[z0,z1,z2,z47,z3,z4,z7]),(0,[z0,z48,z49,z1,z3,z4,z7]),(0,[z0,z1,z2,z50,z3,z4,z7]),(0,[z0,z1,z2,z51,z3,z4,z7]),(0,[z0,z33,z1,z2,z3,z4,z7])]],
   [[(0,[z52,z0,z53,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z21,z7]),(0,[z0,z1,z2,z3,z4,z7,z54]),(0,[z0,z1,z2,z3,z4,z55,z7]),(0,[z56,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z57,z3,z58,z4,z7]),(0,[z0,z59,z1,z2,z3,z4,z7])],[(1,[z0,z1,z8,z3,z4,z7]),(0,[z0,z1,z2,z3,z60,z40,z7]),(0,[z61,z0,z1,z2,z3,z4,z7])],[(1,[z1,z2,z3,z4,z11,z62]),(0,[z0,z63,z1,z2,z3,z4,z7]),(0,[z0,z64,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z65,z4,z7])],[(0,[z0,z66,z1,z2,z3,z4,z7]),(0,[z0,z1,z67,z2,z3,z4,z7]),(0,[z68,z0,z1,z2,z3,z4,z11]),(1,[z0,z69,z2,z3,z70,z7])],[(0,[z0,z1,z71,z2,z3,z4,z7]),(0,[z72,z0,z1,z2,z3,z4,z5]),(0,[z0,z73,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z74,z3,z4,z7]),(1,[z0,z1,z2,z3,z75,z7]),(0,[z0,z76,z1,z2,z3,z4,z7]),(0,[z0,z77,z1,z2,z3,z4,z7]),(0,[z78,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z79,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z80,z7])],[(0,[z0,z33,z1,z2,z3,z4,z81]),(0,[z0,z1,z2,z3,z4,z82,z7]),(0,[z0,z1,z2,z3,z83,z4,z7]),(0,[z0,z84,z1,z2,z3,z4,z7])],[(1,[z0,z1,z71,z3,z4,z7]),(1,[z78,z1,z2,z3,z40,z7]),(0,[z0,z85,z1,z2,z3,z4,z86]),(0,[z0,z1,z87,z2,z3,z4,z7])]],
   [[(1,[z0,z1,z2,z3,z4,z88]),(0,[z0,z0,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z3,z4,z89,z7]),(0,[z0,z1,z2,z3,z4,z7,z90]),(0,[z0,z1,z2,z91,z3,z37,z7]),(0,[z0,z92,z1,z2,z3,z4,z7])],[(0,[z68,z0,z1,z2,z3,z4,z7]),(0,[z0,z93,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z9,z4,z11]),(0,[z0,z1,z2,z94,z3,z4,z7]),(0,[z0,z17,z1,z2,z3,z4,z11]),(0,[z0,z95,z1,z2,z3,z4,z7])],[(0,[z68,z1,z2,z3,z9,z4,z7]),(0,[z0,z41,z1,z2,z3,z4,z96]),(0,[z0,z97,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z86,z7])],[(0,[z0,z98,z1,z2,z3,z4,z7]),(0,[z0,z99,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z100,z3,z4,z7])],[(0,[z52,z0,z1,z2,z3,z21,z7]),(0,[z0,z1,z2,z3,z101,z4,z7]),(0,[z0,z1,z2,z3,z102,z4,z7])],[(0,[z0,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z103,z7]),(0,[z0,z1,z2,z3,z4,z7,z104]),(0,[z0,z105,z1,z2,z24,z4,z7]),(0,[z0,z1,z2,z3,z4,z106,z7]),(0,[z107,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z108,z3,z4,z7]),(1,[z0,z1,z2,z31,z4,z7]),(1,[z30,z1,z2,z3,z39,z7]),(0,[z0,z1,z2,z3,z4,z109,z7]),(0,[z0,z1,z2,z3,z4,z70,z11]),(0,[z0,z1,z2,z3,z4,z110,z11]),(0,[z0,z44,z111,z1,z3,z4,z7]),(0,[z0,z112,z1,z2,z3,z4,z7]),(0,[z113,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z114,z4,z7])]],
   [[(1,[z0,z1,z2,z3,z115,z7]),(0,[z0,z1,z2,z3,z4,z7,z116]),(0,[z0,z1,z2,z117,z3,z4,z7]),(0,[z0,z1,z2,z3,z9,z4,z7]),(0,[z0,z1,z2,z118,z3,z4,z7]),(0,[z0,z111,z2,z119,z3,z4,z7]),(0,[z0,z69,z1,z2,z3,z60,z7])],[(0,[z120,z0,z1,z2,z3,z4,z7]),(0,[z72,z0,z1,z2,z3,z75,z7]),(0,[z0,z121,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z122,z4,z7]),(0,[z0,z123,z1,z2,z3,z4,z7]),(0,[z0,z124,z1,z2,z3,z4,z7]),(0,[z125,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z126,z4,z7]),(0,[z127,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z36,z2,z58,z4,z7]),(0,[z0,z128,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z129]),(0,[z0,z1,z2,z3,z80,z7,z34]),(0,[z0,z1,z2,z3,z4,z7,z130])],[(0,[z0,z1,z2,z131,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z132,z7])],[(0,[z72,z0,z1,z71,z3,z4,z7]),(1,[z133,z134,z2,z3,z4,z7]),(0,[z0,z1,z2,z135,z3,z4,z7]),(0,[z0,z99,z1,z2,z136,z4,z7]),(0,[z0,z137,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z138]),(0,[z0,z139,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z140,z7]),(0,[z0,z1,z2,z3,z4,z110,z7]),(0,[z0,z1,z2,z3,z141,z4,z7]),(0,[z0,z142,z1,z2,z3,z4,z7])],[(0,[z0,z143,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z144,z3,z4,z7]),(0,[z0,z1,z2,z57,z9,z4,z7]),(0,[z0,z1,z2,z3,z40,z70,z7]),(0,[z0,z44,z1,z2,z3,z4,z62]),(0,[z0,z1,z36,z2,z3,z4,z11]),(0,[z0,z145,z1,z2,z3,z4,z7]),(0,[z0,z146,z1,z2,z3,z4,z147]),(0,[z148,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z149]),(0,[z0,z150,z1,z2,z3,z4,z7]),(0,[z0,z41,z1,z2,z3,z60,z7]),(0,[z0,z1,z2,z3,z4,z7,z151])]],
   [[(0,[z0,z1,z2,z3,z152,z4,z7]),(0,[z0,z1,z2,z91,z3,z4,z62]),(0,[z0,z1,z2,z3,z4,z7,z153]),(0,[z154,z0,z1,z2,z3,z4,z7]),(1,[z0,z13,z1,z2,z4,z7]),(0,[z0,z1,z2,z91,z37,z4,z7]),(0,[z0,z155,z1,z2,z3,z7,z156])],[(0,[z0,z157,z1,z2,z3,z4,z7]),(0,[z30,z0,z1,z2,z3,z4,z158]),(0,[z0,z2,z24,z3,z136,z4,z7])],[(0,[z159,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z115,z4,z7]),(0,[z0,z1,z2,z3,z160,z4,z7]),(0,[z0,z1,z2,z3,z161,z4,z7]),(0,[z0,z1,z2,z3,z4,z62,z162]),(1,[z61,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z3,z4,z163,z7])],[(0,[z0,z1,z2,z119,z3,z4,z62]),(0,[z0,z164,z1,z2,z3,z4,z7]),(0,[z0,z165,z1,z2,z3,z4,z7]),(1,[z0,z166,z2,z3,z4,z81])],[(0,[z72,z0,z1,z2,z3,z115,z7]),(0,[z0,z1,z167,z2,z3,z4,z7])],[(0,[z0,z134,z2,z119,z3,z4,z7]),(1,[z0,z168,z1,z3,z4,z7]),(0,[z0,z169,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z170,z3,z4,z7]),(0,[z0,z171,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z4,z172,z7,z156])],[(0,[z0,z1,z2,z173,z3,z4,z7]),(0,[z0,z1,z2,z174,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z175]),(0,[z0,z1,z2,z3,z4,z4,z7]),(0,[z0,z176,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z91,z3,z80,z7])],[(0,[z0,z177,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z62,z149]),(1,[z0,z111,z119,z3,z4,z7])]],
   [[(0,[z0,z178,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z45,z4,z62]),(0,[z0,z1,z2,z3,z4,z7,z179]),(0,[z0,z180,z1,z2,z3,z4,z7])],[(1,[z0,z1,z2,z3,z181,z7]),(0,[z0,z1,z2,z3,z182,z136,z7]),(0,[z0,z1,z2,z183,z3,z4,z7])],[(0,[z0,z1,z2,z3,z184,z4,z7]),(0,[z0,z185,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z186,z7])],[(0,[z133,z0,z1,z2,z3,z4,z11]),(0,[z0,z187,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z11,z188]),(0,[z0,z189,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z190,z7]),(0,[z0,z191,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z192]),(0,[z0,z1,z2,z3,z4,z193,z7])],[(1,[z0,z1,z2,z3,z4,z103]),(0,[z0,z1,z2,z31,z3,z4,z7]),(0,[z0,z194,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z195]),(0,[z0,z1,z2,z91,z3,z86,z7]),(0,[z0,z196,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z197,z7])],[(0,[z52,z0,z1,z2,z3,z4,z198]),(0,[z199,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z200,z7]),(0,[z0,z146,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z4,z7,z201]),(0,[z0,z202,z1,z2,z3,z4,z110])]],
   [[(0,[z0,z1,z2,z3,z4,z203,z7]),(0,[z0,z1,z2,z3,z204,z4,z7]),(0,[z0,z15,z1,z2,z91,z4,z7])],[(0,[z52,z0,z1,z2,z3,z4,z205]),(0,[z0,z206,z1,z2,z3,z4,z7]),(0,[z207,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z208,z7]),(0,[z0,z1,z2,z3,z4,z80,z62]),(0,[z0,z209,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z210,z7]),(0,[z0,z211,z1,z2,z3,z4,z7]),(0,[z0,z1,z36,z2,z57,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z212])],[(0,[z30,z0,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z213,z4,z7]),(1,[z0,z214,z2,z3,z4,z7]),(0,[z0,z10,z1,z2,z3,z4,z172])],[(0,[z133,z0,z1,z2,z3,z4,z116]),(1,[z0,z1,z2,z3,z4,z158]),(0,[z0,z49,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z215,z4,z7])],[(1,[z216,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z217,z3,z4,z7]),(1,[z0,z48,z1,z3,z4,z7])],[(0,[z72,z0,z218,z2,z3,z4,z7]),(0,[z216,z1,z2,z3,z4,z7,z62]),(0,[z0,z1,z2,z3,z219,z4,z7]),(0,[z0,z49,z2,z24,z3,z4,z7])],[(0,[z0,z1,z2,z220,z3,z4,z7]),(0,[z0,z221,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z222]),(0,[z216,z0,z1,z2,z3,z4,z62]),(1,[z0,z1,z2,z3,z223,z7])]],
   [[(0,[z68,z0,z1,z2,z3,z4,z224]),(0,[z78,z0,z1,z2,z3,z4,z225]),(0,[z0,z1,z2,z3,z4,z7,z226])],[(0,[z52,z0,z1,z2,z227,z4,z7]),(0,[z0,z1,z2,z3,z228,z4,z7]),(0,[z0,z1,z2,z91,z3,z4,z11]),(0,[z0,z1,z2,z3,z4,z7,z229])],[(0,[z0,z1,z2,z230,z3,z4,z62]),(1,[z0,z41,z2,z3,z60,z7]),(0,[z0,z146,z1,z2,z3,z4,z231]),(0,[z0,z1,z2,z3,z4,z7,z232])],[(0,[z0,z1,z2,z3,z39,z4,z11]),(0,[z0,z233,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z234,z4,z7]),(0,[z0,z1,z119,z57,z3,z4,z7]),(1,[z0,z15,z1,z2,z86,z7])],[(0,[z0,z1,z2,z3,z4,z235,z7]),(0,[z0,z1,z2,z3,z4,z236,z7])],[(0,[z237,z0,z1,z2,z3,z4,z7]),(0,[z0,z44,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z238,z4,z7]),(0,[z0,z1,z2,z3,z4,z239,z7])],[(0,[z0,z18,z1,z2,z3,z4,z11]),(0,[z0,z240,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z241,z4,z7]),(0,[z0,z146,z1,z3,z4,z231,z7])],[(0,[z242,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z243,z7]),(0,[z0,z48,z1,z2,z3,z4,z7]),(0,[z244,z0,z1,z2,z3,z4,z7])]],
   [[(0,[z245,z1,z2,z23,z3,z4,z7]),(0,[z0,z18,z1,z2,z3,z246,z7]),(0,[z0,z10,z1,z2,z4,z7,z156])],[(0,[z247,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z248,z7]),(0,[z0,z1,z2,z3,z4,z7,z249])],[(0,[z0,z250,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z119,z3,z4,z7])],[(0,[z0,z1,z2,z3,z251,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z252])],[(0,[z72,z0,z134,z2,z3,z4,z7]),(0,[z0,z253,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z254,z3,z4,z62]),(0,[z0,z33,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z3,z4,z255,z7]),(0,[z0,z1,z2,z3,z256,z4,z7])],[(0,[z0,z1,z2,z257,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z258]),(0,[z259,z0,z1,z2,z3,z4,z7])],[(1,[z0,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z4,z246,z62]),(0,[z61,z0,z1,z2,z3,z4,z11]),(1,[z0,z1,z2,z3,z182,z7]),(0,[z260,z0,z1,z2,z3,z4,z7])],[(0,[z0,z261,z1,z2,z3,z4,z7]),(0,[z0,z262,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z263,z4,z7]),(0,[z0,z1,z2,z3,z45,z4,z7]),(0,[z0,z1,z2,z3,z4,z264,z7]),(0,[z0,z1,z2,z3,z4,z7,z265])]],
   [[(0,[z266,z0,z1,z2,z3,z4,z7]),(0,[z0,z146,z1,z2,z3,z4,z11]),(0,[z0,z267,z1,z2,z3,z4,z7]),(0,[z0,z268,z1,z2,z3,z4,z7])],[(0,[z269,z0,z1,z2,z3,z4,z7]),(0,[z270,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z271,z2,z3,z4,z7]),(0,[z0,z105,z1,z119,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z272]),(0,[z78,z0,z1,z2,z3,z4,z11]),(0,[z0,z273,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z158,z7]),(0,[z0,z1,z2,z3,z4,z80,z11]),(0,[z0,z1,z2,z3,z4,z7,z274]),(0,[z0,z202,z166,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z275,z4,z7])],[(0,[z0,z276,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z3,z277,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z278]),(1,[z0,z1,z2,z3,z279,z4]),(0,[z0,z1,z2,z3,z70,z80,z7]),(0,[z0,z166,z1,z2,z230,z3,z4])],[(0,[z0,z1,z2,z3,z280,z4,z7]),(0,[z0,z1,z2,z3,z281,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z205]),(0,[z245,z0,z1,z2,z3,z4,z7]),(0,[z0,z282,z1,z2,z3,z4,z7]),(0,[z0,z283,z1,z2,z3,z4,z7]),(0,[z0,z146,z1,z2,z3,z4,z7]),(0,[z0,z284,z1,z2,z3,z4,z7]),(0,[z285,z0,z1,z2,z3,z4,z7])],[(0,[z68,z0,z1,z2,z23,z4,z7]),(0,[z0,z1,z286,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z287,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z86,z11])],[(0,[z0,z288,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z91,z3,z39,z7]),(0,[z0,z276,z1,z2,z3,z4,z7]),(0,[z0,z99,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z3,z4,z289,z7]),(0,[z0,z1,z290,z2,z3,z4,z7])],[(0,[z72,z0,z1,z2,z3,z4,z62]),(0,[z291,z0,z1,z2,z3,z4,z222]),(0,[z30,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z60,z4,z62]),(0,[z0,z1,z2,z3,z4,z62,z272]),(0,[z0,z1,z2,z3,z292,z4,z7])],[(0,[z0,z1,z2,z3,z4,z293,z7]),(0,[z0,z1,z2,z3,z294,z4,z7]),(0,[z0,z1,z2,z3,z27,z4,z80])],[(0,[z72,z133,z1,z2,z3,z4,z7]),(0,[z52,z1,z2,z295,z3,z4,z7]),(0,[z296,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z297,z2,z3,z4,z7])],[(0,[z68,z0,z1,z2,z3,z4,z104]),(0,[z0,z1,z2,z57,z3,z4,z62]),(0,[z0,z1,z2,z3,z4,z7,z298]),(0,[z0,z299,z1,z2,z3,z4,z7])],[(0,[z216,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z136,z4,z62]),(0,[z0,z1,z2,z300,z3,z4,z7]),(0,[z0,z1,z2,z3,z301,z4,z7])],[(0,[z302,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z303,z7]),(0,[z0,z202,z1,z2,z3,z4,z81]),(0,[z0,z17,z1,z2,z3,z246,z7]),(0,[z0,z1,z2,z3,z4,z7,z304])]],
   [[(0,[z0,z1,z2,z3,z4,z305,z7]),(0,[z0,z49,z1,z2,z3,z4,z62]),(0,[z0,z306,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z7,z129])],[(0,[z0,z1,z2,z3,z4,z307,z7]),(0,[z0,z308,z1,z2,z3,z4,z7]),(0,[z0,z309,z1,z2,z3,z136,z7]),(0,[z0,z1,z2,z3,z182,z4,z7]),(0,[z0,z1,z2,z230,z3,z4,z7])],[(0,[z0,z1,z2,z3,z310,z4,z7]),(0,[z0,z1,z2,z311,z3,z4,z7]),(0,[z0,z1,z2,z3,z27,z4,z110]),(1,[z0,z1,z2,z4,z312,z7]),(0,[z0,z313,z1,z2,z3,z4,z7])],[(0,[z314,z0,z1,z2,z3,z4,z7]),(0,[z0,z315,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z316]),(0,[z0,z317,z1,z2,z3,z4,z7]),(0,[z0,z155,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z40,z62]),(0,[z0,z15,z1,z2,z3,z40,z7]),(0,[z0,z1,z2,z318,z3,z4,z7]),(0,[z0,z2,z3,z136,z4,z70,z7]),(0,[z0,z1,z2,z3,z4,z7,z319]),(0,[z0,z1,z2,z3,z4,z320,z7])],[(0,[z0,z321,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z8,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z322,z7]),(0,[z0,z1,z2,z3,z4,z7,z323]),(0,[z0,z324,z1,z2,z3,z4,z7]),(1,[z0,z309,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z279,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z325])],[(0,[z326,z0,z1,z2,z3,z4,z7]),(0,[z0,z105,z1,z2,z3,z4,z62]),(1,[z0,z267,z1,z2,z3,z4]),(0,[z0,z1,z327,z2,z3,z4,z7])],[(0,[z0,z328,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z135,z4,z7]),(0,[z0,z329,z1,z2,z3,z4,z7]),(0,[z0,z330,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z331,z3,z4,z7])]],
   [[(0,[z332,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z333,z7]),(0,[z0,z1,z2,z3,z4,z334,z7]),(0,[z0,z1,z2,z3,z335,z4,z7]),(0,[z0,z336,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z337,z7]),(0,[z0,z1,z2,z3,z4,z7,z338])],[(0,[z0,z1,z339,z2,z3,z4,z7]),(0,[z78,z0,z1,z2,z3,z39,z7]),(0,[z0,z1,z2,z3,z4,z225,z7]),(0,[z0,z1,z2,z3,z340,z4,z62]),(0,[z0,z1,z2,z3,z4,z172,z62]),(0,[z341,z0,z1,z2,z3,z4,z7])],[(0,[z0,z342,z1,z2,z3,z4,z7]),(0,[z0,z343,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z254,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z243,z62]),(0,[z0,z43,z1,z2,z126,z4,z7]),(0,[z344,z0,z1,z2,z3,z4,z7]),(0,[z345,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z312,z7]),(0,[z0,z1,z2,z346,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z347])],[(1,[z0,z1,z2,z184,z4,z7]),(0,[z245,z0,z1,z2,z3,z4,z348]),(0,[z0,z1,z2,z3,z4,z7,z349]),(0,[z30,z78,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z350,z4,z7]),(0,[z30,z0,z1,z2,z3,z39,z7]),(0,[z0,z351,z1,z2,z3,z4,z7]),(1,[z0,z17,z1,z3,z246,z7])],[(1,[z0,z1,z2,z3,z4,z7]),(0,[z291,z0,z1,z57,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z11,z323]),(0,[z0,z111,z1,z119,z3,z4,z7]),(0,[z0,z202,z1,z2,z3,z223,z7]),(0,[z0,z1,z2,z3,z4,z246,z7]),(1,[z0,z1,z2,z3,z4,z197])],[(0,[z0,z1,z2,z3,z4,z7,z188]),(0,[z0,z1,z2,z3,z4,z11,z34]),(0,[z0,z352,z1,z2,z3,z4,z7]),(0,[z0,z105,z15,z1,z2,z4,z7]),(0,[z353,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z354]),(0,[z0,z355,z1,z2,z3,z4,z7]),(0,[z0,z356,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z357])]],
   [[(0,[z0,z1,z2,z3,z358,z4,z7]),(0,[z359,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z360,z4,z7]),(0,[z361,z0,z1,z2,z3,z4,z7]),(0,[z0,z362,z1,z2,z3,z4,z7])],[(0,[z0,z1,z218,z2,z3,z4,z62]),(0,[z0,z1,z2,z363,z3,z4,z7]),(0,[z0,z15,z1,z2,z4,z86,z7]),(0,[z0,z364,z1,z2,z3,z4,z7])],[(0,[z245,z0,z1,z2,z3,z365,z7]),(0,[z0,z1,z2,z3,z4,z366,z7]),(0,[z0,z105,z1,z3,z58,z4,z7]),(1,[z0,z367,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z368,z4,z7]),(1,[z245,z1,z2,z23,z4,z7]),(0,[z0,z369,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z370,z3,z4,z7]),(0,[z0,z371,z1,z2,z3,z4,z7])],[],[(0,[z0,z1,z2,z3,z4,z7,z5]),(0,[z269,z0,z1,z2,z3,z4,z62])],[(0,[z372,z0,z1,z2,z3,z4,z7]),(0,[z291,z0,z1,z2,z3,z4,z373]),(0,[z0,z1,z2,z3,z3,z4,z7]),(0,[z0,z15,z1,z2,z9,z4,z7]),(0,[z0,z1,z2,z57,z3,z4,z11]),(0,[z0,z1,z2,z3,z4,z374,z7]),(0,[z0,z10,z202,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z7,z375]),(0,[z0,z1,z2,z376,z3,z4,z7])],[(0,[z0,z1,z2,z3,z377,z4,z7]),(0,[z0,z1,z2,z24,z9,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z22]),(0,[z0,z378,z1,z2,z3,z4,z7]),(0,[z0,z379,z1,z2,z3,z4,z7]),(0,[z0,z380,z1,z2,z3,z4,z7]),(0,[z0,z381,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z213,z4,z246]),(0,[z0,z1,z2,z37,z4,z86,z7])]],
   [[(1,[z0,z1,z382,z3,z4,z7]),(0,[z72,z0,z1,z2,z184,z4,z7]),(1,[z0,z383,z2,z3,z4,z7]),(0,[z52,z0,z1,z57,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z384,z7]),(0,[z0,z1,z2,z3,z4,z7,z385])],[(0,[z72,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z386,z2,z3,z4,z7]),(0,[z0,z49,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z3,z60,z4,z7]),(0,[z387,z0,z1,z2,z3,z4,z7])],[(0,[z388,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z365,z4,z7]),(0,[z245,z0,z1,z2,z3,z4,z62]),(0,[z0,z2,z3,z60,z4,z70,z7]),(0,[z0,z1,z2,z230,z3,z4,z156])],[(0,[z0,z389,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z37,z4,z62]),(0,[z0,z390,z1,z2,z3,z4,z7]),(0,[z391,z0,z1,z2,z3,z4,z7]),(1,[z0,z10,z1,z2,z4,z156])],[(0,[z0,z43,z218,z2,z3,z4,z7]),(0,[z0,z202,z1,z2,z3,z4,z62]),(0,[z0,z69,z1,z2,z91,z3,z7]),(0,[z0,z1,z2,z57,z3,z4,z7])],[(0,[z0,z1,z2,z3,z392,z4,z7]),(0,[z0,z1,z2,z3,z136,z4,z7]),(0,[z0,z393,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z394,z3,z4,z7]),(0,[z0,z1,z2,z3,z395,z4,z7]),(0,[z0,z69,z1,z2,z3,z70,z7])],[(0,[z0,z1,z2,z3,z396,z4,z7]),(0,[z0,z41,z2,z3,z60,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z397]),(0,[z0,z1,z2,z3,z4,z398,z7])]],
   [[(0,[z0,z399,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z4,z11,z385]),(1,[z0,z1,z2,z3,z27,z80])],[(0,[z52,z0,z1,z2,z3,z181,z7]),(0,[z1,z2,z23,z3,z9,z4,z7]),(0,[z0,z1,z2,z400,z3,z4,z7]),(0,[z401,z0,z1,z2,z3,z4,z7]),(0,[z0,z402,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z403,z4,z7])],[(0,[z0,z404,z1,z2,z3,z4,z7]),(0,[z0,z111,z1,z2,z3,z4,z62]),(0,[z0,z44,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z405,z3,z4,z7]),(0,[z0,z1,z36,z2,z24,z4,z7]),(0,[z0,z1,z2,z406,z3,z4,z7]),(0,[z407,z0,z1,z2,z3,z4,z7])],[(1,[z0,z1,z2,z3,z4,z348]),(0,[z0,z1,z2,z3,z4,z40,z7]),(0,[z0,z43,z1,z119,z3,z4,z7]),(0,[z0,z408,z1,z2,z3,z4,z7]),(0,[z0,z41,z2,z3,z136,z4,z7]),(0,[z0,z15,z41,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z409,z4,z7]),(0,[z0,z1,z3,z4,z231,z7,z147])],[(0,[z72,z0,z1,z382,z3,z4,z7]),(0,[z0,z1,z295,z119,z3,z4,z7]),(0,[z0,z44,z1,z295,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z410,z7]),(0,[z0,z1,z2,z3,z411,z4,z7])],[(0,[z0,z1,z2,z412,z3,z4,z7]),(0,[z52,z0,z383,z2,z3,z4,z7]),(0,[z0,z1,z413,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z88]),(0,[z30,z1,z2,z3,z39,z4,z7]),(0,[z0,z414,z1,z2,z3,z4,z7]),(0,[z0,z105,z1,z2,z3,z4,z7])],[(0,[z415,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z416,z4,z7]),(0,[z0,z49,z1,z2,z136,z4,z7]),(0,[z0,z1,z2,z3,z4,z417,z7]),(0,[z0,z1,z2,z3,z4,z418,z7])],[(0,[z0,z1,z2,z119,z3,z4,z11]),(0,[z419,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z420,z4,z7])]],
   [[(0,[z0,z421,z1,z2,z3,z4,z7]),(0,[z0,z44,z1,z14,z3,z4,z7]),(0,[z0,z1,z422,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z39,z246,z7]),(0,[z0,z1,z2,z3,z4,z423,z7]),(0,[z0,z1,z2,z3,z4,z7,z424])],[(0,[z0,z1,z2,z382,z3,z4,z7]),(1,[z0,z1,z2,z3,z365,z7]),(0,[z0,z1,z2,z3,z340,z4,z7]),(0,[z0,z1,z2,z3,z4,z425,z7]),(0,[z0,z1,z2,z426,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z172,z7])],[(0,[z0,z1,z218,z2,z3,z4,z11]),(0,[z0,z43,z134,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z427,z4,z7]),(0,[z0,z1,z2,z3,z4,z428,z7]),(0,[z0,z1,z2,z3,z27,z4,z81]),(0,[z0,z33,z1,z2,z3,z7,z34])],[(0,[z0,z1,z2,z3,z4,z11,z429]),(0,[z430,z0,z1,z2,z3,z4,z7]),(0,[z0,z105,z1,z36,z3,z4,z7]),(0,[z0,z1,z2,z4,z312,z246,z7])],[(0,[z0,z1,z2,z3,z45,z4,z11])],[(0,[z0,z1,z2,z3,z4,z431,z7]),(0,[z0,z1,z2,z3,z4,z432,z7]),(0,[z0,z1,z2,z3,z433,z4,z7]),(0,[z0,z1,z2,z3,z4,z434,z7]),(0,[z0,z146,z1,z2,z3,z27,z4]),(0,[z0,z33,z1,z2,z3,z27,z7])],[(0,[z0,z435,z1,z2,z3,z4,z7]),(0,[z269,z0,z1,z2,z3,z4,z11])],[(0,[z0,z1,z2,z3,z4,z436,z7]),(0,[z0,z1,z2,z3,z58,z4,z62]),(0,[z0,z1,z2,z3,z4,z437,z11]),(1,[z0,z1,z2,z281,z4,z7]),(1,[z0,z105,z1,z58,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z438])]],
   [[(0,[z0,z1,z218,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z439,z4,z7]),(0,[z30,z0,z1,z2,z3,z4,z54])],[(0,[z0,z1,z2,z3,z4,z373,z7]),(0,[z0,z309,z1,z2,z3,z4,z7])],[(0,[z0,z1,z14,z119,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z231,z62]),(0,[z0,z440,z1,z2,z3,z4,z7]),(0,[z0,z441,z1,z2,z3,z4,z7])],[(0,[z291,z0,z1,z2,z3,z4,z62]),(0,[z0,z168,z1,z2,z3,z4,z7]),(0,[z245,z0,z1,z2,z3,z4,z11]),(0,[z30,z0,z1,z2,z350,z4,z7]),(0,[z0,z1,z2,z442,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z443,z7])],[(0,[z0,z444,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z224]),(0,[z0,z1,z2,z3,z37,z4,z11])],[(0,[z0,z53,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z437,z7]),(0,[z0,z1,z445,z2,z3,z4,z7]),(0,[z0,z446,z1,z2,z3,z4,z7]),(0,[z0,z447,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z27,z4,z34])],[(0,[z0,z448,z1,z2,z3,z4,z7]),(0,[z0,z49,z2,z3,z4,z70,z7]),(1,[z0,z1,z2,z3,z449,z7]),(0,[z0,z367,z1,z2,z3,z4,z7])],[(0,[z134,z1,z218,z2,z3,z4,z7]),(0,[z30,z0,z1,z2,z3,z4,z11]),(0,[z0,z105,z44,z1,z3,z4,z7]),(0,[z0,z450,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z451]),(0,[z0,z41,z1,z2,z3,z4,z192]),(0,[z0,z2,z3,z4,z110,z7,z81]),(0,[z0,z10,z33,z1,z2,z3,z4]),(0,[z0,z452,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z7,z129,z156]),(0,[z0,z453,z1,z2,z3,z4,z7])]],
   [[(0,[z454,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z225]),(0,[z0,z1,z2,z3,z4,z455,z62]),(0,[z0,z1,z2,z3,z4,z62,z258]),(1,[z0,z146,z1,z3,z4,z231]),(1,[z0,z155,z1,z2,z3,z7]),(0,[z0,z1,z2,z230,z3,z27,z4])],[(0,[z0,z1,z2,z456,z3,z4,z7]),(0,[z0,z1,z214,z2,z3,z4,z7])],[(0,[z0,z457,z1,z2,z3,z4,z62]),(0,[z0,z458,z1,z2,z3,z4,z62]),(0,[z0,z15,z214,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z37,z4,z7])],[(0,[z0,z459,z1,z2,z3,z4,z7]),(0,[z216,z0,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z3,z460,z4,z7]),(0,[z0,z202,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z461,z4,z7]),(0,[z291,z0,z105,z1,z3,z4,z7]),(0,[z0,z462,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z91,z3,z40,z7]),(0,[z0,z166,z1,z2,z3,z4,z110]),(0,[z0,z1,z2,z3,z4,z7,z463]),(0,[z0,z15,z33,z1,z2,z3,z7])],[(0,[z0,z464,z1,z2,z3,z4,z7]),(0,[z0,z15,z1,z36,z2,z4,z7]),(0,[z0,z465,z1,z2,z3,z4,z7]),(0,[z0,z466,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z467,z7])],[(0,[z52,z0,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z295,z3,z4,z62]),(0,[z0,z1,z468,z2,z3,z4,z7]),(0,[z0,z1,z2,z230,z3,z4,z11]),(0,[z0,z1,z2,z3,z4,z469,z7]),(0,[z0,z1,z2,z3,z4,z470,z7]),(0,[z0,z1,z2,z3,z4,z7,z81]),(1,[z0,z18,z1,z3,z45,z7]),(0,[z0,z33,z146,z1,z2,z3,z4])],[(0,[z0,z399,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z11,z7]),(0,[z0,z471,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z472,z4,z7])]],
   [[(0,[z245,z0,z1,z2,z3,z384,z7]),(0,[z0,z1,z2,z3,z473,z4,z7]),(0,[z0,z1,z2,z474,z3,z4,z7]),(1,[z0,z85,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z7,z475])],[(0,[z476,z0,z1,z2,z3,z4,z7]),(0,[z0,z111,z1,z2,z3,z4,z7]),(0,[z0,z1,z477,z2,z3,z4,z7])],[(0,[z0,z1,z2,z478,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z348,z7]),(1,[z0,z1,z2,z3,z4,z54]),(0,[z0,z479,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z60,z80,z7]),(0,[z0,z1,z2,z3,z480,z4,z7]),(0,[z0,z26,z1,z2,z3,z4,z147])],[(0,[z481,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z45,z39,z7]),(0,[z0,z1,z2,z3,z4,z482,z62]),(0,[z0,z1,z36,z57,z3,z4,z7]),(0,[z0,z483,z1,z2,z3,z4,z7])],[(0,[z484,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z333,z11]),(0,[z0,z485,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z213,z4]),(0,[z0,z1,z486,z2,z3,z4,z7]),(0,[z487,z0,z1,z2,z3,z4,z7]),(0,[z0,z85,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z488,z4,z7])],[(1,[z0,z1,z2,z350,z4,z7]),(0,[z0,z489,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z4,z337,z11]),(0,[z0,z1,z2,z3,z4,z11,z81]),(0,[z490,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z491,z4,z7]),(0,[z0,z492,z1,z2,z3,z4,z7]),(0,[z0,z33,z1,z2,z230,z3,z4]),(0,[z0,z1,z2,z493,z3,z4,z7]),(0,[z0,z494,z1,z2,z3,z4,z7])],[(0,[z495,z0,z1,z2,z3,z4,z7]),(0,[z52,z0,z105,z1,z3,z4,z7]),(0,[z0,z1,z2,z3,z27,z4,z62]),(0,[z0,z1,z496,z2,z3,z4,z7]),(0,[z0,z497,z1,z2,z3,z4,z7])]],
   [[(0,[z498,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z499,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z58,z4,z11]),(0,[z0,z343,z1,z2,z3,z4,z11]),(0,[z0,z33,z1,z2,z3,z60,z7])],[(0,[z500,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z74,z4,z7]),(0,[z0,z1,z2,z3,z4,z501,z7]),(0,[z0,z1,z2,z502,z3,z4,z7]),(0,[z0,z105,z1,z2,z37,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z503]),(0,[z0,z1,z2,z3,z4,z7,z34])],[(0,[z504,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z505,z3,z4,z7]),(0,[z0,z506,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z3,z4,z246,z11]),(0,[z0,z1,z2,z507,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z147]),(0,[z0,z508,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z509,z7])],[(0,[z0,z69,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z4,z231,z11]),(0,[z0,z1,z2,z3,z4,z510,z7])],[(0,[z0,z10,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z511,z4,z7]),(0,[z0,z1,z2,z3,z4,z512,z7]),(0,[z0,z1,z513,z2,z3,z4,z7])],[(0,[z78,z0,z1,z2,z3,z40,z7]),(0,[z0,z15,z1,z2,z3,z4,z62]),(0,[z0,z514,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z27,z80,z7])],[(0,[z0,z1,z2,z23,z3,z4,z62]),(0,[z0,z1,z2,z515,z3,z4,z7]),(0,[z0,z1,z2,z24,z3,z4,z62]),(0,[z1,z2,z3,z4,z11,z7,z62]),(0,[z516,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z58,z4,z7])],[(0,[z0,z1,z2,z3,z4,z517,z7])]],
   [[(0,[z0,z518,z1,z2,z3,z4,z7]),(0,[z0,z519,z1,z2,z3,z4,z7]),(1,[z0,z240,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z7,z520]),(0,[z521,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z156])],[(1,[z0,z1,z2,z3,z4,z104]),(0,[z0,z1,z2,z3,z40,z246,z7]),(0,[z0,z1,z2,z3,z522,z4,z7]),(0,[z0,z1,z2,z3,z4,z231,z7])],[(0,[z0,z1,z2,z523,z3,z4,z7]),(0,[z291,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z524,z2,z3,z4,z7]),(0,[z0,z41,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z4,z11,z147]),(0,[z0,z202,z2,z3,z4,z110,z7]),(0,[z0,z525,z1,z2,z3,z4,z7])],[(1,[z0,z1,z2,z3,z4,z116]),(0,[z526,z0,z1,z2,z3,z4,z7]),(0,[z0,z527,z1,z2,z3,z4,z7]),(0,[z0,z528,z1,z2,z3,z4,z7])],[(0,[z0,z26,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z529,z4,z7])],[(0,[z72,z0,z1,z2,z74,z4,z7]),(0,[z0,z99,z1,z2,z24,z4,z7]),(0,[z0,z41,z49,z2,z3,z4,z7]),(0,[z0,z530,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z531,z7]),(0,[z0,z532,z1,z2,z3,z4,z7])],[(0,[z72,z0,z1,z2,z3,z4,z11]),(0,[z0,z1,z533,z2,z3,z4,z7]),(0,[z0,z534,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z535,z7]),(0,[z0,z1,z2,z3,z60,z4,z11]),(1,[z0,z1,z25,z3,z4,z7]),(0,[z0,z10,z166,z1,z2,z3,z4])],[(0,[z52,z0,z1,z2,z135,z4,z7]),(0,[z52,z0,z1,z2,z3,z4,z11]),(0,[z536,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z384,z7]),(0,[z0,z1,z2,z537,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z455,z7]),(0,[z0,z43,z1,z2,z3,z4,z7]),(0,[z0,z538,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z96]),(0,[z0,z1,z2,z3,z449,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z539]),(0,[z0,z1,z2,z3,z540,z4,z7]),(0,[z0,z541,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z230,z4,z172,z7])]],
   [[(0,[z0,z542,z1,z2,z3,z4,z7]),(0,[z0,z390,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z3,z4,z11,z156]),(0,[z543,z0,z1,z2,z3,z4,z7])],[(0,[z52,z0,z1,z295,z3,z4,z7]),(0,[z0,z457,z1,z2,z3,z4,z7]),(0,[z0,z458,z1,z2,z3,z4,z7]),(0,[z0,z544,z1,z2,z3,z4,z7]),(0,[z0,z15,z1,z2,z3,z86,z7]),(0,[z0,z1,z2,z3,z4,z545,z7])],[(0,[z0,z1,z2,z57,z23,z4,z7]),(0,[z0,z1,z2,z3,z136,z4,z11])],[(0,[z133,z0,z218,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z62]),(0,[z0,z546,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z547,z4,z7]),(0,[z0,z1,z2,z3,z4,z548,z7])],[(0,[z0,z549,z1,z2,z3,z4,z7]),(0,[z0,z26,z1,z3,z4,z7,z147]),(0,[z0,z1,z2,z3,z550,z4,z7]),(0,[z551,z0,z1,z2,z3,z4,z7])],[(0,[z133,z0,z1,z2,z3,z4,z103]),(0,[z52,z0,z1,z2,z3,z4,z7]),(0,[z52,z0,z1,z14,z3,z4,z7]),(0,[z0,z1,z2,z295,z3,z4,z7]),(0,[z78,z1,z2,z3,z4,z40,z7]),(0,[z0,z105,z1,z2,z58,z4,z7])],[(1,[z72,z218,z2,z3,z4,z7]),(0,[z0,z218,z2,z119,z3,z4,z7]),(0,[z0,z17,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z4,z552,z7]),(0,[z0,z553,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z554,z7]),(0,[z0,z26,z1,z2,z3,z4,z231]),(0,[z0,z1,z2,z555,z3,z4,z7])]],
   [[(1,[z0,z53,z2,z3,z4,z7]),(0,[z78,z0,z1,z2,z3,z4,z88]),(0,[z0,z1,z2,z3,z4,z40,z11]),(0,[z0,z1,z2,z3,z27,z4,z11]),(0,[z0,z556,z1,z2,z3,z4,z7]),(0,[z0,z146,z26,z1,z3,z4,z7])],[(0,[z557,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z558,z4,z7])],[(0,[z0,z105,z1,z2,z3,z4,z11]),(0,[z0,z559,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z560,z7])],[(0,[z68,z0,z1,z2,z9,z4,z7]),(0,[z0,z1,z2,z3,z4,z11,z62]),(0,[z0,z1,z2,z3,z4,z70,z62]),(0,[z0,z1,z2,z3,z4,z482,z7]),(1,[z0,z202,z2,z3,z4,z110])],[(0,[z1,z14,z2,z295,z3,z4,z7]),(0,[z0,z69,z1,z2,z3,z4,z11]),(0,[z0,z44,z2,z119,z3,z4,z7]),(0,[z0,z166,z1,z2,z3,z4,z81]),(0,[z0,z202,z1,z2,z3,z449,z7]),(0,[z0,z561,z1,z2,z3,z4,z7]),(1,[z0,z1,z36,z57,z4,z7])],[(0,[z0,z489,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z562,z3,z4,z7]),(0,[z563,z0,z1,z2,z3,z4,z7]),(0,[z0,z564,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z429]),(0,[z0,z1,z2,z3,z4,z172,z11]),(0,[z565,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z566,z4,z7]),(0,[z0,z41,z1,z2,z91,z3,z7]),(0,[z0,z1,z2,z3,z567,z4,z7]),(0,[z0,z1,z2,z3,z27,z4,z7])],[(0,[z0,z1,z2,z568,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z569,z7]),(0,[z0,z1,z2,z570,z3,z4,z7]),(0,[z571,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z572,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z573,z7]),(0,[z0,z49,z1,z25,z3,z4,z7]),(0,[z0,z41,z1,z2,z3,z70,z7]),(0,[z0,z574,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z575,z3,z4,z7])],[(0,[z576,z0,z1,z2,z3,z4,z7]),(0,[z133,z0,z134,z2,z3,z4,z7]),(0,[z133,z134,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z577,z4,z7]),(0,[z0,z43,z44,z1,z3,z4,z7]),(0,[z0,z578,z1,z2,z3,z4,z7]),(0,[z0,z579,z1,z2,z3,z4,z7])],[(0,[z580,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z36,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z4,z432,z11]),(0,[z581,z0,z1,z2,z3,z4,z7]),(0,[z0,z69,z1,z2,z3,z4,z7])],[(0,[z0,z1,z1,z2,z3,z4,z7]),(0,[z0,z10,z1,z2,z3,z4,z7]),(0,[z582,z0,z1,z2,z3,z4,z7]),(0,[z0,z583,z1,z2,z3,z4,z7])],[(0,[z0,z584,z1,z2,z3,z4,z62]),(0,[z0,z17,z1,z3,z4,z246,z7]),(0,[z0,z15,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z23,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z585,z7]),(0,[z0,z26,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z24,z3,z4,z7]),(0,[z0,z586,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z587])],[(0,[z0,z1,z2,z3,z60,z39,z7]),(0,[z0,z99,z2,z3,z136,z4,z7]),(0,[z0,z588,z1,z2,z3,z4,z7]),(0,[z589,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z590])],[(0,[z0,z1,z2,z591,z3,z4,z7]),(0,[z592,z0,z1,z2,z3,z4,z7]),(0,[z0,z105,z1,z2,z136,z4,z7]),(0,[z0,z240,z1,z2,z3,z136,z4]),(0,[z0,z267,z1,z2,z3,z4,z246])]],
   [[(0,[z0,z1,z2,z9,z136,z4,z7]),(0,[z0,z1,z2,z3,z4,z593,z7])],[(1,[z52,z1,z295,z3,z4,z7]),(0,[z0,z1,z2,z42,z3,z4,z7]),(0,[z0,z41,z1,z2,z3,z4,z7]),(0,[z0,z15,z367,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z594,z4,z7]),(0,[z0,z1,z2,z230,z3,z4,z172])],[(0,[z0,z134,z1,z2,z3,z4,z62]),(1,[z0,z1,z2,z3,z4,z222]),(0,[z0,z1,z2,z595,z3,z4,z7])],[(0,[z0,z166,z2,z3,z4,z7,z81]),(0,[z0,z26,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z596])],[(0,[z0,z1,z2,z3,z597,z4,z7]),(0,[z0,z1,z2,z598,z3,z4,z7]),(0,[z0,z1,z2,z23,z136,z4,z7]),(0,[z0,z1,z2,z3,z4,z599,z7]),(0,[z0,z1,z2,z600,z3,z4,z7])],[(0,[z61,z1,z2,z3,z4,z11,z7]),(0,[z0,z1,z2,z3,z4,z601,z7]),(0,[z0,z49,z1,z2,z24,z4,z7])],[(0,[z0,z1,z2,z3,z4,z75,z7]),(0,[z0,z1,z383,z2,z3,z4,z7]),(0,[z0,z602,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z224,z7]),(0,[z0,z105,z1,z2,z57,z4,z7]),(0,[z0,z1,z2,z3,z4,z603,z7])],[(0,[z133,z0,z1,z2,z3,z4,z62]),(0,[z245,z0,z1,z2,z23,z4,z7]),(0,[z0,z1,z2,z3,z4,z604,z7]),(0,[z605,z0,z1,z2,z3,z4,z7])]],
   [[(0,[z0,z202,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z606,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z607,z7])],[(0,[z0,z608,z1,z2,z3,z4,z11]),(0,[z0,z43,z1,z2,z281,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z7]),(0,[z0,z18,z1,z3,z45,z4,z7])],[(0,[z0,z1,z2,z3,z4,z609,z7]),(0,[z0,z43,z1,z2,z3,z4,z62]),(0,[z0,z610,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z11,z11])],[(0,[z0,z611,z1,z2,z3,z4,z7]),(0,[z0,z17,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z612,z4,z7]),(0,[z0,z10,z1,z2,z230,z4,z7])],[(0,[z0,z15,z1,z2,z3,z39,z7]),(0,[z0,z111,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z3,z4,z613,z7]),(0,[z0,z33,z1,z2,z3,z4,z34])],[(0,[z0,z608,z1,z2,z3,z4,z7]),(0,[z0,z1,z614,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z162])]],
   [[(0,[z291,z1,z14,z2,z3,z4,z7]),(0,[z0,z15,z1,z2,z3,z37,z7]),(0,[z0,z1,z2,z3,z615,z4,z7])],[(0,[z68,z245,z1,z2,z3,z4,z7]),(0,[z0,z166,z1,z2,z3,z4,z62]),(0,[z0,z69,z2,z3,z4,z70,z7]),(0,[z0,z1,z2,z3,z4,z7,z96]),(0,[z0,z616,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z70,z7]),(0,[z0,z17,z1,z2,z3,z45,z7]),(0,[z0,z1,z2,z3,z617,z4,z7]),(0,[z0,z618,z1,z2,z3,z4,z7])],[(0,[z619,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z293]),(0,[z0,z1,z2,z620,z3,z4,z7])],[(0,[z621,z0,z1,z2,z3,z4,z7]),(0,[z0,z622,z1,z2,z3,z4,z7]),(0,[z0,z10,z1,z2,z3,z4,z156]),(0,[z0,z1,z2,z3,z4,z7,z623])],[(0,[z0,z43,z44,z2,z3,z4,z7]),(0,[z0,z1,z2,z624,z3,z4,z7]),(0,[z0,z1,z625,z2,z3,z4,z7]),(0,[z0,z626,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z627,z3,z4,z7])],[(1,[z0,z1,z2,z3,z4,z198]),(0,[z0,z1,z2,z3,z628,z4,z7])],[(0,[z0,z1,z2,z3,z629,z4,z7]),(0,[z0,z1,z2,z3,z45,z40,z7]),(0,[z0,z1,z2,z3,z39,z4,z62]),(0,[z0,z630,z1,z2,z3,z4,z7]),(0,[z0,z1,z631,z2,z3,z4,z7]),(0,[z0,z1,z3,z45,z4,z246,z7]),(0,[z0,z1,z2,z3,z4,z7,z632]),(0,[z0,z1,z2,z633,z3,z4,z7]),(0,[z0,z33,z1,z2,z3,z4,z80])]],
   [[(0,[z634,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z198,z7]),(0,[z0,z1,z2,z3,z4,z635,z7]),(0,[z0,z1,z2,z3,z4,z7,z636])],[(1,[z0,z1,z2,z3,z4,z205]),(0,[z0,z1,z2,z3,z4,z62,z81]),(0,[z637,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z36,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z638,z4,z7])],[(0,[z0,z1,z14,z2,z3,z4,z62]),(0,[z0,z18,z1,z2,z3,z4,z62]),(1,[z0,z49,z2,z24,z4,z7]),(1,[z0,z26,z1,z3,z4,z147]),(0,[z0,z1,z2,z3,z4,z197,z86])],[(0,[z72,z1,z218,z2,z3,z4,z7]),(0,[z0,z134,z1,z2,z3,z4,z11]),(0,[z0,z639,z1,z2,z3,z4,z7]),(0,[z0,z584,z1,z2,z3,z4,z7]),(0,[z0,z640,z1,z2,z3,z4,z7]),(0,[z0,z1,z641,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z642]),(0,[z0,z1,z2,z3,z4,z643,z7])],[(0,[z0,z1,z2,z9,z37,z4,z7]),(0,[z644,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z645,z7]),(1,[z0,z1,z2,z91,z37,z7])],[(0,[z0,z646,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z373]),(0,[z0,z1,z2,z3,z522,z4,z11]),(0,[z0,z1,z2,z3,z279,z136,z4]),(0,[z0,z33,z1,z2,z3,z4,z110])],[(0,[z72,z0,z1,z2,z3,z4,z293]),(0,[z291,z0,z1,z2,z3,z4,z11]),(0,[z0,z647,z1,z2,z3,z4,z7]),(0,[z0,z202,z1,z2,z230,z3,z4]),(1,[z0,z1,z2,z230,z4,z172])]],
   [[(0,[z0,z33,z1,z2,z3,z4,z62]),(0,[z0,z527,z1,z2,z3,z4,z11]),(0,[z0,z43,z111,z2,z3,z4,z7]),(0,[z0,z1,z36,z2,z136,z4,z7]),(0,[z0,z1,z2,z3,z648,z4,z7]),(0,[z0,z1,z2,z649,z3,z4,z7])],[(0,[z0,z134,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z227,z4,z7]),(0,[z291,z0,z1,z295,z3,z4,z7]),(0,[z0,z1,z650,z2,z3,z4,z7]),(0,[z0,z1,z2,z23,z37,z4,z7]),(0,[z0,z1,z2,z3,z651,z4,z7])],[(0,[z0,z1,z2,z3,z4,z181,z7]),(0,[z0,z168,z1,z3,z9,z4,z7]),(0,[z0,z1,z2,z3,z652,z4,z7]),(0,[z30,z0,z1,z2,z3,z40,z7]),(0,[z61,z0,z1,z2,z3,z4,z62])],[(0,[z245,z0,z1,z2,z3,z4,z22]),(0,[z0,z1,z2,z126,z3,z4,z7]),(0,[z0,z1,z2,z3,z653,z4,z7])],[(0,[z654,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z62,z34]),(0,[z0,z43,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z3,z4,z655,z7])],[(0,[z291,z0,z1,z14,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z62,z147]),(0,[z0,z656,z1,z2,z3,z4,z7]),(0,[z657,z0,z1,z2,z3,z4,z7]),(0,[z0,z658,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z659,z4,z7]),(0,[z660,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z661,z4,z7])],[(0,[z133,z0,z1,z2,z3,z4,z7]),(0,[z662,z0,z1,z2,z3,z4,z7]),(0,[z78,z0,z1,z2,z3,z4,z62]),(0,[z0,z15,z69,z1,z2,z3,z7]),(0,[z0,z15,z1,z2,z3,z80,z7])],[]],
   [[(0,[z663,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z192,z7]),(0,[z0,z1,z2,z3,z4,z7,z664])],[(0,[z0,z549,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z665,z3,z4,z7]),(0,[z666,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z227,z4,z7]),(0,[z0,z1,z2,z295,z3,z4,z11]),(1,[z291,z1,z14,z3,z4,z7]),(0,[z68,z0,z1,z2,z3,z4,z62]),(0,[z0,z166,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z3,z4,z667,z7])],[(0,[z0,z1,z2,z3,z668,z4,z7]),(0,[z0,z1,z2,z3,z4,z62,z156]),(0,[z0,z1,z2,z3,z4,z669,z7]),(0,[z0,z670,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z86,z62]),(0,[z0,z671,z1,z2,z3,z4,z7]),(0,[z0,z672,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z39,z70,z7]),(0,[z0,z99,z1,z2,z3,z4,z62])],[(0,[z0,z1,z2,z3,z4,z673,z7]),(0,[z0,z1,z2,z3,z4,z7,z674]),(0,[z0,z1,z2,z3,z4,z675,z7]),(0,[z0,z1,z676,z2,z3,z4,z7])],[(0,[z677,z0,z1,z2,z3,z4,z7]),(0,[z678,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z679,z2,z3,z4,z7]),(0,[z0,z0,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z680,z4,z7]),(0,[z0,z13,z1,z2,z4,z246,z7]),(0,[z0,z1,z2,z3,z4,z7,z681])]],
   [[(0,[z245,z0,z1,z2,z9,z4,z7]),(0,[z61,z216,z1,z2,z3,z4,z7]),(0,[z0,z44,z1,z57,z3,z4,z7]),(0,[z0,z99,z49,z2,z3,z4,z7]),(0,[z0,z166,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z223,z7]),(0,[z0,z1,z2,z3,z4,z682,z7]),(0,[z0,z1,z2,z3,z4,z7,z683])],[(1,[z68,z1,z2,z9,z4,z7]),(0,[z0,z1,z2,z3,z9,z4,z62]),(0,[z0,z1,z2,z9,z58,z4,z7]),(0,[z684,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z685,z3,z4,z7]),(0,[z0,z1,z2,z3,z686,z4,z7]),(1,[z0,z99,z2,z136,z4,z7]),(0,[z0,z1,z2,z3,z4,z687,z7]),(0,[z0,z1,z2,z688,z3,z4,z7]),(0,[z0,z689,z1,z2,z3,z4,z7])],[(0,[z0,z124,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z4,z690,z7]),(0,[z691,z0,z1,z2,z3,z4,z7]),(0,[z0,z10,z1,z2,z3,z27,z4])],[(0,[z0,z1,z2,z3,z4,z7,z692]),(0,[z0,z1,z14,z2,z3,z4,z11]),(0,[z0,z1,z693,z2,z3,z4,z7])],[(0,[z694,z0,z1,z2,z3,z4,z7]),(0,[z695,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z696,z2,z3,z4,z7]),(0,[z0,z697,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z698,z4,z7]),(0,[z0,z1,z2,z91,z3,z4,z7]),(0,[z0,z33,z1,z2,z91,z3,z7])],[(0,[z0,z1,z2,z23,z58,z4,z7]),(0,[z0,z1,z2,z699,z3,z4,z7]),(0,[z700,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z701,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z702,z7])],[(0,[z0,z1,z2,z3,z39,z4,z7]),(0,[z0,z1,z2,z703,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z62,z62]),(0,[z0,z1,z2,z3,z4,z140,z62]),(0,[z0,z1,z2,z3,z4,z110,z62]),(0,[z0,z69,z41,z2,z3,z4,z7]),(0,[z0,z33,z1,z2,z3,z70,z7]),(0,[z0,z704,z1,z2,z3,z4,z7])],[(0,[z52,z291,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z705,z7]),(0,[z706,z0,z1,z2,z3,z4,z7])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z52,z53,z295,z3,z4,z7]),(0,[z0,z1,z2,z3,z707,z7]),(0,[z0,z1,z2,z3,z708,z4]),(0,[z0,z15,z1,z2,z86,z62]),(0,[z0,z309,z2,z3,z70,z7])],[(0,[z0,z709,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z710,z7])],[(0,[z0,z1,z2,z135,z4,z205]),(0,[z0,z1,z2,z3,z711,z7]),(0,[z0,z1,z2,z257,z37,z7]),(0,[z0,z1,z2,z3,z365,z22]),(0,[z0,z1,z2,z4,z62,z712])],[(0,[z0,z1,z2,z713,z4,z7]),(0,[z0,z124,z1,z3,z4,z272]),(0,[z0,z49,z2,z24,z4,z11])],[(0,[z0,z1,z2,z3,z4,z714]),(0,[z68,z1,z2,z9,z4,z224]),(0,[z0,z214,z2,z9,z4,z7]),(0,[z0,z1,z715,z58,z4,z7])],[(0,[z0,z1,z2,z716,z4,z7]),(0,[z0,z1,z2,z3,z4,z198])],[(0,[z0,z1,z2,z717,z4,z7]),(0,[z0,z1,z2,z3,z4,z718]),(0,[z1,z2,z3,z540,z4,z62]),(0,[z353,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z91,z37,z11]),(1,[z0,z2,z719,z4,z7]),(0,[z0,z1,z2,z3,z70,z192]),(0,[z0,z10,z1,z2,z3,z449]),(1,[z0,z1,z3,z4,z720])],[(0,[z0,z1,z382,z3,z115,z7]),(0,[z0,z1,z2,z3,z4,z721]),(0,[z0,z166,z2,z3,z4,z81])]],
   [[],[(0,[z387,z1,z2,z9,z4,z7]),(0,[z0,z722,z1,z3,z4,z11]),(0,[z0,z48,z49,z24,z4,z7]),(1,[z0,z2,z3,z4,z723]),(0,[z0,z267,z1,z2,z4,z312])],[(0,[z0,z1,z2,z227,z4,z11]),(0,[z0,z33,z1,z2,z3,z424])],[(0,[z0,z1,z2,z3,z724,z7]),(0,[z0,z1,z2,z3,z725,z7]),(0,[z0,z1,z2,z3,z182,z62]),(0,[z361,z1,z2,z3,z4,z62]),(0,[z0,z111,z119,z3,z4,z7])],[(0,[z0,z1,z2,z726,z4,z7]),(0,[z0,z1,z2,z727,z4,z7]),(0,[z0,z43,z44,z281,z4,z7])],[(0,[z0,z1,z2,z3,z4,z373]),(0,[z0,z1,z2,z3,z4,z728]),(0,[z490,z1,z2,z9,z4,z7]),(0,[z0,z1,z2,z31,z4,z158]),(0,[z30,z1,z2,z3,z39,z158]),(0,[z0,z1,z2,z729,z4,z7])],[(0,[z0,z1,z2,z3,z730,z7]),(0,[z0,z1,z2,z3,z731,z4])],[(0,[z0,z383,z57,z3,z4,z7]),(0,[z0,z1,z2,z9,z365,z7]),(0,[z0,z1,z2,z3,z522,z80]),(0,[z0,z44,z1,z126,z4,z7]),(0,[z0,z49,z25,z24,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z103]),(0,[z72,z218,z2,z3,z4,z293]),(0,[z0,z383,z2,z3,z4,z198]),(0,[z0,z1,z2,z3,z732,z7]),(0,[z0,z49,z2,z719,z4,z7]),(0,[z0,z2,z3,z4,z723,z81]),(0,[z0,z1,z2,z3,z733,z34])],[(0,[z0,z1,z8,z3,z4,z62]),(0,[z0,z1,z734,z3,z4,z7]),(0,[z551,z1,z2,z23,z4,z7])],[(0,[z0,z1,z2,z3,z4,z735])],[(0,[z291,z1,z14,z3,z4,z11]),(0,[z0,z1,z2,z91,z439,z7]),(0,[z0,z69,z2,z3,z70,z62]),(0,[z0,z1,z2,z3,z4,z736])],[(0,[z0,z1,z2,z3,z4,z737]),(0,[z0,z2,z3,z4,z738,z7]),(0,[z0,z1,z2,z3,z4,z739]),(0,[z0,z15,z1,z2,z585,z7]),(0,[z0,z1,z2,z3,z740,z7])],[(0,[z0,z1,z2,z3,z75,z62]),(0,[z291,z1,z741,z3,z4,z7]),(0,[z419,z1,z2,z3,z4,z62]),(0,[z0,z41,z2,z3,z742,z7])],[(0,[z0,z121,z119,z3,z4,z7])],[(0,[z0,z1,z71,z3,z4,z62]),(0,[z0,z743,z1,z2,z3,z4]),(0,[z0,z744,z1,z2,z3,z4]),(0,[z0,z1,z2,z213,z4,z312])]],
   [[(0,[z0,z53,z2,z3,z4,z205]),(0,[z0,z1,z2,z3,z4,z745]),(0,[z0,z390,z1,z3,z4,z333]),(0,[z0,z1,z2,z3,z4,z746])],[(0,[z0,z218,z382,z3,z4,z7]),(0,[z72,z218,z2,z74,z4,z7]),(0,[z0,z1,z2,z3,z4,z747]),(0,[z291,z1,z14,z3,z4,z7]),(0,[z0,z48,z1,z3,z4,z7])],[(0,[z32,z218,z2,z3,z4,z7]),(0,[z68,z1,z2,z9,z4,z11]),(0,[z0,z99,z2,z136,z4,z11]),(0,[z0,z1,z2,z3,z80,z733])],[(0,[z0,z1,z2,z3,z4,z748]),(0,[z0,z1,z2,z3,z4,z749]),(0,[z68,z1,z2,z750,z4,z7]),(0,[z0,z751,z2,z3,z4,z11]),(0,[z0,z1,z2,z3,z4,z752])],[(0,[z0,z146,z1,z3,z4,z243])],[(0,[z0,z1,z2,z3,z4,z753]),(0,[z0,z1,z2,z754,z4,z7]),(0,[z0,z755,z2,z3,z4,z7])],[(0,[z78,z1,z2,z3,z40,z225]),(0,[z1,z2,z3,z39,z756,z7]),(0,[z0,z1,z2,z3,z757,z4]),(0,[z0,z1,z2,z3,z758,z7]),(0,[z0,z759,z2,z3,z4,z7]),(0,[z0,z760,z2,z3,z4,z7])],[(0,[z0,z1,z2,z761,z4,z7]),(0,[z0,z762,z2,z3,z4,z7]),(0,[z543,z1,z2,z3,z40,z7]),(0,[z0,z1,z2,z31,z4,z62]),(0,[z30,z1,z2,z3,z39,z62]),(0,[z1,z2,z3,z4,z62,z503]),(0,[z0,z105,z1,z310,z4,z7]),(0,[z0,z15,z1,z2,z86,z7])]],
   [[(0,[z0,z1,z2,z3,z115,z62]),(0,[z0,z53,z2,z227,z4,z7]),(0,[z0,z253,z2,z136,z4,z7]),(0,[z0,z2,z3,z4,z7,z763]),(0,[z0,z764,z1,z2,z3,z4]),(0,[z0,z48,z1,z136,z4,z7])],[(0,[z68,z1,z2,z9,z4,z104]),(0,[z0,z751,z2,z3,z4,z7]),(1,[z1,z2,z3,z4,z765]),(0,[z0,z1,z2,z3,z766,z4])],[],[(0,[z1,z2,z23,z750,z4,z7]),(0,[z0,z1,z2,z230,z3,z449])],[(0,[z0,z1,z2,z3,z7,z767]),(0,[z1,z2,z3,z4,z62,z347]),(0,[z0,z578,z2,z24,z4,z7])],[(0,[z0,z1,z2,z3,z4,z768]),(0,[z0,z769,z2,z3,z4,z62])],[(0,[z0,z1,z2,z3,z4,z770]),(0,[z0,z15,z1,z2,z132,z7])],[(0,[z0,z134,z382,z3,z4,z7]),(0,[z0,z1,z2,z3,z771,z7]),(0,[z0,z772,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z773,z4]),(0,[z0,z43,z44,z3,z4,z11]),(0,[z0,z1,z774,z3,z4,z7]),(0,[z0,z41,z2,z3,z60,z192])]],
   [[(0,[z0,z1,z775,z3,z4,z7]),(0,[z0,z2,z3,z4,z7,z776]),(0,[z551,z1,z2,z3,z39,z7]),(0,[z0,z13,z1,z2,z4,z62]),(0,[z0,z202,z2,z3,z4,z455]),(0,[z0,z1,z777,z3,z4,z7])],[(0,[z0,z1,z2,z184,z4,z62]),(0,[z0,z1,z2,z135,z21,z7]),(0,[z0,z1,z2,z3,z21,z11]),(0,[z52,z1,z295,z3,z4,z205]),(0,[z0,z1,z778,z3,z4,z7]),(0,[z0,z1,z2,z3,z7,z779]),(0,[z780,z1,z2,z3,z4,z7]),(0,[z0,z362,z2,z3,z70,z7]),(0,[z0,z781,z1,z2,z3,z4]),(0,[z0,z1,z2,z4,z7,z782])],[(0,[z0,z1,z8,z3,z4,z11]),(0,[z61,z1,z2,z3,z4,z765]),(0,[z0,z1,z2,z3,z182,z7]),(0,[z0,z783,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z784])],[(0,[z1,z2,z3,z4,z11,z765]),(0,[z0,z1,z2,z3,z4,z785]),(0,[z0,z33,z1,z2,z3,z642]),(0,[z0,z786,z2,z3,z4,z7]),(0,[z0,z214,z36,z2,z4,z7]),(0,[z0,z1,z2,z3,z27,z733])],[(0,[z0,z1,z2,z3,z4,z787]),(0,[z0,z1,z2,z788,z4,z7]),(0,[z0,z69,z2,z3,z70,z11])],[(0,[z0,z789,z1,z2,z3,z4]),(0,[z0,z168,z1,z3,z4,z62]),(0,[z0,z1,z2,z3,z790,z7])],[(0,[z0,z1,z2,z3,z4,z791]),(1,[z1,z2,z750,z4,z7]),(0,[z0,z1,z2,z230,z4,z418])],[(0,[z245,z1,z2,z23,z4,z22]),(0,[z0,z457,z2,z3,z4,z81]),(0,[z0,z1,z2,z3,z4,z792])]],
   [[(0,[z0,z1,z71,z3,z4,z11]),(0,[z0,z1,z8,z3,z4,z7]),(0,[z0,z1,z2,z3,z384,z22]),(0,[z78,z1,z2,z3,z40,z11])],[(0,[z52,z1,z295,z227,z4,z7]),(0,[z0,z1,z2,z3,z181,z62]),(0,[z0,z1,z2,z3,z4,z793]),(0,[z0,z1,z2,z3,z4,z794]),(0,[z0,z1,z3,z4,z7,z795]),(0,[z0,z1,z2,z3,z4,z796]),(0,[z0,z584,z1,z2,z4,z258])],[(0,[z0,z69,z2,z3,z70,z7]),(0,[z0,z33,z1,z2,z3,z520]),(0,[z0,z1,z2,z3,z27,z667])],[(0,[z0,z1,z2,z184,z75,z7]),(0,[z0,z1,z2,z3,z797,z4]),(0,[z0,z1,z2,z798,z4,z7]),(0,[z0,z1,z2,z3,z799,z4]),(0,[z0,z1,z2,z3,z800,z7]),(0,[z0,z1,z2,z3,z801,z4]),(0,[z0,z15,z1,z2,z802,z7])],[(0,[z0,z1,z2,z3,z75,z7]),(0,[z30,z1,z2,z350,z39,z7])],[(0,[z0,z1,z382,z3,z4,z62]),(0,[z0,z1,z803,z3,z4,z7]),(0,[z72,z218,z2,z3,z4,z5]),(0,[z592,z134,z2,z3,z4,z7]),(0,[z0,z383,z2,z3,z4,z62]),(0,[z0,z1,z2,z804,z4,z7]),(0,[z0,z805,z1,z3,z4,z7]),(0,[z0,z44,z578,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z806]),(0,[z0,z807,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z756,z7]),(0,[z0,z309,z1,z36,z2,z7]),(0,[z0,z1,z2,z3,z4,z808]),(0,[z0,z1,z2,z3,z4,z809]),(0,[z0,z1,z2,z4,z7,z810])],[(0,[z291,z1,z131,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z88]),(0,[z0,z811,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z812])]],
   [[(0,[z1,z2,z750,z9,z4,z7]),(0,[z30,z1,z2,z3,z39,z11]),(0,[z813,z1,z2,z3,z4,z7]),(0,[z0,z814,z1,z2,z3,z7]),(0,[z0,z13,z17,z1,z246,z7]),(0,[z0,z1,z3,z4,z231,z720])],[(0,[z0,z1,z2,z3,z115,z11]),(0,[z1,z2,z3,z4,z765,z62]),(0,[z148,z1,z2,z3,z4,z62])],[(0,[z0,z1,z2,z3,z815,z7]),(0,[z0,z1,z2,z3,z816,z7]),(0,[z345,z1,z2,z23,z4,z7]),(0,[z0,z1,z2,z126,z4,z11])],[(0,[z0,z15,z1,z2,z200,z7]),(0,[z0,z214,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z817,z4]),(0,[z0,z146,z1,z3,z4,z443])],[(0,[z133,z134,z2,z3,z4,z11]),(0,[z0,z1,z2,z4,z818,z7]),(0,[z245,z1,z2,z750,z4,z7]),(0,[z516,z1,z2,z23,z4,z7]),(0,[z361,z1,z2,z3,z39,z7]),(0,[z0,z1,z2,z3,z7,z129])],[(0,[z0,z1,z3,z4,z819,z7])],[(0,[z0,z1,z2,z74,z4,z293]),(0,[z0,z1,z2,z31,z4,z7]),(0,[z30,z1,z2,z3,z39,z7]),(0,[z0,z1,z2,z820,z4,z7]),(0,[z0,z1,z2,z3,z4,z821])],[(0,[z0,z1,z2,z3,z115,z7]),(0,[z0,z1,z382,z3,z75,z7]),(0,[z0,z53,z2,z3,z21,z7]),(0,[z0,z1,z2,z3,z4,z822]),(0,[z0,z1,z2,z3,z4,z823]),(0,[z0,z1,z2,z3,z223,z62]),(0,[z0,z1,z2,z3,z4,z824]),(0,[z0,z1,z2,z3,z4,z825])]],
   [[(0,[z0,z826,z1,z3,z4,z7]),(0,[z0,z43,z389,z3,z4,z7]),(0,[z1,z2,z3,z4,z607,z11]),(0,[z0,z1,z2,z4,z810,z156])],[(0,[z0,z1,z2,z827,z4,z7]),(0,[z0,z1,z2,z3,z4,z828]),(0,[z0,z1,z2,z3,z4,z829]),(0,[z0,z214,z2,z3,z80,z7])],[(0,[z0,z41,z2,z3,z60,z62]),(0,[z0,z1,z2,z830,z4,z7]),(0,[z0,z831,z2,z3,z4,z7]),(0,[z832,z1,z2,z3,z4,z7]),(0,[z0,z85,z1,z2,z91,z3])],[(0,[z0,z1,z2,z4,z833,z7]),(0,[z0,z1,z2,z3,z4,z834])],[(0,[z72,z218,z71,z3,z4,z7]),(0,[z0,z1,z2,z3,z835,z7]),(0,[z0,z1,z2,z3,z4,z836]),(0,[z0,z769,z2,z3,z4,z7]),(0,[z1,z2,z3,z661,z4,z62]),(0,[z0,z1,z2,z3,z11,z129]),(0,[z0,z1,z2,z3,z837,z7]),(0,[z838,z1,z2,z3,z4,z7]),(0,[z0,z2,z3,z60,z742,z7])],[(0,[z0,z1,z2,z3,z4,z839]),(0,[z0,z15,z85,z1,z2,z3]),(0,[z0,z1,z2,z4,z802,z7]),(1,[z0,z1,z2,z3,z733])],[(0,[z0,z1,z2,z3,z4,z840]),(0,[z0,z168,z1,z3,z4,z11]),(0,[z0,z1,z2,z3,z365,z62]),(0,[z0,z1,z2,z3,z841,z4]),(0,[z0,z2,z3,z4,z110,z723])],[(0,[z0,z842,z2,z3,z4,z7]),(0,[z0,z1,z2,z91,z3,z192]),(0,[z0,z13,z1,z2,z4,z7]),(0,[z0,z33,z1,z2,z3,z517])]],
   [[(0,[z0,z1,z2,z184,z4,z7]),(0,[z0,z1,z843,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z844]),(0,[z0,z1,z2,z3,z4,z845]),(0,[z78,z1,z2,z3,z756,z7]),(0,[z0,z111,z119,z3,z4,z11]),(0,[z0,z15,z1,z2,z235,z7]),(0,[z0,z1,z2,z3,z4,z720])],[(0,[z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z846]),(0,[z0,z1,z847,z3,z4,z7]),(0,[z0,z1,z2,z227,z4,z205]),(0,[z61,z1,z2,z3,z4,z11])],[(0,[z0,z1,z848,z3,z4,z7]),(0,[z0,z849,z1,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z850]),(0,[z0,z1,z2,z135,z181,z7]),(0,[z0,z1,z2,z3,z4,z851]),(0,[z0,z1,z2,z3,z4,z852]),(0,[z0,z105,z1,z426,z4,z7]),(0,[z0,z15,z367,z2,z86,z7])],[(0,[z0,z1,z2,z853,z4,z7])],[(0,[z0,z168,z1,z3,z4,z7]),(0,[z0,z1,z3,z4,z7,z854]),(0,[z0,z1,z2,z281,z4,z62]),(0,[z0,z105,z1,z58,z4,z62]),(0,[z0,z2,z3,z4,z723,z7]),(0,[z0,z1,z2,z3,z4,z855])],[(0,[z0,z1,z2,z254,z4,z482]),(0,[z285,z1,z2,z3,z4,z62]),(0,[z0,z856,z119,z3,z4,z7]),(0,[z0,z1,z2,z857,z4,z7]),(0,[z0,z13,z267,z1,z2,z4]),(0,[z0,z10,z1,z2,z129,z156])],[(0,[z0,z1,z2,z3,z858,z7]),(0,[z0,z99,z2,z279,z136,z4])],[(0,[z430,z1,z14,z3,z4,z7]),(0,[z0,z1,z2,z859,z4,z7]),(0,[z0,z2,z719,z136,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z181,z7]),(0,[z52,z1,z295,z3,z21,z7]),(0,[z1,z2,z3,z756,z40,z7]),(0,[z0,z1,z2,z31,z39,z7]),(0,[z0,z1,z2,z3,z4,z860]),(0,[z0,z544,z119,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z861]),(0,[z0,z15,z1,z2,z403,z7])],[(0,[z0,z1,z2,z3,z4,z862]),(0,[z0,z1,z2,z3,z4,z863]),(0,[z0,z1,z2,z3,z4,z864]),(0,[z0,z865,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z449,z110])],[(0,[z497,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z866,z4,z7]),(0,[z0,z1,z2,z3,z4,z192])],[(0,[z0,z1,z382,z184,z4,z7]),(0,[z0,z1,z2,z3,z4,z867]),(0,[z0,z168,z1,z136,z4,z7]),(0,[z0,z868,z1,z3,z4,z62]),(0,[z0,z41,z2,z3,z83,z7])],[(0,[z0,z1,z382,z3,z4,z7]),(0,[z0,z383,z2,z3,z4,z7]),(0,[z0,z1,z869,z3,z4,z7]),(0,[z0,z870,z1,z3,z4,z7]),(0,[z0,z1,z2,z3,z871,z4]),(0,[z0,z1,z2,z872,z4,z7]),(0,[z0,z214,z2,z3,z4,z11]),(0,[z0,z1,z3,z4,z11,z854]),(0,[z0,z1,z2,z3,z873,z7])],[(0,[z874,z218,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z875]),(0,[z0,z876,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z877,z7])],[(0,[z0,z1,z2,z878,z4,z7]),(0,[z216,z1,z2,z3,z4,z765]),(0,[z0,z48,z1,z3,z4,z11]),(0,[z1,z2,z3,z4,z510,z11]),(0,[z0,z1,z2,z3,z4,z879])],[(0,[z0,z1,z2,z3,z340,z140]),(0,[z1,z2,z3,z4,z512,z11]),(0,[z0,z527,z1,z2,z4,z429]),(0,[z0,z10,z1,z2,z473,z4]),(0,[z0,z10,z1,z2,z4,z156])]],
   [[(0,[z0,z1,z2,z3,z880,z7]),(0,[z0,z53,z2,z3,z4,z198]),(0,[z0,z881,z2,z3,z4,z7]),(0,[z1,z2,z3,z4,z765,z7]),(0,[z0,z1,z2,z3,z223,z11]),(1,[z0,z856,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z882]),(0,[z0,z10,z1,z2,z403,z4])],[(0,[z0,z13,z1,z2,z39,z7]),(0,[z0,z883,z1,z2,z3,z4]),(1,[z0,z1,z2,z802,z7])],[(0,[z0,z884,z1,z2,z3,z4]),(0,[z0,z214,z2,z3,z4,z7]),(0,[z0,z41,z214,z2,z3,z7])],[(0,[z0,z383,z2,z3,z181,z7]),(0,[z0,z1,z2,z3,z4,z158]),(0,[z0,z124,z1,z3,z4,z147]),(0,[z0,z41,z2,z3,z60,z11]),(1,[z0,z1,z2,z4,z810])],[(0,[z216,z1,z2,z3,z4,z62]),(0,[z0,z15,z1,z2,z86,z11]),(0,[z0,z762,z2,z3,z4,z11]),(0,[z885,z1,z2,z3,z4,z7]),(0,[z0,z309,z240,z1,z2,z3]),(0,[z0,z886,z1,z2,z4,z7]),(0,[z0,z10,z155,z1,z2,z156])],[(0,[z0,z1,z2,z887,z4,z7]),(0,[z0,z1,z3,z4,z720,z147])],[(0,[z0,z342,z119,z3,z4,z7]),(0,[z0,z1,z2,z3,z223,z7])],[(0,[z0,z1,z2,z3,z4,z348]),(0,[z0,z33,z1,z2,z3,z264])]],
   [[(0,[z0,z1,z2,z3,z4,z888]),(0,[z0,z1,z2,z3,z4,z889])],[(0,[z0,z1,z2,z3,z890,z7]),(0,[z0,z891,z2,z3,z4,z7]),(0,[z666,z1,z2,z3,z4,z11]),(0,[z589,z1,z2,z3,z4,z11]),(0,[z0,z41,z2,z3,z60,z7])],[(0,[z0,z1,z2,z4,z312,z62])],[(0,[z0,z1,z2,z74,z4,z5]),(0,[z0,z1,z2,z350,z4,z62])],[(0,[z672,z1,z2,z3,z4,z11]),(0,[z0,z105,z309,z1,z2,z7])],[(0,[z0,z1,z2,z3,z4,z892]),(0,[z0,z1,z2,z893,z4,z7]),(0,[z0,z1,z2,z3,z365,z7]),(0,[z245,z1,z2,z23,z4,z348]),(0,[z0,z309,z1,z2,z3,z62]),(0,[z113,z1,z2,z3,z4,z11]),(0,[z0,z856,z1,z3,z4,z7]),(0,[z0,z1,z2,z894,z4,z7]),(0,[z0,z895,z1,z3,z4,z7]),(0,[z0,z1,z2,z896,z4,z7])],[(0,[z0,z1,z2,z897,z4,z7]),(0,[z0,z1,z778,z3,z4,z11]),(0,[z0,z1,z2,z3,z898,z7])],[(0,[z0,z1,z899,z3,z4,z7]),(0,[z0,z1,z2,z135,z4,z62]),(0,[z0,z1,z2,z3,z4,z765]),(0,[z0,z1,z2,z3,z182,z11]),(0,[z0,z1,z2,z3,z900,z4]),(0,[z0,z343,z1,z3,z4,z188]),(0,[z0,z1,z901,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z21,z205]),(0,[z0,z1,z2,z3,z902,z7]),(0,[z0,z1,z2,z903,z4,z7]),(0,[z154,z1,z2,z3,z40,z7]),(0,[z0,z1,z2,z230,z4,z482]),(0,[z0,z41,z2,z3,z60,z96]),(0,[z0,z904,z2,z3,z4,z7])],[(0,[z0,z1,z71,z3,z4,z293]),(0,[z52,z1,z295,z3,z4,z198]),(0,[z0,z15,z1,z2,z322,z7]),(0,[z0,z44,z856,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z905]),(0,[z0,z1,z2,z3,z4,z906]),(0,[z56,z1,z2,z3,z4,z11])],[(0,[z0,z1,z2,z907,z4,z7]),(0,[z245,z1,z2,z23,z365,z7]),(0,[z0,z2,z3,z4,z62,z763]),(0,[z0,z549,z2,z3,z4,z337]),(0,[z0,z1,z2,z281,z4,z7]),(0,[z0,z1,z2,z3,z908,z7]),(0,[z0,z105,z1,z58,z4,z7]),(0,[z909,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z910]),(0,[z0,z214,z2,z3,z39,z7]),(0,[z0,z17,z1,z3,z246,z62])],[(0,[z0,z1,z2,z3,z4,z62]),(0,[z72,z874,z2,z3,z4,z7]),(0,[z0,z1,z57,z461,z4,z7]),(0,[z0,z10,z1,z2,z4,z429])],[(0,[z1,z2,z741,z3,z4,z7]),(0,[z199,z1,z2,z3,z4,z11]),(0,[z107,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z3,z4,z911])],[(0,[z0,z309,z1,z2,z23,z7]),(0,[z0,z1,z2,z3,z62,z767])]],
   [[(0,[z0,z1,z2,z74,z75,z7]),(0,[z0,z1,z2,z227,z21,z7]),(0,[z0,z1,z2,z3,z4,z224]),(0,[z0,z168,z1,z37,z4,z7]),(0,[z0,z2,z3,z4,z912,z62]),(0,[z0,z1,z2,z3,z4,z913]),(0,[z0,z914,z1,z2,z4,z7]),(0,[z0,z209,z2,z3,z60,z7])],[(0,[z0,z1,z2,z3,z75,z11]),(0,[z660,z1,z2,z3,z4,z62]),(0,[z0,z915,z1,z2,z3,z4]),(0,[z0,z1,z916,z3,z4,z7]),(0,[z0,z1,z2,z3,z566,z80]),(0,[z0,z202,z2,z3,z223,z110]),(0,[z0,z1,z2,z3,z4,z917])],[(0,[z0,z1,z71,z74,z4,z7]),(0,[z0,z868,z1,z3,z4,z7]),(0,[z0,z367,z2,z3,z4,z62]),(0,[z0,z1,z2,z42,z4,z172]),(0,[z0,z1,z2,z3,z4,z918]),(0,[z0,z1,z2,z4,z7,z919]),(0,[z0,z920,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z921,z7]),(0,[z245,z1,z2,z23,z4,z62]),(0,[z0,z922,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z279,z4]),(0,[z0,z33,z214,z2,z3,z7])],[(0,[z0,z1,z2,z750,z4,z7]),(0,[z0,z1,z2,z3,z923,z7]),(0,[z0,z1,z2,z31,z4,z54]),(0,[z30,z1,z2,z3,z39,z54]),(0,[z0,z1,z2,z3,z279,z182]),(0,[z0,z146,z1,z3,z4,z231]),(0,[z0,z155,z1,z2,z3,z7])],[(0,[z0,z1,z2,z3,z4,z924])],[(0,[z0,z99,z2,z719,z4,z7])],[(0,[z0,z925,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z926]),(0,[z0,z1,z2,z3,z4,z927]),(0,[z0,z33,z1,z2,z555,z3])]],
   [[(0,[z0,z1,z2,z3,z928,z7]),(0,[z1,z2,z3,z929,z4,z7])],[(0,[z0,z1,z2,z3,z930,z7]),(0,[z0,z1,z2,z931,z4,z7]),(0,[z32,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z449,z81]),(0,[z0,z932,z1,z2,z3,z4]),(0,[z0,z15,z214,z2,z86,z7])],[(0,[z0,z1,z2,z3,z4,z933]),(0,[z0,z1,z3,z4,z934,z7]),(0,[z0,z1,z935,z3,z4,z7]),(0,[z0,z18,z1,z3,z45,z7])],[(0,[z0,z1,z2,z74,z115,z7]),(0,[z0,z936,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z365,z348]),(0,[z0,z937,z2,z3,z4,z7]),(0,[z0,z1,z2,z31,z4,z11]),(0,[z0,z938,z1,z2,z3,z62]),(0,[z0,z1,z2,z3,z939,z11]),(0,[z1,z2,z3,z4,z593,z11])],[(0,[z0,z1,z2,z3,z940,z7]),(0,[z0,z941,z2,z3,z4,z7]),(0,[z0,z1,z3,z4,z62,z795]),(0,[z0,z942,z1,z3,z4,z7])],[(0,[z0,z943,z1,z3,z4,z7]),(0,[z0,z166,z327,z2,z3,z4])],[(0,[z291,z1,z14,z3,z4,z222]),(0,[z0,z309,z1,z2,z3,z11]),(0,[z0,z944,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z4,z945]),(0,[z0,z1,z2,z3,z7,z946])],[(0,[z0,z1,z2,z3,z4,z947]),(0,[z0,z1,z2,z3,z4,z54]),(0,[z180,z1,z2,z3,z4,z62]),(0,[z0,z13,z1,z2,z213,z4])]],
   [[(0,[z0,z948,z2,z3,z4,z7]),(0,[z0,z33,z1,z2,z3,z229])],[(0,[z0,z1,z2,z3,z4,z949]),(0,[z68,z1,z8,z9,z4,z7]),(0,[z0,z1,z36,z57,z4,z62]),(0,[z0,z1,z2,z3,z939,z7]),(0,[z0,z856,z2,z3,z4,z7]),(0,[z0,z15,z1,z2,z3,z192]),(0,[z0,z1,z2,z4,z312,z7]),(0,[z0,z17,z1,z3,z213,z246]),(0,[z0,z1,z2,z3,z213,z4])],[(0,[z0,z1,z2,z350,z4,z7]),(0,[z0,z1,z2,z91,z659,z7])],[],[(0,[z0,z1,z2,z3,z950,z7]),(0,[z0,z168,z1,z58,z4,z7]),(0,[z0,z13,z1,z2,z4,z11]),(0,[z0,z309,z1,z2,z3,z7])],[(0,[z0,z1,z2,z184,z4,z11]),(0,[z72,z218,z2,z3,z75,z7]),(0,[z0,z1,z951,z3,z4,z7]),(0,[z0,z1,z2,z952,z4,z7]),(1,[z1,z741,z3,z4,z7]),(0,[z0,z17,z1,z3,z246,z11]),(0,[z0,z267,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z953])],[(0,[z0,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z135,z4,z7]),(0,[z0,z1,z2,z4,z954,z7]),(0,[z0,z955,z1,z2,z3,z4]),(0,[z0,z956,z1,z2,z4,z62]),(0,[z0,z105,z1,z416,z4,z7])],[(0,[z0,z957,z1,z2,z4,z7]),(0,[z0,z489,z1,z3,z4,z243]),(0,[z0,z1,z2,z3,z62,z129]),(0,[z0,z1,z2,z3,z4,z958]),(0,[z0,z1,z3,z715,z4,z7]),(0,[z0,z146,z1,z3,z4,z720])]],
   [[(0,[z133,z134,z2,z3,z4,z116]),(0,[z0,z1,z57,z227,z4,z7]),(0,[z0,z1,z2,z42,z4,z437]),(0,[z0,z1,z2,z3,z4,z959]),(0,[z0,z69,z2,z3,z742,z7]),(0,[z0,z960,z1,z2,z3,z4])],[(0,[z0,z1,z2,z227,z4,z198]),(0,[z0,z1,z2,z3,z4,z961]),(0,[z0,z1,z2,z962,z4,z7]),(0,[z0,z671,z2,z136,z4,z7]),(0,[z0,z1,z2,z3,z963,z7])],[(0,[z0,z458,z1,z2,z3,z34]),(0,[z0,z26,z1,z3,z4,z188]),(0,[z0,z1,z2,z3,z4,z964])],[(0,[z0,z1,z2,z3,z4,z965]),(0,[z0,z1,z2,z3,z4,z966]),(0,[z0,z967,z2,z3,z4,z7]),(0,[z0,z17,z1,z3,z246,z7])],[(0,[z245,z1,z2,z23,z4,z11]),(0,[z0,z1,z2,z3,z4,z197])],[(0,[z0,z168,z1,z227,z4,z7]),(0,[z0,z1,z2,z3,z181,z11]),(0,[z0,z105,z1,z433,z4,z7]),(0,[z0,z1,z57,z715,z4,z7]),(0,[z0,z968,z1,z2,z4,z7]),(0,[z0,z1,z3,z4,z720,z7]),(0,[z0,z1,z2,z3,z802,z7])],[(0,[z0,z1,z71,z3,z4,z5]),(0,[z1,z874,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z969,z7]),(0,[z0,z1,z2,z3,z4,z970]),(1,[z0,z1,z3,z819,z7]),(0,[z0,z971,z2,z3,z4,z7])],[(0,[z0,z2,z3,z4,z912,z7]),(0,[z0,z1,z2,z972,z4,z7]),(0,[z0,z15,z85,z1,z2,z86]),(0,[z0,z1,z2,z3,z4,z810])]],
   [[(0,[z72,z218,z2,z3,z115,z7]),(0,[z0,z273,z1,z3,z246,z7]),(0,[z0,z17,z1,z3,z819,z7])],[(0,[z0,z1,z382,z3,z4,z11]),(0,[z0,z1,z2,z973,z4,z7]),(0,[z0,z383,z2,z3,z4,z11]),(0,[z0,z383,z2,z135,z4,z7]),(0,[z0,z367,z2,z3,z4,z7]),(0,[z0,z99,z2,z182,z136,z7]),(0,[z0,z1,z2,z3,z4,z974])],[(0,[z245,z1,z2,z23,z4,z7]),(0,[z975,z1,z2,z3,z4,z7])],[(0,[z0,z383,z295,z3,z4,z7]),(0,[z0,z1,z2,z3,z384,z7]),(0,[z30,z1,z2,z3,z756,z7]),(0,[z0,z99,z240,z2,z136,z4]),(0,[z0,z1,z2,z3,z4,z96]),(0,[z0,z1,z2,z230,z277,z4]),(0,[z0,z17,z1,z312,z246,z7])],[(0,[z0,z1,z2,z3,z976,z7]),(0,[z0,z1,z2,z977,z4,z7]),(0,[z32,z1,z295,z3,z4,z7]),(0,[z0,z1,z2,z350,z4,z158]),(0,[z0,z1,z2,z3,z4,z978]),(0,[z0,z584,z1,z2,z4,z156]),(0,[z0,z1,z2,z3,z979,z7]),(0,[z0,z2,z3,z719,z4,z7]),(0,[z0,z309,z1,z2,z3,z279]),(0,[z0,z980,z1,z3,z4,z7]),(0,[z981,z1,z2,z3,z4,z7]),(0,[z0,z982,z2,z3,z4,z7])],[(0,[z0,z1,z2,z983,z4,z7]),(0,[z169,z1,z2,z3,z4,z11])],[(0,[z0,z984,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z449,z62]),(0,[z0,z1,z2,z3,z742,z7])],[(0,[z0,z1,z2,z3,z115,z5]),(0,[z0,z383,z14,z3,z4,z7]),(0,[z0,z178,z44,z3,z4,z7]),(0,[z0,z390,z1,z3,z4,z231])]],
   [[(0,[z0,z1,z985,z3,z4,z7]),(0,[z0,z214,z2,z23,z4,z7]),(0,[z0,z155,z1,z2,z3,z62]),(0,[z0,z1,z2,z91,z7,z590])],[(0,[z72,z218,z2,z184,z4,z7]),(0,[z0,z986,z2,z3,z4,z7]),(0,[z0,z856,z111,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z987])],[(0,[z72,z218,z2,z3,z4,z7]),(0,[z0,z105,z383,z3,z4,z7]),(0,[z0,z1,z2,z988,z4,z7]),(0,[z291,z1,z14,z3,z4,z373]),(0,[z0,z938,z1,z2,z3,z7])],[(1,[z874,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z989,z4]),(0,[z0,z105,z214,z2,z4,z7]),(0,[z0,z1,z36,z4,z398,z7])],[(0,[z0,z53,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z990,z7]),(0,[z0,z1,z2,z3,z7,z733])],[(0,[z68,z168,z1,z9,z4,z7]),(0,[z0,z168,z1,z57,z4,z7]),(0,[z0,z1,z2,z3,z4,z991])],[(0,[z78,z1,z2,z3,z40,z88]),(0,[z637,z1,z2,z3,z40,z7]),(0,[z0,z18,z1,z3,z45,z62]),(0,[z0,z43,z44,z126,z4,z7]),(0,[z0,z1,z2,z3,z4,z992])],[(0,[z0,z1,z2,z3,z993,z62]),(0,[z0,z202,z2,z3,z4,z110]),(0,[z0,z202,z2,z3,z472,z4]),(0,[z0,z1,z2,z3,z27,z80])]],
   [[(0,[z0,z1,z36,z57,z4,z7]),(0,[z0,z1,z2,z3,z4,z994])],[(0,[z0,z1,z3,z45,z819,z7]),(0,[z0,z1,z2,z230,z4,z810])],[(0,[z0,z995,z1,z2,z3,z7]),(0,[z0,z996,z2,z3,z4,z7]),(0,[z0,z168,z1,z24,z4,z7]),(0,[z0,z1,z2,z3,z365,z11]),(0,[z0,z1,z2,z3,z4,z997])],[(0,[z0,z1,z2,z3,z998,z7]),(0,[z0,z1,z2,z3,z999,z7]),(0,[z0,z53,z2,z3,z181,z7]),(0,[z0,z2,z3,z1000,z4,z7]),(0,[z0,z1,z2,z3,z4,z1001]),(0,[z0,z1,z2,z23,z365,z7]),(0,[z0,z1,z2,z3,z898,z11]),(0,[z0,z1,z2,z3,z1002,z7]),(0,[z0,z1,z2,z3,z4,z1003]),(0,[z0,z166,z2,z3,z4,z723]),(0,[z1004,z1,z2,z3,z4,z7])],[(0,[z0,z1,z1005,z3,z4,z7]),(0,[z0,z549,z2,z3,z4,z110]),(0,[z0,z1,z3,z819,z246,z7])],[(0,[z0,z1,z2,z3,z1006,z7]),(0,[z72,z218,z382,z3,z4,z7]),(0,[z0,z956,z1,z2,z4,z7]),(0,[z284,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z1007,z4,z7]),(0,[z0,z1,z2,z1008,z4,z7]),(0,[z0,z1009,z1,z2,z3,z4])],[(0,[z0,z1,z2,z1010,z4,z7]),(0,[z0,z1,z2,z3,z27,z163]),(0,[z0,z202,z2,z3,z4,z723])],[(0,[z0,z49,z2,z24,z4,z62]),(0,[z0,z1011,z1,z2,z3,z7])]],
   [[(0,[z0,z1012,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z21,z198]),(0,[z0,z1,z2,z281,z4,z11]),(0,[z0,z105,z1,z58,z4,z11]),(0,[z0,z1,z2,z3,z4,z1013]),(0,[z0,z1,z2,z3,z60,z192]),(0,[z0,z1,z2,z3,z1014,z7])],[(0,[z0,z1,z2,z74,z4,z62]),(0,[z0,z1015,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z384,z348]),(0,[z0,z1,z2,z3,z1016,z7])],[(0,[z0,z1,z2,z3,z75,z293]),(0,[z487,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z1017,z7]),(0,[z0,z313,z33,z1,z2,z3])],[(0,[z0,z1,z2,z3,z4,z1018]),(0,[z52,z352,z1,z3,z4,z7]),(0,[z0,z1,z2,z3,z1019,z7]),(0,[z0,z145,z2,z136,z4,z7])],[(0,[z0,z1,z2,z3,z1020,z4]),(0,[z689,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z3,z1021,z7])],[(0,[z52,z1,z295,z3,z4,z7]),(0,[z0,z1022,z2,z3,z4,z7]),(0,[z1,z741,z295,z3,z4,z7]),(0,[z0,z168,z15,z1,z4,z7]),(0,[z0,z1,z1023,z3,z4,z7])],[(0,[z0,z1,z2,z227,z4,z62])],[(0,[z0,z214,z2,z3,z40,z7]),(0,[z0,z1,z2,z3,z1024,z62]),(0,[z0,z1,z2,z3,z449,z11]),(0,[z0,z1,z2,z3,z7,z1025]),(0,[z0,z1,z2,z3,z4,z1026]),(0,[z1027,z1,z2,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z1028,z4,z7]),(0,[z344,z1,z2,z3,z39,z7]),(0,[z0,z1029,z2,z3,z4,z7])],[(0,[z1,z2,z3,z4,z62,z664]),(0,[z0,z155,z1,z2,z3,z11]),(0,[z0,z1,z2,z37,z802,z7])],[(0,[z0,z309,z1,z2,z9,z7]),(0,[z0,z1030,z1,z2,z3,z4]),(0,[z0,z48,z1,z24,z4,z7]),(0,[z1031,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1032]),(0,[z0,z26,z1,z3,z4,z720])],[(0,[z0,z1033,z1,z2,z3,z4]),(1,[z0,z2,z3,z742,z7])],[(0,[z134,z874,z2,z3,z4,z7]),(0,[z52,z1,z295,z3,z181,z7]),(0,[z0,z185,z2,z3,z70,z7]),(0,[z551,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z4,z1034])],[(0,[z0,z1,z2,z3,z115,z293]),(0,[z0,z1,z2,z3,z449,z7]),(0,[z0,z1,z1035,z3,z4,z7])],[(0,[z1,z14,z741,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1036]),(0,[z0,z1,z25,z3,z4,z62]),(0,[z1,z2,z331,z3,z4,z62]),(0,[z0,z43,z856,z3,z4,z7]),(0,[z0,z1037,z1,z2,z3,z4]),(0,[z0,z209,z2,z3,z4,z110])],[(0,[z0,z1,z2,z3,z4,z1038]),(0,[z0,z1,z1039,z3,z4,z7]),(0,[z0,z105,z1,z227,z4,z7]),(0,[z0,z1,z2,z4,z7,z712]),(0,[z0,z1,z2,z3,z384,z62]),(0,[z0,z1,z2,z3,z1040,z7]),(0,[z0,z1,z2,z3,z4,z225]),(0,[z0,z18,z1,z3,z45,z11]),(0,[z0,z1,z2,z3,z11,z1025]),(0,[z0,z402,z119,z3,z4,z7]),(0,[z0,z1,z2,z3,z1041,z7]),(0,[z0,z1,z1042,z3,z4,z7])]],
   [[(0,[z0,z1,z1043,z3,z4,z7]),(0,[z52,z383,z295,z3,z4,z7]),(0,[z1,z2,z3,z756,z4,z7]),(0,[z0,z1,z2,z350,z4,z54]),(0,[z0,z457,z2,z3,z4,z149]),(0,[z0,z276,z1,z2,z3,z385]),(0,[z0,z26,z1,z595,z3,z4]),(0,[z1044,z1,z2,z3,z4,z7])],[(0,[z0,z1045,z1,z2,z4,z7]),(0,[z0,z1,z2,z3,z4,z1046])],[(0,[z0,z1047,z1,z3,z4,z7]),(0,[z0,z1,z2,z3,z1048,z7])],[(0,[z0,z1,z2,z3,z4,z1049]),(0,[z0,z944,z1,z2,z3,z11]),(0,[z0,z1050,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1051]),(0,[z0,z105,z1,z715,z4,z7])],[(0,[z0,z399,z2,z3,z4,z455]),(0,[z352,z1,z2,z3,z4,z62])],[(0,[z0,z1,z2,z184,z4,z293]),(0,[z72,z218,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z993,z7]),(0,[z68,z1,z2,z9,z4,z62]),(0,[z0,z99,z2,z136,z4,z62]),(0,[z0,z1,z2,z4,z312,z11]),(0,[z0,z1,z2,z3,z4,z1052]),(0,[z0,z1,z2,z3,z1053,z7]),(0,[z0,z15,z1,z2,z547,z7]),(0,[z0,z1,z2,z3,z1054,z7])],[(0,[z0,z1,z2,z3,z4,z293]),(0,[z0,z1,z2,z350,z4,z11]),(0,[z0,z1,z2,z3,z4,z1055]),(0,[z0,z85,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z2,z1056,z4,z7]),(0,[z0,z53,z2,z3,z4,z62]),(0,[z0,z1,z2,z1057,z4,z7]),(0,[z0,z1,z2,z3,z4,z1058]),(0,[z0,z458,z1,z2,z3,z162]),(0,[z0,z33,z1,z2,z3,z733])],[(0,[z0,z1,z2,z3,z1059,z7]),(0,[z0,z1,z2,z3,z4,z1060])],[(0,[z0,z1,z2,z74,z4,z11]),(0,[z0,z1,z2,z3,z4,z1061]),(0,[z0,z1,z36,z562,z4,z7])],[(0,[z0,z1062,z1,z2,z3,z7]),(0,[z0,z1,z2,z135,z4,z11]),(0,[z582,z1,z2,z3,z4,z62])],[(0,[z133,z874,z2,z3,z4,z7]),(0,[z0,z1063,z1,z2,z3,z4]),(0,[z0,z99,z309,z2,z136,z7])],[(0,[z0,z1,z2,z3,z4,z205]),(0,[z16,z1,z2,z3,z4,z62]),(0,[z0,z41,z2,z3,z491,z7]),(0,[z1064,z1,z2,z3,z4,z7])],[(0,[z133,z134,z2,z3,z4,z103]),(0,[z0,z1,z2,z3,z4,z1065]),(0,[z0,z1,z2,z3,z4,z1066]),(0,[z0,z995,z1,z2,z3,z62]),(0,[z0,z49,z2,z24,z4,z7]),(0,[z0,z26,z1,z3,z4,z147])],[(0,[z0,z1,z2,z4,z7,z1067]),(0,[z0,z10,z1,z2,z4,z810])]],
   [[(0,[z0,z1,z2,z74,z4,z7]),(0,[z0,z1,z2,z1068,z4,z7]),(0,[z0,z1,z2,z3,z4,z1069]),(0,[z0,z1,z1070,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1071]),(0,[z0,z1,z2,z3,z4,z1072]),(0,[z0,z1073,z1,z2,z3,z7]),(0,[z0,z202,z2,z3,z449,z110]),(0,[z0,z1074,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z181,z198]),(0,[z0,z1075,z1,z2,z3,z4]),(0,[z0,z233,z2,z3,z60,z7]),(0,[z0,z608,z2,z3,z4,z323]),(0,[z0,z1,z119,z126,z4,z7]),(0,[z0,z309,z41,z2,z3,z7]),(0,[z0,z1,z2,z3,z4,z1076]),(0,[z0,z1,z2,z3,z4,z1077]),(0,[z0,z1,z2,z91,z37,z7])],[(0,[z0,z1,z382,z3,z4,z293]),(0,[z0,z1,z2,z3,z4,z1078])],[(0,[z0,z1,z741,z3,z4,z7]),(0,[z0,z43,z44,z3,z4,z62]),(0,[z1079,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z230,z4,z172])],[(0,[z0,z1,z2,z3,z181,z205]),(0,[z1,z2,z3,z750,z4,z7]),(0,[z0,z722,z1,z3,z4,z7])],[(0,[z0,z1,z2,z227,z4,z7]),(0,[z0,z1,z2,z3,z21,z62]),(0,[z0,z69,z214,z2,z3,z7])],[(0,[z0,z1,z2,z3,z1024,z7]),(0,[z0,z421,z119,z3,z4,z7]),(0,[z0,z1080,z2,z3,z4,z62]),(0,[z0,z367,z2,z3,z4,z11]),(0,[z0,z166,z2,z3,z4,z323]),(0,[z0,z1081,z1,z2,z4,z7]),(0,[z0,z1082,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z75,z5]),(0,[z0,z1,z2,z3,z4,z1083]),(0,[z0,z1,z25,z3,z4,z11]),(0,[z0,z240,z1,z2,z3,z4])]],
   [[(0,[z0,z383,z2,z3,z4,z205]),(0,[z0,z1084,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z104]),(0,[z0,z1,z2,z3,z384,z11]),(0,[z1,z2,z400,z3,z4,z62]),(0,[z341,z1,z2,z3,z4,z11]),(0,[z0,z240,z1,z2,z3,z182]),(0,[z0,z1,z2,z3,z819,z7])],[(0,[z0,z1,z2,z3,z4,z1085]),(0,[z0,z1,z2,z3,z1086,z7]),(0,[z52,z1,z295,z3,z4,z62]),(0,[z1,z2,z405,z3,z4,z62]),(0,[z0,z1,z2,z3,z4,z1087]),(0,[z0,z1,z2,z3,z27,z643]),(0,[z0,z155,z1,z2,z230,z3])],[(0,[z0,z1,z2,z3,z4,z116]),(0,[z0,z1,z2,z715,z4,z7])],[(0,[z0,z1,z382,z74,z4,z7]),(0,[z0,z1,z2,z3,z4,z1088]),(0,[z0,z984,z2,z3,z4,z11]),(0,[z0,z1,z2,z1089,z4,z7]),(1,[z0,z1,z715,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1090]),(0,[z0,z1,z2,z227,z181,z7]),(0,[z0,z1,z2,z1091,z4,z7]),(0,[z78,z1,z2,z3,z40,z62]),(0,[z0,z1,z2,z3,z1092,z62]),(0,[z0,z1093,z2,z3,z4,z7])],[(0,[z0,z1,z1094,z3,z4,z7]),(0,[z0,z1,z1095,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1096]),(0,[z0,z1,z2,z3,z27,z140]),(0,[z0,z1,z25,z3,z4,z7])],[(0,[z0,z1,z2,z31,z40,z7]),(0,[z1,z2,z3,z4,z1097,z7]),(0,[z0,z1,z2,z3,z1098,z7])],[(0,[z72,z218,z2,z3,z4,z11])]],
   [[(0,[z0,z1,z2,z3,z1099,z7]),(0,[z0,z383,z2,z227,z4,z7]),(0,[z0,z1100,z1,z3,z4,z7]),(0,[z0,z1,z2,z1101,z4,z7]),(0,[z0,z1,z36,z715,z4,z7])],[(0,[z0,z53,z2,z3,z4,z11]),(0,[z0,z53,z2,z135,z4,z7]),(0,[z0,z2,z3,z4,z1102,z7]),(0,[z0,z1,z2,z3,z1103,z7]),(0,[z0,z1,z2,z37,z287,z7]),(0,[z0,z1,z2,z3,z1104,z7])],[(0,[z0,z1105,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z1106,z7]),(0,[z0,z1,z2,z3,z4,z1107]),(0,[z0,z1,z2,z3,z4,z1108]),(0,[z0,z1,z3,z4,z1109,z7])],[(0,[z0,z1110,z1,z2,z3,z4])],[(0,[z245,z1,z2,z23,z384,z7]),(0,[z605,z1,z2,z3,z4,z62]),(0,[z0,z105,z1,z114,z4,z7]),(0,[z0,z1,z2,z3,z4,z1111]),(0,[z0,z1,z2,z3,z4,z1112])],[(0,[z68,z1,z2,z9,z4,z7]),(0,[z0,z1,z36,z57,z4,z11]),(0,[z0,z99,z2,z136,z4,z7])],[(0,[z0,z1,z71,z3,z75,z7]),(0,[z0,z1113,z2,z3,z4,z7]),(0,[z0,z1,z2,z126,z4,z62]),(0,[z0,z1,z2,z3,z522,z432]),(0,[z0,z309,z214,z2,z3,z7]),(0,[z0,z1,z2,z3,z1114,z4])],[(0,[z0,z1115,z1,z2,z3,z7]),(0,[z0,z13,z1,z2,z40,z7]),(0,[z516,z1,z2,z3,z4,z62]),(0,[z0,z1116,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z7,z1117])]],
   [[(0,[z133,z134,z2,z3,z4,z62])],[(0,[z0,z1,z2,z3,z4,z1118]),(0,[z0,z874,z2,z3,z4,z7]),(0,[z0,z1,z2,z1119,z4,z7]),(0,[z0,z1,z2,z3,z4,z1120])],[(0,[z0,z1121,z1,z3,z4,z7]),(0,[z0,z709,z2,z3,z4,z62]),(0,[z0,z1,z2,z802,z86,z7]),(0,[z0,z1,z2,z3,z80,z249])],[(0,[z0,z1,z2,z184,z4,z5]),(0,[z0,z1,z2,z1122,z4,z7]),(0,[z1123,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1124])],[(0,[z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1125,z7]),(0,[z0,z1,z2,z3,z4,z1126]),(0,[z0,z1,z2,z3,z7,z1127]),(0,[z0,z1,z2,z4,z172,z810])],[(0,[z0,z1,z2,z3,z1128,z4]),(0,[z0,z1,z2,z3,z4,z22]),(0,[z0,z1129,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1130]),(0,[z0,z1,z2,z3,z4,z1131])]],
   [[(0,[z0,z1,z2,z3,z4,z1132]),(0,[z0,z33,z1,z2,z3,z34])],[(0,[z0,z1,z71,z3,z115,z7]),(0,[z0,z1,z2,z3,z1133,z7]),(0,[z0,z1,z445,z57,z4,z7]),(0,[z0,z1,z2,z3,z4,z1134]),(0,[z0,z1,z2,z719,z4,z7]),(0,[z0,z1,z2,z4,z1135,z7])],[(0,[z52,z1,z295,z135,z4,z7]),(0,[z52,z1,z295,z3,z4,z11]),(0,[z0,z1,z2,z1136,z4,z7]),(0,[z0,z250,z1,z3,z45,z7]),(0,[z0,z43,z44,z3,z4,z7]),(0,[z0,z2,z3,z742,z70,z7])],[(0,[z0,z1,z2,z1137,z4,z7]),(0,[z0,z1138,z2,z3,z4,z7]),(0,[z359,z1,z2,z9,z4,z7]),(0,[z0,z2,z24,z719,z4,z7]),(0,[z0,z1139,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z21,z7]),(0,[z0,z1,z2,z3,z4,z1140]),(0,[z0,z111,z119,z3,z4,z62]),(0,[z0,z1,z2,z3,z4,z723]),(0,[z0,z1,z2,z3,z4,z1141])],[(0,[z0,z1,z1142,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1143]),(0,[z0,z1144,z2,z3,z4,z7]),(0,[z0,z1,z1145,z3,z4,z7]),(0,[z0,z1080,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1146]),(0,[z0,z1,z2,z91,z37,z62]),(0,[z0,z2,z3,z4,z11,z776]),(0,[z0,z1,z2,z3,z4,z1147])],[(0,[z1,z2,z3,z4,z11,z62]),(0,[z0,z1,z2,z3,z4,z1148]),(0,[z0,z1,z2,z3,z4,z1149]),(0,[z0,z15,z1,z2,z197,z86])],[(0,[z0,z1,z382,z3,z4,z5]),(0,[z0,z2,z3,z1150,z4,z7])]],
   [[(0,[z52,z1,z741,z3,z4,z7]),(1,[z1,z2,z3,z756,z7]),(0,[z30,z1,z2,z31,z39,z7]),(0,[z0,z1,z2,z3,z4,z1151]),(0,[z0,z1,z2,z3,z4,z1152]),(0,[z0,z1,z2,z3,z4,z733])],[(0,[z0,z1,z2,z1153,z4,z7]),(0,[z0,z1,z2,z3,z4,z222]),(0,[z0,z33,z1,z2,z3,z354]),(0,[z0,z10,z155,z1,z2,z3])],[(0,[z0,z1,z71,z184,z4,z7]),(0,[z0,z1154,z1,z2,z3,z4])],[(0,[z0,z1,z71,z3,z4,z7]),(0,[z0,z1155,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z1092,z7]),(0,[z0,z157,z2,z24,z4,z7]),(0,[z0,z1,z422,z57,z4,z7]),(0,[z78,z1,z2,z3,z40,z7]),(0,[z483,z1,z2,z3,z4,z62]),(0,[z0,z49,z2,z624,z4,z7])],[(0,[z0,z1,z2,z3,z1156,z7])],[(0,[z0,z1157,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1158]),(0,[z492,z1,z2,z3,z4,z62]),(0,[z0,z2,z3,z4,z738,z62])],[],[(0,[z0,z383,z2,z3,z21,z7]),(0,[z0,z1047,z1,z3,z4,z11]),(0,[z0,z1,z2,z3,z4,z1159])]],
   [[(0,[z0,z1,z2,z3,z1160,z4]),(0,[z0,z1,z2,z3,z4,z1161]),(0,[z1,z2,z3,z4,z1162,z7])],[(0,[z1,z2,z3,z4,z62,z226]),(0,[z0,z2,z3,z4,z742,z7]),(0,[z0,z1,z2,z91,z802,z7])],[(0,[z291,z1,z14,z3,z4,z62]),(0,[z0,z48,z1,z3,z4,z62]),(0,[z0,z33,z1,z2,z3,z385]),(0,[z0,z1,z2,z1163,z4,z7]),(0,[z0,z1,z2,z3,z4,z1164])],[(0,[z0,z1,z2,z184,z115,z7]),(0,[z0,z1,z2,z3,z4,z1165]),(0,[z581,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z3,z1166,z7])],[(0,[z0,z1,z2,z3,z4,z1167]),(0,[z1168,z1,z2,z3,z4,z7]),(0,[z0,z17,z267,z1,z3,z246]),(0,[z0,z18,z1,z3,z819,z7])],[(0,[z0,z1169,z1,z2,z3,z4]),(0,[z0,z1,z2,z126,z4,z7])],[(0,[z1170,z1,z2,z3,z4,z7]),(0,[z0,z494,z2,z3,z4,z81]),(0,[z0,z1,z2,z3,z4,z1171])],[(0,[z133,z134,z2,z3,z4,z7]),(0,[z0,z1,z2,z135,z4,z198]),(0,[z407,z1,z2,z3,z4,z11])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 530) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 530).take 536) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1066).take 138) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1204)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [530, 536, 138] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 123).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 123).take 128).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 251).take 5).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [123, 128, 5] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

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

end PEqualNP.Outside.L_meta_39143

theorem PEqualNP.Outside.L_meta_39143 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4205494400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4205494400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39143.solve