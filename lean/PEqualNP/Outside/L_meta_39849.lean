import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39849

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
  Nat.testBit (4008373984 * 2 ^ 32 + 4008364160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00014c386421586e#64 ++ 0x8000530e1908561b#64 ++ 0xad27dc78ec63f8ff#64 ++ 0xeb49f71e3b18fe3f#64 : BitVec 256),
   (0x044b058b018cc3b4#64 ++ 0xc112c162c06330ed#64 ++ 0xfedb278f139ccfff#64 ++ 0xffb6c9e3c4e733ff#64 : BitVec 256),
   (0x13143805bc170d1b#64 ++ 0x04c50e016f05c346#64 ++ 0xd71c380ffc1f0f1f#64 ++ 0xb5c70e03ff07c3c7#64 : BitVec 256),
   (0x0ba03ad01ee00ec0#64 ++ 0x02e80eb407b803b0#64 ++ 0xfbe03ff01fe00fe3#64 ++ 0x7ef80ffc07f803f8#64 : BitVec 256),
   (0x03fe80001b5aa000#64 ++ 0x00ffa00006d6a800#64 ++ 0x9fffc0001ffff002#64 ++ 0xe7fff00007fffc00#64 : BitVec 256),
   (0x23fff76ec0000000#64 ++ 0x08fffddbb0000000#64 ++ 0xe3ffffffe0000001#64 ++ 0xf8fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [10, 9]⟩, ⟨.or, [13, 4]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x8d27c0000c63f002 0xe349f0000318fc00

def z1 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0xad27dc78ec63f8ff 0xeb49f71e3b18fe3f

def z2 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x9fffc0001ffff002 0xe7fff00007fffc00

def z3 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0xfedb278f139ccfff 0xffb6c9e3c4e733ff

def z4 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0xfbe03ff01fe00fe3 0x7ef80ffc07f803f8

def z5 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0x5218380ff01c0f1d 0x14860e03fc0703c7

def z6 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0xe3ffffffe0000001 0xf8fffffff8000000

def z7 : W := mkw 0x13143804bc130c0b 0x04c50e012f04c302 0x85041808ec03081f 0xa14106023b00c207

def z8 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0xd71c380ffc1f0f1f 0xb5c70e03ff07c3c7

def z9 : W := mkw 0x0bfeb2c01bdaa680 0x02ffacb006f6a9a0 0xdfffe3801ffff702 0xf7fff8e007fffdc0

def z10 : W := mkw 0x030038101c200c40 0x00c00e0407080310 0xfb203c701c600fe3 0x7ec80f1c071803f8

def z11 : W := mkw 0x0ba17ef85ee05ee4 0x82e85fbe17b817b9 0xfbe3fff01fe0ffe3 0x7ef8fffc07f83ff8

def z12 : W := mkw 0x000000001b5aa000 0x0000000006d6a800 0x1c0000001ffff002 0x0700000007fffc00

def z13 : W := mkw 0x2001776ec0000000 0x08005ddbb0000000 0x60003fffe0000001 0x18000ffff8000000

def z14 : W := mkw 0x0001040800004024 0x8000410200001009 0xac0304080000c8ff 0xeb00c1020000323f

def z15 : W := mkw 0x000144286001502e 0x8000510a1800540b 0x0407c008e003f01c 0x8101f0023800fc07

def z16 : W := mkw 0x07ff858b018cc3b4 0xc1ffe162c06330ed 0xffffe78f139ccfff 0xfffff9e3c4e733ff

def z17 : W := mkw 0x1bb43ad4bef30ecb 0x06ed0eb52fbcc3b2 0xfbe43ff0ffe30fe3 0x7ef90ffc3ff8c3f8

def z18 : W := mkw 0x13fffc3dff7ffd7f 0x84ffff0f7fdfff5f 0xfffffc7fffffffff 0xffffff1fffffffff

def z19 : W := mkw 0x000048306421184a 0x0000120c19084612 0x0124d870ec633000 0x0049361c3b18cc00

def z20 : W := mkw 0x044b4dbb65addbfe 0xc112d36ed96b76ff 0xffffffffffffffff 0xffffffffffffffff

def z21 : W := mkw 0x044a0081018cc3b4 0xc1128020406330ed 0x9edb0000139ccffe 0xe7b6c00004e733ff

def z22 : W := mkw 0x00ea80001b5aa000 0x003aa00006d6a800 0x1ce3c0001ffff002 0x4738f00007fffc00

def z23 : W := mkw 0x10003805a4050d1b 0x04000e0169014346 0x4000380fe0000f1d 0x10000e03f80003c7

def z24 : W := mkw 0x10140005a017011b 0x040500016805c046 0x041c000fe01f001c 0x81070003f807c007

def z25 : W := mkw 0x0bfebad01ee00ec0 0x02ffaeb407b803b0 0xfbfffff01fe00fe3 0xfefffffc07f803f8

def z26 : W := mkw 0x0000000000000000 0x0000000000000000 0x0823c0000060f000 0x4208f00000183c00

def z27 : W := mkw 0x0000000000000000 0x0000000000000000 0x8127c00000000000 0xe049f00000000000

def z28 : W := mkw 0x000008102421184a 0x0000020409084612 0x000000000c633000 0x000000000318cc00

def z29 : W := mkw 0x23ffff6ee401080a 0x08ffffdbb9004202 0xe7ffffffec03081f 0xf9fffffffb00c207

def z30 : W := mkw 0x27fff7efc18cc3b4 0xc9fffdfbf06330ed 0xfffffffff39ccfff 0xfffffffffce733ff

def z31 : W := mkw 0x07fe80811bdee3b4 0xc1ffa02046f7b8ed 0x9fffc0001ffffffe 0xe7fff00007ffffff

def z32 : W := mkw 0x03a17e786421586e 0x80e85f9e1908561b 0xefe7fff8ec63f8ff 0xfbf9fffe3b18fe3f

def z33 : W := mkw 0x000144286001502e 0x8000510a1800540b 0xa527dc78e003f01d 0xe949f71e3800fc07

def z34 : W := mkw 0x044b058a0188c2a4 0xc112c162806230a9 0xeadb278f0380c0e1 0xfab6c9e3c0e03038

def z35 : W := mkw 0x080032c000800680 0x02000cb0002001a0 0x4000238000000700 0x100008e0000001c0

def z36 : W := mkw 0x1015442de017513f 0x8405510b7805d44f 0x041fc00fe01ff01c 0x8107f003f807fc07

def z37 : W := mkw 0x0000000000000000 0x0000000000000000 0x9ac0000013800002 0x66b0000004e00000

def z38 : W := mkw 0x10143805a4170d1b 0x04050e016905c346 0x441c380fe01f0f1d 0x91070e03f807c3c7

def z39 : W := mkw 0x23fff76edb5aa000 0x08fffddbb6d6a800 0xfffffffffffff003 0xfffffffffffffc00

def z40 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0x2927dc70ec63f0e0 0x4a49f71c3b18fc38

def z41 : W := mkw 0x000008002401080a 0x0000020009004202 0x85041808ec03081f 0xa14106023b00c207

def z42 : W := mkw 0x044a0183018c8390 0x41128060c06320e4 0xd6d8238f139c0f1f 0xb5b608e3c4e703c7

def z43 : W := mkw 0x0401058b008443b4 0xc1004162c02110ed 0x6000278f00000ffd 0x180009e3c00003ff

def z44 : W := mkw 0x03fe80011b5ea110 0x00ffa00046d7a844 0xdfffe00f1fffff1f 0xf7fff803c7ffffc7

def z45 : W := mkw 0x080008901ee00ec0 0x0200022407b803b0 0xfac027801fe00fe3 0x7eb009e007f803f8

def z46 : W := mkw 0x2bfffffec4a00ec0 0x0affffffb12803b0 0xe3ffffffe0000fe1 0xf8fffffff80003f8

def z47 : W := mkw 0x2ba17ffedee00ec0 0x0ae85fffb7b803b0 0xfbe03fffffe00fe3 0x7ef80ffffff803f8

def z48 : W := mkw 0x0000000000000000 0x0000000000000000 0xd200200010000f03 0x34800800040003c0

def z49 : W := mkw 0x044b452b610dd13e 0xc112d14ad843744f 0x041fc00fe01ff01c 0x8107f003f807fc07

def z50 : W := mkw 0x0ba032c01ac00680 0x02e80cb006b001a0 0x52c0238013800700 0x14b008e004e001c0

def z51 : W := mkw 0x03fe800000000000 0x00ffa00000000000 0x83ffc00000000000 0xe0fff00000000000

def z52 : W := mkw 0x00014c386421184a 0x0000530e19084612 0xa127dc78ec633001 0xe849f71e3b18cc00

def z53 : W := mkw 0x100000012017011b 0x040000004805c046 0x04000000001f001c 0x010000000007c007

def z54 : W := mkw 0x03a038001e400c00 0x00e80e0007900300 0xdbe038001fe00f03 0x76f80e0007f803c0

def z55 : W := mkw 0x0000008000800280 0x00000020002000a0 0xfac0278013800fe3 0x7eb009e004e003f8

def z56 : W := mkw 0x0ba03a501e600c40 0x02e80e9407980310 0x012018700c600000 0x0048061c03180000

def z57 : W := mkw 0x030038001c000c00 0x00c00e0007000300 0xd30038001c000f03 0x34c00e00070003c0

def z58 : W := mkw 0x1bb43ad5bef70fdb 0x06ed0eb56fbdc3f6 0xfffc3fffffff0fff 0xffff0fffffffc3ff

def z59 : W := mkw 0x004b050a00000000 0x0012c14280000000 0xe2db278f00000001 0xf8b6c9e3c0000000

def z60 : W := mkw 0x0000000000000000 0x0000000000000000 0x0407c0000003f000 0x8101f0000000fc00

def z61 : W := mkw 0x0001442840000000 0x0000510a10000000 0xa127dc78e0000001 0xe849f71e38000000

def z62 : W := mkw 0x044a0183018cc3b4 0xc1128060c06330ed 0x5ed82387139ccffe 0x17b608e1c4e733ff

def z63 : W := mkw 0x08003a5004200c40 0x02000e9401080310 0x0000187000000000 0x0000061c00000000

def z64 : W := mkw 0x03ea00001b488000 0x00fa800006d22000 0x9ffb00001ffcc002 0xe7fec00007ff3000

def z65 : W := mkw 0x1ba03ad13ef70fdb 0x06e80eb44fbdc3f6 0xffe03ff01fff0fff 0x7ff80ffc07ffc3ff

def z66 : W := mkw 0x0ba13ed81ee04ee4 0x82e84fb607b813b9 0xffe33ff81fe0cfff 0xfff8cffe07f833ff

def z67 : W := mkw 0x03a0324000000000 0x00e80c9000000000 0xe3e03ff000000001 0x78f80ffc00000000

def z68 : W := mkw 0x080008901ee00ec0 0x0200022407b803b0 0x180000001fe00fe2 0x0600000007f803f8

def z69 : W := mkw 0x1314300598160511 0x04c50c0166058144 0x52182007101c0700 0x14860801c40701c0

def z70 : W := mkw 0x23b5f76ec0000000 0x08ed7ddbb0000000 0x6124ffffe0000001 0x18493ffff8000000

def z71 : W := mkw 0x0401058b008443b4 0xc1004162c02110ed 0xf618278f101c0fff 0xbd8609e3c40703ff

def z72 : W := mkw 0x044b050b010cc134 0xc112c142c043304d 0x041b000f001cc01c 0x8106c003c0073007

def z73 : W := mkw 0x240177efc08443b4 0xc9005dfbf02110ed 0x60003fffe0000ffd 0x18000ffff80003ff

def z74 : W := mkw 0x0001442840000000 0x0000510a10000000 0x0007c008e0000000 0x8001f00238000000

def z75 : W := mkw 0x13157c2dfc170d1b 0x04c55f0b7f05c346 0xf73ffc7ffc1f0f1f 0xfdcfff1fff07c3c7

def z76 : W := mkw 0x03a000001a400000 0x00e8000006900000 0x9be000001fe00002 0x66f8000007f80000

def z77 : W := mkw 0x23fff76eda400000 0x08fffddbb6900000 0xfbffffffffe00003 0xfefffffffff80000

def z78 : W := mkw 0x005e8000011aa000 0x0017a0000046a800 0x041fc000001ff000 0x8107f0000007fc00

def z79 : W := mkw 0x0bfebad01ffaaec0 0x02ffaeb407feabb0 0xfffffff01fffffe3 0xfffffffc07fffff8

def z80 : W := mkw 0x000008102421084a 0x0000020409084212 0xad241c78ec6308ff 0xeb49071e3b18c23f

def z81 : W := mkw 0x044b45ab618dd3be 0xc112d16ad86374ef 0xfedfe78ff39fffff 0xffb7f9e3fce7ffff

def z82 : W := mkw 0x23fff76ec348a000 0x08fffddbb0d22800 0xebffffffe3e0f001 0xfafffffff8f83c00

def z83 : W := mkw 0x180008913ef70fdb 0x060002244fbdc3f6 0x1c0000001fff0ffe 0x0700000007ffc3ff

def z84 : W := mkw 0x00014c286401582e 0x8000530a1900560b 0x8507d808ec03f81f 0xa141f6023b00fe07

def z85 : W := mkw 0x28017ffec4a00ec0 0x0a005fffb12803b0 0x60003fffe0000fe1 0x18000ffff80003f8

def z86 : W := mkw 0x044b058a0188c2a4 0xc112c162806230a9 0xacc307880380c8ff 0xeb30c1e200e0323f

def z87 : W := mkw 0x23ffff7ee421586e 0x88ffffdfb908561b 0xefffffffec63f8ff 0xfbfffffffb18fe3f

def z88 : W := mkw 0x07fe81831bdea390 0x41ffa060c6f7a8e4 0x52d82387139c0700 0x14b608e1c4e701c0

def z89 : W := mkw 0x0000000100040110 0x0000000040010044 0xd618200f101c0f1f 0xb5860803c40703c7

def z90 : W := mkw 0x0bb43ad49ee00ec0 0x02ed0eb527b803b0 0xfbfc3fffffe00fe3 0xfeff0ffffff803f8

def z91 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0x72c03ff013800fe1 0x1cb00ffc04e003f8

def z92 : W := mkw 0x0001040800004024 0x8000410200001009 0x040300080000c01c 0x8100c00200003007

def z93 : W := mkw 0x0ceb07da03e8c2e4 0xc33ac1f680fa30b9 0x28e307f003e0c0e0 0x4a38c1fc00f83038

def z94 : W := mkw 0x004b050a00000000 0x0012c14280000000 0x20c3078000000000 0x4830c1e000000000

def z95 : W := mkw 0x000144386021506e 0x8000510e1808541b 0x2c27c478e063f0fc 0xcb09f11e3818fc3f

def z96 : W := mkw 0x044a0183018c8390 0x41128060c06320e4 0x52d82387139c0700 0x14b608e1c4e701c0

def z97 : W := mkw 0x0314000018120000 0x00c5000006048000 0x971c00001c1f0002 0xa5c700000707c000

def z98 : W := mkw 0x08a03ad006e00ec0 0x02280eb401b803b0 0x68e03ff003e00fe1 0x5a380ffc00f803f8

def z99 : W := mkw 0x000008102421586e 0x800002040908561b 0x8d27c0000c63f8fe 0xe349f0000318fe3f

def z100 : W := mkw 0x10140005a017011b 0x040500016805c046 0xd61c200ff01f0f1f 0xb5870803fc07c3c7

def z101 : W := mkw 0x2bb4faf4dee00ec0 0x0aed3ebd37b803b0 0xfbe4fff0ffe00fe3 0x7ef93ffc3ff803f8

def z102 : W := mkw 0x0001040800004024 0x8000410200001009 0x20000408000008fd 0x080001020000023f

def z103 : W := mkw 0x20ebf76ec0000000 0x083afddbb0000000 0x60e3ffffe0000001 0x5838fffff8000000

def z104 : W := mkw 0x08a002d002e002c0 0x022800b400b800b0 0x28e007f003e000e0 0x4a3801fc00f80038

def z105 : W := mkw 0x0314300480000000 0x00c50c0120000000 0xc31c380fe0000001 0xb0c70e03f8000000

def z106 : W := mkw 0x20ebc76a40000000 0x083af1da90000000 0x20e3c7f000000000 0x4838f1fc00000000

def z107 : W := mkw 0x044b058a0188c2a4 0xc112c162806230a9 0x28c307800380c0e0 0x4a30c1e000e03038

def z108 : W := mkw 0x13143804bc130c0b 0x04c50e012f04c302 0x01041800ec030000 0x004106003b00c000

def z109 : W := mkw 0x2bb4fa74de600c40 0x0aed3e9d37980310 0x0124d870ec600000 0x0049361c3b180000

def z110 : W := mkw 0x0ba032d01ae006c0 0x02e80cb406b801b0 0x7ae027f013e007e0 0x5eb809fc04f801f8

def z111 : W := mkw 0x08003ad004a00ec0 0x02000eb4012803b0 0x60003ff000000fe1 0x18000ffc000003f8

def z112 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0x20001c78e00008fd 0x0800071e3800023f

def z113 : W := mkw 0x0ba03ad03ee10eca 0x02e80eb40fb843b2 0xffe43ff8ffe30fff 0xfff90ffe3ff8c3ff

def z114 : W := mkw 0x08a00ad006e00ac0 0x022802b401b802b0 0xa9e01ff00fe008e3 0x6a7807fc03f80238

def z115 : W := mkw 0x205ff76ec0000000 0x0817fddbb0000000 0x601fffffe0000001 0x9807fffff8000000

def z116 : W := mkw 0x0001443840205064 0x8000510e10081419 0xad27c4700c63f0e2 0xeb49f11c0318fc38

def z117 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0xefffffffec63f003 0xfbfffffffb18fc00

def z118 : W := mkw 0x2bfffffedee00ec0 0x0affffffb7b803b0 0xfbffffffffe00fe3 0xfefffffffff803f8

def z119 : W := mkw 0x17143885bd9fcfbf 0xc5c50e216f67f3ef 0xdf1c380fff9fcfff 0xb7c70e03ffe7f3ff

def z120 : W := mkw 0x3bfffffffef70fdb 0x0effffffffbdc3f6 0xffffffffffff0fff 0xffffffffffffc3ff

def z121 : W := mkw 0x175f7dbffdbfdfff 0xc5d7df6fff6ff7ff 0xffffffffffffffff 0xffffffffffffffff

def z122 : W := mkw 0x04000081018cc3b4 0xc1000020406330ed 0x1c000000139ccffe 0x0700000004e733ff

def z123 : W := mkw 0x0314000018120000 0x00c5000006048000 0x9f3fc0001c7ff002 0xe7cff000071ffc00

def z124 : W := mkw 0x044b45bb41acd3f4 0xc112d16ed06b34fd 0xfefbe7ff13fcffff 0xffbef9ffc4ff3fff

def z125 : W := mkw 0x27ffb7cf818cc3b4 0xc9ffedf3e06330ed 0xfedb278f139ccfff 0xffb6c9e3c4e733ff

def z126 : W := mkw 0x004a000001088000 0x0012800000422000 0x9edb0000139cc002 0xe7b6c00004e73000

def z127 : W := mkw 0x20017f7ee421586e 0x88005fdfb908561b 0xed27ffffec63f8ff 0xfb49fffffb18fe3f

def z128 : W := mkw 0x0ba17ef87ee15eee 0x82e85fbe1fb857bb 0xffe7fff8ffe3ffff 0xfff9fffe3ff8ffff

def z129 : W := mkw 0x205fc52ec11aa000 0x0817f14bb046a800 0x041fc00fe01ff000 0x8107f003f807fc00

def z130 : W := mkw 0x03fe8000011aa000 0x00ffa0000046a800 0x87ffc000001ff000 0xe1fff0000007fc00

def z131 : W := mkw 0x004b04080108c024 0x8012c10200423009 0xbedb0408139cc8ff 0xefb6c10204e7323f

def z132 : W := mkw 0x07ff858b1bdee3b4 0xc1ffe162c6f7b8ed 0xffffe78f1fffffff 0xfffff9e3c7ffffff

def z133 : W := mkw 0x0ba002d01ae002c0 0x02e800b406b800b0 0xbbe007f01fe000e2 0x6ef801fc07f80038

def z134 : W := mkw 0x2fffffffdfeccff4 0xcbfffffff7fb33fd 0xfffffffffffccfff 0xffffffffffff33ff

def z135 : W := mkw 0x0ba17ef87ee15eee 0x82e85fbe1fb857bb 0xfbe03ff8ffe00fff 0x7ef80ffe3ff803ff

def z136 : W := mkw 0x08003ad004a00ec0 0x02000eb4012803b0 0xfac03ff013800fe3 0x7eb00ffc04e003f8

def z137 : W := mkw 0x2001452ec0000000 0x0800514bb0000000 0x0000000fe0000000 0x00000003f8000000

def z138 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0x0c07c008ec63f8fe 0x8301f0023b18fe3f

def z139 : W := mkw 0x0314000018120000 0x00c5000006048000 0x12180000101c0000 0x0486000004070000

def z140 : W := mkw 0x175e3987bd9f8f9b 0x45d78e61ef67e3e6 0xd7dc3b8fff9f0f1f 0xb5f70ee3ffe7c3c7

def z141 : W := mkw 0x0000380004000c00 0x00000e0001000300 0x4000380000000f01 0x10000e00000003c0

def z142 : W := mkw 0x00014c396425597e 0x8000530e5909565f 0xff3ffc7ffc7fffff 0xffcfff1fff1fffff

def z143 : W := mkw 0x08014cb87ee15eee 0x8200532e1fb857bb 0xbd27dc78ffe3ffff 0xef49f71e3ff8ffff

def z144 : W := mkw 0x03a000001b5aa000 0x00e8000006d6a800 0x9fe000001ffff002 0x67f8000007fffc00

def z145 : W := mkw 0x03ffcc387f7bf86e 0x80fff30e1fdefe1b 0xbfffdc78fffff8ff 0xeffff71e3ffffe3f

def z146 : W := mkw 0x1000000118160511 0x0400000046058144 0x10000000101c0700 0x04000000040701c0

def z147 : W := mkw 0x13feb805bf5fad1b 0x04ffae016fd7eb46 0xdffff80fffffff1f 0xf7fffe03ffffffc7

def z148 : W := mkw 0x000008102421586e 0x800002040908561b 0x00000000000008fc 0x000000000000023f

def z149 : W := mkw 0x23b4f264c0000000 0x08ed3c9930000000 0x0124d870e0000000 0x0049361c38000000

def z150 : W := mkw 0x04014cb965addbfe 0xc100532e596b76ff 0xbd27dc78ffffffff 0xef49f71e3fffffff

def z151 : W := mkw 0x13b43a45bc170d1b 0x04ed0e916f05c346 0xf7fc3ffffc1f0f1f 0xfdff0fffff07c3c7

def z152 : W := mkw 0x0feb37cb1bccc7b4 0xc3facdf2c6f331ed 0xfedb278f139ccfff 0xffb6c9e3c4e733ff

def z153 : W := mkw 0x100008013c170d1b 0x040002004f05c346 0x95041808fc1f0f1f 0xa54106023f07c3c7

def z154 : W := mkw 0x08a002c002c00280 0x022800b000b000a0 0x00c0038003800000 0x003000e000e00000

def z155 : W := mkw 0x044b058b018c8390 0x4112c162c06320e4 0xf2db278f139c0701 0xfcb6c9e3c4e701c0

def z156 : W := mkw 0x0401058b008443b4 0xc1004162c02110ed 0xfac0278f13800fff 0x7eb009e3c4e003ff

def z157 : W := mkw 0x23fff76ed8120000 0x08fffddbb6048000 0xf7fffffffc1f0003 0xfdffffffff07c000

def z158 : W := mkw 0x100008013c170d1b 0x040002004f05c346 0x140000001c1f0f1e 0x050000000707c3c7

def z159 : W := mkw 0x10154c3de437597f 0x8405530f790dd65f 0xad3fdc7fec7ff8ff 0xeb4ff71ffb1ffe3f

def z160 : W := mkw 0x17ffbd8fbfdfefbf 0xc5ffef63eff7fbef 0xffffff8fffffffff 0xffffffe3ffffffff

def z161 : W := mkw 0x0401058b018cc3b4 0xc1004162c06330ed 0x7c00278f139ccfff 0x1f0009e3c4e733ff

def z162 : W := mkw 0x0feb7ffb7feddffe 0xc3fadffedffb77ff 0xffffffffffffffff 0xffffffffffffffff

def z163 : W := mkw 0x000008012405091a 0x0000020049014246 0xd71c380ffc1f0f1f 0xb5c70e03ff07c3c7

def z164 : W := mkw 0x03b480001a522000 0x00ed200006948800 0x8d27c0000c63f002 0xe349f0000318fc00

def z165 : W := mkw 0x03fe80801bdaa280 0x00ffa02006f6a8a0 0xffffe7801fffffe3 0xfffff9e007fffff8

def z166 : W := mkw 0x23fff77ec0205064 0x88fffddfb0081419 0xebffffffe060f0e1 0xfafffffff8183c38

def z167 : W := mkw 0x004b452a40000000 0x0012d14a90000000 0xe3ffffffe0000001 0xf8fffffff8000000

def z168 : W := mkw 0x23a1776ec0000000 0x08e85ddbb0000000 0xe3e03fffe0000001 0x78f80ffff8000000

def z169 : W := mkw 0x33ffff6ffc170d1b 0x0cffffdbff05c346 0xf7fffffffc1f0f1f 0xfdffffffff07c3c7

def z170 : W := mkw 0x0000081004200840 0x0000020401080210 0xa9201c700c6008e3 0x6a48071c03180238

def z171 : W := mkw 0x0001443840205064 0x8000510e10081419 0x2823c4700060f0e0 0x4a08f11c00183c38

def z172 : W := mkw 0x00a0000002400000 0x0028000000900000 0x08e0000003e00000 0x4238000000f80000

def z173 : W := mkw 0x000144286001502e 0x8000510a1800540b 0x8d27c008ec63f01e 0xe349f0023b18fc07

def z174 : W := mkw 0x0000324000000000 0x00000c9000000000 0x60003ff000000001 0x18000ffc00000000

def z175 : W := mkw 0x1bb43a54be730c4b 0x06ed0e952f9cc312 0x01241870ec630000 0x0049061c3b18c000

def z176 : W := mkw 0x33fff76fe017011b 0x0cfffddbf805c046 0xe7ffffffe01f001d 0xf9fffffff807c007

def z177 : W := mkw 0x04014dbb64a55bfe 0xc100536ed92956ff 0x60003fffe0000ffd 0x18000ffff80003ff

def z178 : W := mkw 0x13b4b805be572d1b 0x04ed2e016f95cb46 0xd73cf80ffc7f3f1f 0xb5cf3e03ff1fcfc7

def z179 : W := mkw 0x0401050b00044134 0xc1004142c001104d 0x0000000f0000001c 0x00000003c0000007

def z180 : W := mkw 0x0314300480000000 0x00c50c0120000000 0x01041800e0000000 0x0041060038000000

def z181 : W := mkw 0x20ffc76ec0000000 0x083ff1dbb0000000 0x20ffc7ffe0000000 0xc83ff1fff8000000

def z182 : W := mkw 0x03b480001a522000 0x00ed200006948800 0x0000000000000000 0x0000000000000000

def z183 : W := mkw 0x000008002401080a 0x0000020009004202 0x01041800ec030000 0x004106003b00c000

def z184 : W := mkw 0x13143815bc370d5b 0x04c50e056f0dc356 0xff3c3c7ffc7f0fff 0xffcf0f1fff1fc3ff

def z185 : W := mkw 0x080008903ee15eee 0x820002240fb857bb 0x1c0000001fe3fffe 0x0700000007f8ffff

def z186 : W := mkw 0x13147834fc331c4b 0x04c51e0d3f0cc712 0x0124d870ec633000 0x0049361c3b18cc00

def z187 : W := mkw 0x044b050b010cc134 0xc112c142c043304d 0x9edb000f139cc01e 0xe7b6c003c4e73007

def z188 : W := mkw 0x03eb374a00000000 0x00facdd280000000 0xe3fb3fff00000001 0xf8fecfffc0000000

def z189 : W := mkw 0x0c0008911feccff4 0xc300022447fb33fd 0x1c0000001ffccffe 0x0700000007ff33ff

def z190 : W := mkw 0x000000001b5aa000 0x0000000006d6a800 0x9d27c0001ffff002 0xe749f00007fffc00

def z191 : W := mkw 0x23feb34680000000 0x08ffacd1a0000000 0x42d8238700000000 0x10b608e1c0000000

def z192 : W := mkw 0x03154c387c33586e 0x80c5530e1f0cd61b 0xbf3fdc78fc7ff8ff 0xefcff71e3f1ffe3f

def z193 : W := mkw 0x004a0001010c8110 0x0012800040432044 0xdedb200f139ccf1f 0xf7b6c803c4e733c7

def z194 : W := mkw 0x10017c3de4255d7f 0x84005f0f7909575f 0xed27fc7fec63ffff 0xfb49ff1ffb18ffff

def z195 : W := mkw 0x08a002d002e002c0 0x022800b400b800b0 0xfae027f013e00fe3 0x7eb809fc04f803f8

def z196 : W := mkw 0x13fe88013f5fad1b 0x04ffa2004fd7eb46 0x9fffc0001fffff1e 0xe7fff00007ffffc7

def z197 : W := mkw 0x03fe88103f7bf86e 0x80ffa2040fdefe1b 0x9fffc0001ffff8fe 0xe7fff00007fffe3f

def z198 : W := mkw 0x0000081004200840 0x0000020401080210 0xad27dc700c63f8e3 0xeb49f71c0318fe38

def z199 : W := mkw 0x0001040800004024 0x8000410200001009 0x280304000000c0e0 0x4a00c10000003038

def z200 : W := mkw 0x03ffc4287b5bf02e 0x80fff10a1ed6fc0b 0x9fffc008fffff01e 0xe7fff0023ffffc07

def z201 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x9bf800001ffc0002 0x66fe000007ff0000

def z202 : W := mkw 0x0314300498120000 0x00c50c0126048000 0xd71c380ffc1f0003 0xb5c70e03ff07c000

def z203 : W := mkw 0x204bc52a40000000 0x0812f14a90000000 0x0003c00000000000 0x0000f00000000000

def z204 : W := mkw 0x23fff76ec0004024 0x88fffddbb0001009 0xefffffffe000c8ff 0xfbfffffff800323f

def z205 : W := mkw 0x03fe88101f7aa840 0x00ffa20407deaa10 0xbfffdc701ffff8e3 0xeffff71c07fffe38

def z206 : W := mkw 0x13b43805be570d1b 0x04ed0e016f95c346 0xdffc380fffff0f1f 0xf7ff0e03ffffc3c7

def z207 : W := mkw 0x0000000100040110 0x0000000040010044 0x0418000f001c001c 0x81060003c0070007

def z208 : W := mkw 0x144b0d8b3d9fcfbf 0xc512c362cf67f3ef 0xfedb278f1f9fcfff 0xffb6c9e3c7e7f3ff

def z209 : W := mkw 0x03ffc4285b5aa000 0x00fff10a16d6a800 0xbfffdc78fffff003 0xeffff71e3ffffc00

def z210 : W := mkw 0x23fff76eda522000 0x08fffddbb6948800 0xe3ffffffec633001 0xf8fffffffb18cc00

def z211 : W := mkw 0x00ea80000348a000 0x003aa00000d22800 0x08e3c00003e0f000 0x4238f00000f83c00

def z212 : W := mkw 0x0feb3fdb1feccff4 0xc3facff6c7fb33fd 0xfffb3fff1ffccfff 0xfffecfffc7ff33ff

def z213 : W := mkw 0x03b400001a520000 0x00ed000006948000 0x9ffc00001fff0002 0xe7ff000007ffc000

def z214 : W := mkw 0x00014c3844200840 0x0000530e11080210 0xa927dc78ec6008e3 0xea49f71e3b180238

def z215 : W := mkw 0x0001040800000000 0x0000410200000000 0xa003040800000001 0xe800c10200000000

def z216 : W := mkw 0x03b480001a522000 0x00ed200006948800 0x0124c0000c633000 0x004930000318cc00

def z217 : W := mkw 0x204b776ec0000000 0x0812dddbb0000000 0xe2db3fffe0000001 0xf8b6cffff8000000

def z218 : W := mkw 0x13143885bc970f9b 0x04c50e216f25c3e6 0xffdc3f8fff9f0fff 0xfff70fe3ffe7c3ff

def z219 : W := mkw 0x000048306421184a 0x0000120c19084612 0x00001870e0000000 0x0000061c38000000

def z220 : W := mkw 0x03fe800001088000 0x00ffa00000422000 0x9fffc000139cc002 0xe7fff00004e73000

def z221 : W := mkw 0x044b050b010cc134 0xc112c142c043304d 0xd61b200f101ccf1f 0xb586c803c40733c7

def z222 : W := mkw 0x13157c3dfc375d7f 0x84c55f0f7f0dd75f 0xff3ffc7ffc7fffff 0xffcfff1fff1fffff

def z223 : W := mkw 0x04010489018cc3b4 0xc1004122406330ed 0xbc030408139ccfff 0xef00c10204e733ff

def z224 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0x0527d878ec63f01c 0x8149f61e3b18fc07

def z225 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0x531c3807fc1f0700 0x14c70e01ff07c1c0

def z226 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0x2124dc78ec6338fd 0x0849371e3b18ce3f

def z227 : W := mkw 0x10003805bc170d1b 0x04000e016f05c346 0x5400380ffc1f0f1f 0x15000e03ff07c3c7

def z228 : W := mkw 0x00014c387f7bf86e 0x8000530e1fdefe1b 0xbd27dc78fffff8ff 0xef49f71e3ffffe3f

def z229 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0xdf3ff80ffc7fff1f 0xf7cffe03ff1fffc7

def z230 : W := mkw 0x03b5cc387e73786e 0x80ed730e1f9cde1b 0xad27dc78ec63f8ff 0xeb49f71e3b18fe3f

def z231 : W := mkw 0x0bb4bad01ef22ec0 0x02ed2eb407bc8bb0 0xfbe4fff01fe33fe3 0x7ef93ffc07f8cff8

def z232 : W := mkw 0x00ea80000348a000 0x003aa00000d22800 0x9efbc00013fcf002 0xe7bef00004ff3c00

def z233 : W := mkw 0x0000008100840390 0x00000020402100e4 0xfed8278f139c0fff 0xffb609e3c4e703ff

def z234 : W := mkw 0x000000002001000a 0x0000000008004002 0x04040008e003001c 0x810100023800c007

def z235 : W := mkw 0x000008102421586e 0x800002040908561b 0x0c0000000c63f8fe 0x030000000318fe3f

def z236 : W := mkw 0x1b143ad5bcb70fdb 0x06c50eb56f2dc3f6 0xf71c3ffffc1f0fff 0xbdc70fffff07c3ff

def z237 : W := mkw 0x0bfffef87ffbfeee 0x82ffffbe1ffeffbb 0xfffffff8ffffffff 0xfffffffe3fffffff

def z238 : W := mkw 0x0001442840000000 0x0000510a10000000 0x2023c47000000000 0x4808f11c00000000

def z239 : W := mkw 0x044a0103010c8110 0x41128040c0432044 0x00180007001c0000 0x00060001c0070000

def z240 : W := mkw 0x0ba03a501e600c40 0x02e80e9407980310 0xd32038701c600f03 0x34c80e1c071803c0

def z241 : W := mkw 0x175f358f999ec7b5 0xc5d7cd63e667b1ed 0xfedb278f139ccfff 0xffb6c9e3c4e733ff

def z242 : W := mkw 0x080008901ffaaec0 0x0200022407feabb0 0x1c0000001fffffe2 0x0700000007fffff8

def z243 : W := mkw 0x03b480001a522000 0x00ed200006948800 0x9be4c0001fe33002 0x66f9300007f8cc00

def z244 : W := mkw 0x205fc52ec0000000 0x0817f14bb0000000 0x001fc00fe0000000 0x8007f003f8000000

def z245 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0x62d83fffe0000001 0x18b60ffff8000000

def z246 : W := mkw 0x0ba03ad03ee15eee 0x82e80eb40fb857bb 0xffe03ff01fe3ffff 0x7ff80ffc07f8ffff

def z247 : W := mkw 0x000008002401080a 0x0000020009004202 0x8d27d808ec63f81f 0xe349f6023b18fe07

def z248 : W := mkw 0x031408003c13080a 0x00c502000f04c202 0x971c1808fc1f081f 0xa5c706023f07c207

def z249 : W := mkw 0x04014dbb64a55bfe 0xc100536ed92956ff 0xed27ffffec63ffff 0xfb49fffffb18ffff

def z250 : W := mkw 0x23b4f264c0000000 0x08ed3c9930000000 0xe3e4fff0e0000001 0x78f93ffc38000000

def z251 : W := mkw 0x004a000000000000 0x0012800000000000 0x82db000000000000 0xe0b6c00000000000

def z252 : W := mkw 0x044a018201888280 0x41128060806220a0 0x00c0038003800000 0x003000e000e00000

def z253 : W := mkw 0x13140005b817011b 0x04c500016e05c046 0x971c000ffc1f001e 0xa5c70003ff07c007

def z254 : W := mkw 0x33ffff6fff5fad1b 0x0cffffdbffd7eb46 0xffffffffffffff1f 0xffffffffffffffc7

def z255 : W := mkw 0x175f3d8fbd9fcfbf 0xc5d7cf63ef67f3ef 0xffdf3f8fff9fcfff 0xfff7cfe3ffe7f3ff

def z256 : W := mkw 0x00010c182421586e 0x800043060908561b 0xac0304080c63f8ff 0xeb00c1020318fe3f

def z257 : W := mkw 0x03ffc42840000000 0x00fff10a10000000 0xa3ffdc78e0000001 0xe8fff71e38000000

def z258 : W := mkw 0x0001442840000000 0x0000510a10000000 0xad27dc78ec63f003 0xeb49f71e3b18fc00

def z259 : W := mkw 0x0ba008901ee00ec0 0x02e8022407b803b0 0x9be000001fe00fe2 0x66f8000007f803f8

def z260 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0x1c1b000f139ccffe 0x8706c003c4e733ff

def z261 : W := mkw 0x0300300018000400 0x00c00c0006000100 0x5200200010000700 0x14800800040001c0

def z262 : W := mkw 0x10003805a4050d1b 0x04000e0169014346 0xd618380ff01c0f1f 0xb5860e03fc0703c7

def z263 : W := mkw 0x135eb805bd1fad1b 0x04d7ae016f47eb46 0xd71ff80ffc1fff1f 0xb5c7fe03ff07ffc7

def z264 : W := mkw 0x13feb0059b5ea511 0x04ffac0166d7a944 0x52d82007139c0700 0x14b60801c4e701c0

def z265 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0xffe7fff01fe3ffe3 0xfff9fffc07f8fff8

def z266 : W := mkw 0x2001776ec0000000 0x08005ddbb0000000 0xe127ffffe0000001 0xf849fffff8000000

def z267 : W := mkw 0x044b45ba41a8d2e4 0xc112d16e906a34b9 0x28e3c7f003e0f0e0 0x4a38f1fc00f83c38

def z268 : W := mkw 0x0315742cc0000000 0x00c55d0b30000000 0xe33ffc7fe0000001 0xf8cfff1ff8000000

def z269 : W := mkw 0x0000001000205064 0x8000000400081419 0x080000000060f0e0 0x0200000000183c38

def z270 : W := mkw 0x03a000801ac00280 0x00e8002006b000a0 0xfbe027801fe00fe3 0x7ef809e007f803f8

def z271 : W := mkw 0x044b058b1bdee3b4 0xc112c162c6f7b8ed 0xfedb278f1fffffff 0xffb6c9e3c7ffffff

def z272 : W := mkw 0x040000800188c2a4 0xc1000020006230a9 0x080000000380c0e0 0x0200000000e03038

def z273 : W := mkw 0x03a032c000800280 0x00e80cb0002000a0 0xfbe03ff013800fe3 0x7ef80ffc04e003f8

def z274 : W := mkw 0x10140805bc170d1b 0x040502016f05c346 0x141c000ffc1f0f1e 0x85070003ff07c3c7

def z275 : W := mkw 0x20ebc76a4348a000 0x083af1da90d22800 0x28e3c7f003e0f000 0x4a38f1fc00f83c00

def z276 : W := mkw 0x03feb0049b5aa000 0x00ffac0126d6a800 0xdffff80ffffff003 0xf7fffe03fffffc00

def z277 : W := mkw 0x000000001a522000 0x0000000006948800 0x000000000c633000 0x000000000318cc00

def z278 : W := mkw 0x0ceb07db03ecc3f4 0xc33ac1f6c0fb30fd 0xfefb27ff13fccfff 0xffbec9ffc4ff33ff

def z279 : W := mkw 0x080008901ee00ec0 0x0200022407b803b0 0xb9201c701fe00fe3 0x6e48071c07f803f8

def z280 : W := mkw 0x08ea82d003e8a2c0 0x023aa0b400fa28b0 0x28e3c7f003e0f0e0 0x4a38f1fc00f83c38

def z281 : W := mkw 0x0401058a008042a4 0xc1004162802010a9 0x20000780000000e0 0x080001e000000038

def z282 : W := mkw 0x005e8000011aa000 0x0017a0000046a800 0x9edfc000139ff002 0xe7b7f00004e7fc00

def z283 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0x2c23c4700c63f8fe 0x4b08f11c0318fe3f

def z284 : W := mkw 0x044b058a0188c2a4 0xc112c162806230a9 0xbedb0780139cc0e2 0xefb6c1e004e73038

def z285 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0x29e01ff00fe000e0 0x4a7807fc03f80038

def z286 : W := mkw 0x1314300598160511 0x04c50c0166058144 0xd71c20071c1f0702 0xb5c70801c707c1c0

def z287 : W := mkw 0x044b45ab418cc3b4 0xc112d16ad06330ed 0xfffffffff39ccfff 0xfffffffffce733ff

def z288 : W := mkw 0x045f850b011ee134 0xc117e142c047b84d 0x041fc00f001ff01c 0x8107f003c007fc07

def z289 : W := mkw 0x13147835fc371d5b 0x04c51e0d7f0dc756 0xd73cf87ffc7f3f1f 0xb5cf3e1fff1fcfc7

def z290 : W := mkw 0x005e80001b5aa000 0x0017a00006d6a800 0x1c1fc0001ffff002 0x8707f00007fffc00

def z291 : W := mkw 0x075f358f818cc3b4 0xc1d7cd63e06330ed 0xffdf3f8ff39ccfff 0xfff7cfe3fce733ff

def z292 : W := mkw 0x03a032401a400000 0x00e80c9006900000 0xfbe03ff01fe00003 0x7ef80ffc07f80000

def z293 : W := mkw 0x03ff850a1b5aa000 0x00ffe14286d6a800 0xffffe78f1ffff003 0xfffff9e3c7fffc00

def z294 : W := mkw 0x23ffff6edc000c00 0x08ffffdbb7000300 0xf3fffffffc000f03 0xfcffffffff0003c0

def z295 : W := mkw 0x27ffffffe5addbfe 0xc9fffffff96b76ff 0xffffffffffffffff 0xffffffffffffffff

def z296 : W := mkw 0x0000403040201040 0x0000100c10080410 0x0020c07000603000 0x0008301c00180c00

def z297 : W := mkw 0x27fff7efc08443b4 0xc9fffdfbf02110ed 0xe3ffffffe0000ffd 0xf8fffffff80003ff

def z298 : W := mkw 0x030038801c800e80 0x00c00e20072003a0 0xfbc03f801f800fe3 0x7ef00fe007e003f8

def z299 : W := mkw 0x03017c387c215c6e 0x80c05f0e1f08571b 0xff27fc78fc63ffff 0xffc9ff1e3f18ffff

def z300 : W := mkw 0x031438049c000c00 0x00c50e0127000300 0xd31c380ffc000f03 0xb4c70e03ff0003c0

def z301 : W := mkw 0x27fff7efc18c8390 0x49fffdfbf06320e4 0xf3fffffff39c0701 0xfcfffffffce701c0

def z302 : W := mkw 0x004a008001888280 0x00128020006220a0 0xfedb2780139ccfe3 0xffb6c9e004e733f8

def z303 : W := mkw 0x131408013c170d1b 0x04c502004f05c346 0x971c00001c1f0f1e 0xa5c700000707c3c7

def z304 : W := mkw 0x00fe8000035aa000 0x003fa00000d6a800 0x0cffc00003fff000 0xc33ff00000fffc00

def z305 : W := mkw 0x13feb805bf5fad1b 0x04ffae016fd7eb46 0xd7dc380fff9f0f1f 0xb5f70e03ffe7c3c7

def z306 : W := mkw 0x23b4f264da522000 0x08ed3c9936948800 0x0124d870ec633000 0x0049361c3b18cc00

def z307 : W := mkw 0x0ba032c01ac00680 0x02e80cb006b001a0 0xf3e03ff013800701 0x7cf80ffc04e001c0

def z308 : W := mkw 0x0000000100040110 0x0000000040010044 0x4000200f00000f1d 0x10000803c00003c7

def z309 : W := mkw 0x03b4324480000000 0x00ed0c9120000000 0xe3fc3fffe0000001 0xf8ff0ffff8000000

def z310 : W := mkw 0x0b003ad01ca00ec0 0x02c00eb4072803b0 0xf3003ff01c000fe3 0x3cc00ffc070003f8

def z311 : W := mkw 0x030038001c000c00 0x00c00e0007000300 0x010018000c000000 0x0040060003000000

def z312 : W := mkw 0x245fc52fc10cc134 0xc917f14bf043304d 0x041fc00fe01cc01c 0x8107f003f8073007

def z313 : W := mkw 0x04000081018cc3b4 0xc1000020406330ed 0xde18200f139ccfff 0xb7860803c4e733ff

def z314 : W := mkw 0x20ebc76a40000000 0x083af1da90000000 0xa1e7dff8e0000001 0xe879f7fe38000000

def z315 : W := mkw 0x004a000001088000 0x0012800000422000 0x041b0000001cc000 0x8106c00000073000

def z316 : W := mkw 0x044b050b010cc134 0xc112c142c043304d 0xac1b040f001cc8ff 0xeb06c103c007323f

def z317 : W := mkw 0x13157c3cfc335c6f 0x84c55f0f3f0cd71b 0xad27dc78ec63f8ff 0xeb49f71e3b18fe3f

def z318 : W := mkw 0x23feb34680000000 0x08ffacd1a0000000 0xc3dc3b8fe0000001 0xb0f70ee3f8000000

def z319 : W := mkw 0x07eb058b1bccc3b4 0xc1fac162c6f330ed 0xfffb278f1ffccfff 0xfffec9e3c7ff33ff

def z320 : W := mkw 0x000000001a400000 0x0000000006900000 0x180000001fe00002 0x0600000007f80000

def z321 : W := mkw 0x2315776ec0000000 0x08c55ddbb0000000 0xe31c3fffe0000001 0xb8c70ffff8000000

def z322 : W := mkw 0x031438001c120c00 0x00c50e0007048300 0xd71c38001c1f0f03 0xb5c70e000707c3c0

def z323 : W := mkw 0x0001050a00000000 0x0000414280000000 0x6000278f00000001 0x180009e3c0000000

def z324 : W := mkw 0x0bfeba501f7aac40 0x02ffae9407deab10 0x9fffd8701ffff002 0xe7fff61c07fffc00

def z325 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0xffffe78f1fffffff 0xfffff9e3c7ffffff

def z326 : W := mkw 0x2000334680000000 0x08000cd1a0000000 0x4000238700000000 0x100008e1c0000000

def z327 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x12d80000139c0000 0x04b6000004e70000

def z328 : W := mkw 0x075f058b199ec3b4 0xc1d7c162c667b0ed 0xffdf278f1f9fcfff 0xfff7c9e3c7e7f3ff

def z329 : W := mkw 0x205fc52ec0000000 0x0817f14bb0000000 0xe2dfe78fe0000001 0xf8b7f9e3f8000000

def z330 : W := mkw 0x175e3187999e8791 0x45d78c61e667a1e4 0x52d82387139c0700 0x14b608e1c4e701c0

def z331 : W := mkw 0x03fe80001a522000 0x00ffa00006948800 0x83ffc0000c633000 0xe0fff0000318cc00

def z332 : W := mkw 0x03143804a401080a 0x00c50e0129004202 0xc71c380fec03081f 0xb1c70e03fb00c207

def z333 : W := mkw 0x044b4dba65a9daee 0xc112d36e996a76bb 0xade7dff8efe3f8ff 0xeb79f7fe3bf8fe3f

def z334 : W := mkw 0x1b143895bef70fdb 0x06c50e256fbdc3f6 0xdf1c380fffff0fff 0xb7c70e03ffffc3ff

def z335 : W := mkw 0x23b4fa74e421184a 0x08ed3e9d39084612 0x0124d870ec633000 0x0049361c3b18cc00

def z336 : W := mkw 0x205fc52ee001502e 0x8817f14bb800540b 0x041fc00fe003f01c 0x8107f003f800fc07

def z337 : W := mkw 0x135e3805bd1f8d1b 0x04d78e016f47e346 0xdfdf380fff9fcf1f 0xf7f7ce03ffe7f3c7

def z338 : W := mkw 0x17153d8fbc974fbf 0xc5c54f63ef25d3ef 0xf71c3f8ffc1f0fff 0xbdc70fe3ff07c3ff

def z339 : W := mkw 0x23ffff7eff7bf86e 0x88ffffdfbfdefe1b 0xfffffffffffff8ff 0xfffffffffffffe3f

def z340 : W := mkw 0x004a000001088000 0x0012800000422000 0x08c300000380c000 0x4230c00000e03000

def z341 : W := mkw 0x03ff850a00000000 0x00ffe14280000000 0xe3ffe78f00000001 0xf8fff9e3c0000000

def z342 : W := mkw 0x035f350e80000000 0x00d7cd43a0000000 0xe3df3f8fe0000001 0xf8f7cfe3f8000000

def z343 : W := mkw 0x23ffff7ec4200840 0x08ffffdfb1080210 0xebffffffec6008e3 0xfafffffffb180238

def z344 : W := mkw 0x030038003c010c0a 0x00c00e000f004302 0xd7043808fc030f1f 0xb5c10e023f00c3c7

def z345 : W := mkw 0x004b050a01088000 0x0012c14280422000 0xfedb278f139cc003 0xffb6c9e3c4e73000

def z346 : W := mkw 0x03ea80001b48a000 0x00faa00006d22800 0x9be3c0001fe0f002 0x66f8f00007f83c00

def z347 : W := mkw 0x004a000001088000 0x0012800000422000 0x9fffc0001ffff002 0xe7fff00007fffc00

def z348 : W := mkw 0x04000081018c8390 0x41000020406320e4 0x10000000139c0700 0x0400000004e701c0

def z349 : W := mkw 0x0bb43ad01ef20ec0 0x02ed0eb407bc83b0 0xfffc3ff01fff0fe3 0xffff0ffc07ffc3f8

def z350 : W := mkw 0x33157f6ffc170d1b 0x0cc55fdbff05c346 0xf71c3ffffc1f0f1f 0xbdc70fffff07c3c7

def z351 : W := mkw 0x0b0038901ee00ec0 0x02c00e2407b803b0 0xdb0038001fe00fe3 0x36c00e0007f803f8

def z352 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0x72d8278f139c0ffd 0x1cb609e3c4e703ff

def z353 : W := mkw 0x03a000001a400000 0x00e8000006900000 0x9fe7c0001fe3f002 0xe7f9f00007f8fc00

def z354 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0x561820071c1f0f1e 0x15860801c707c3c7

def z355 : W := mkw 0x0000008000800280 0x00000020002000a0 0x28c00780038000e0 0x4a3001e000e00038

def z356 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0x21e7dff0e0000000 0x4879f7fc38000000

def z357 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0x5ac023801fe00fe2 0x16b008e007f803f8

def z358 : W := mkw 0x0314300580040110 0x00c50c0160010044 0xd71c380ff01c0f1f 0xb5c70e03fc0703c7

def z359 : W := mkw 0x20ebc77a40205064 0x883af1de90081419 0x28e3c7f00060f0e0 0x4a38f1fc00183c38

def z360 : W := mkw 0x0000008000800280 0x00000020002000a0 0x6000278000000fe1 0x180009e0000003f8

def z361 : W := mkw 0x044b058a0188c2a4 0xc112c162806230a9 0xfac327801380cfe3 0x7eb0c9e004e033f8

def z362 : W := mkw 0x00010c082401482e 0x800043020900520b 0xad071c08ec03c8ff 0xeb41c7023b00f23f

def z363 : W := mkw 0x035e0000191a8000 0x00d780000646a000 0x9fdf00001f9fc002 0xe7f7c00007e7f000

def z364 : W := mkw 0x0ba032c01ac00680 0x02e80cb006b001a0 0xdbe023801fe00702 0x76f808e007f801c0

def z365 : W := mkw 0x23fef366c0000000 0x08ffbcd9b0000000 0x43fcfbf7e0000000 0x10ff3efdf8000000

def z366 : W := mkw 0x23b5f66cc0000000 0x08ed7d9b30000000 0xa127dc78e0000001 0xe849f71e38000000

def z367 : W := mkw 0x0bb4ba501e722c40 0x02ed2e94079c8b10 0x0124d8700c633000 0x0049361c0318cc00

def z368 : W := mkw 0x03feb00480000000 0x00ffac0120000000 0xc3fff80fe0000001 0xf0fffe03f8000000

def z369 : W := mkw 0x03a000001a400000 0x00e8000006900000 0x12c0000013800000 0x04b0000004e00000

def z370 : W := mkw 0x23fff76edb5aa000 0x08fffddbb6d6a800 0xf3fffffff39c0001 0xfcfffffffce70000

def z371 : W := mkw 0x030038011c040d10 0x00c00e0047010344 0xd718380f1c1c0f1f 0xb5c60e03c70703c7

def z372 : W := mkw 0x03fe88003f5ba80a 0x00ffa2000fd6ea02 0x9fffd808fffff81f 0xe7fff6023ffffe07

def z373 : W := mkw 0x08003ad01ee00ec0 0x02000eb407b803b0 0x78003ff01fe00fe3 0x1e000ffc07f803f8

def z374 : W := mkw 0x004a00001b5aa000 0x0012800006d6a800 0x9edb00001ffff002 0xe7b6c00007fffc00

def z375 : W := mkw 0x044b050a0108c024 0xc112c14280423009 0x000300000000c000 0x0000c00000003000

def z376 : W := mkw 0x33b4fa64fc130c0b 0x0ced3e993f04c302 0x0124d870ec030000 0x0049361c3b00c000

def z377 : W := mkw 0x000008002401080a 0x0000020009004202 0x040000000c03081e 0x010000000300c207

def z378 : W := mkw 0x33febb47bc170d1b 0x0cffaed1ef05c346 0xd7dc3b8ffc1f0f1f 0xb5f70ee3ff07c3c7

def z379 : W := mkw 0x0beb3fda1ee00ec0 0x02facff687b803b0 0xfbfb3fff1fe00fe3 0xfefecfffc7f803f8

def z380 : W := mkw 0x0014000480000000 0x0005000120000000 0x001c000fe0000000 0x80070003f8000000

def z381 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0xac031c78e000c8ff 0xeb00c71e3800323f

def z382 : W := mkw 0x03b4800000000000 0x00ed200000000000 0x0124c00000000000 0x0049300000000000

def z383 : W := mkw 0x23feb3469b5aa000 0x08ffacd1a6d6a800 0xdfffe3871ffff002 0xf7fff8e1c7fffc00

def z384 : W := mkw 0x13feb804bf5bac0b 0x04ffae012fd6eb02 0x9fffd800fffff002 0xe7fff6003ffffc00

def z385 : W := mkw 0x005e8000011aa000 0x0017a0000046a800 0x8d3fc0000c7ff002 0xe34ff000031ffc00

def z386 : W := mkw 0x27feb3c7818c8390 0x49ffacf1e06320e4 0x52d82387139c0700 0x14b608e1c4e701c0

def z387 : W := mkw 0x0c4b0d9b1feccff4 0xc312c366c7fb33fd 0xfedb278f1ffccfff 0xffb6c9e3c7ff33ff

def z388 : W := mkw 0x13143005b817051b 0x04c50c016e05c146 0x561c200ff01f071c 0x95870803fc07c1c7

def z389 : W := mkw 0x33fff76fd8160511 0x0cfffddbf6058144 0xf3fffffff01c0701 0xfcfffffffc0701c0

def z390 : W := mkw 0x000000000348a000 0x0000000000d22800 0x0800000003e0f000 0x0200000000f83c00

def z391 : W := mkw 0x0000000000000000 0x0000000000000000 0xe2c0278000000001 0x78b009e000000000

def z392 : W := mkw 0x03fe80001a400000 0x00ffa00006900000 0x9bffc0001fe00002 0xe6fff00007f80000

def z393 : W := mkw 0x00014c286401080a 0x0000530a19004202 0xa527dc78ec03081f 0xe949f71e3b00c207

def z394 : W := mkw 0x23ffff7ee421184a 0x08ffffdfb9084612 0xe3ffffffec633001 0xf8fffffffb18cc00

def z395 : W := mkw 0x00a0800002402000 0x0028200000900800 0x0020c00000603000 0x0008300000180c00

def z396 : W := mkw 0x37ffffeffd9fcfbf 0xcdfffffbff67f3ef 0xffffffffff9fcfff 0xffffffffffe7f3ff

def z397 : W := mkw 0x000008001c000c00 0x0000020007000300 0x100000001c000f02 0x04000000070003c0

def z398 : W := mkw 0x20ebcf7a6421586e 0x883af3de9908561b 0xade7dff8ec63f8ff 0xeb79f7fe3b18fe3f

def z399 : W := mkw 0x03a14c387e61586e 0x80e8530e1f98561b 0xbfe7dc78ffe3f8ff 0xeff9f71e3ff8fe3f

def z400 : W := mkw 0x140008813d9fcfbf 0xc50002204f67f3ef 0x1c0000001f9fcffe 0x0700000007e7f3ff

def z401 : W := mkw 0x13143804bc130c0b 0x04c50e012f04c302 0xc31c380fec030001 0xb0c70e03fb00c000

def z402 : W := mkw 0x005e8000011aa000 0x0017a0000046a800 0x00180000001c0000 0x0006000000070000

def z403 : W := mkw 0x23feb3469b5aa000 0x08ffacd1a6d6a800 0x52d82387139c0000 0x14b608e1c4e70000

def z404 : W := mkw 0x0bfe88901ffaaec0 0x02ffa22407feabb0 0x9fffc0001fffffe2 0xe7fff00007fffff8

def z405 : W := mkw 0x23fff76ec11aa000 0x08fffddbb046a800 0xe7ffffffe01ff001 0xf9fffffff807fc00

def z406 : W := mkw 0x0001443840205064 0x8000510e10081419 0x20000470000000e0 0x0800011c00000038

def z407 : W := mkw 0x1bb57efdfef75fff 0x86ed5fbf7fbdd7ff 0xffffffffffffffff 0xffffffffffffffff

def z408 : W := mkw 0x0014000000120000 0x0005000000048000 0x041c0000001f0000 0x810700000007c000

def z409 : W := mkw 0x13143805a4050d1b 0x04c50e0169014346 0xc31c380fe0000f1d 0xb0c70e03f80003c7

def z410 : W := mkw 0x20007264c0000000 0x08001c9930000000 0x00001870e0000000 0x0000061c38000000

def z411 : W := mkw 0x08a00ad01ee00ec0 0x022802b407b803b0 0x38e007f01fe00fe2 0x4e3801fc07f803f8

def z412 : W := mkw 0x2bfffffedffaaec0 0x0affffffb7feabb0 0xffffffffffffffe3 0xfffffffffffffff8

def z413 : W := mkw 0x2bebfffa5ee00ec0 0x0afafffe97b803b0 0xfbe3fff01fe00fe3 0x7ef8fffc07f803f8

def z414 : W := mkw 0x13143804bc130c0b 0x04c50e012f04c302 0x971c1800fc1f0002 0xa5c706003f07c000

def z415 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x09e7c0000fe3f000 0x4279f00003f8fc00

def z416 : W := mkw 0x03b480001a522000 0x00ed200006948800 0x973cc0001c7f3002 0xa5cf3000071fcc00

def z417 : W := mkw 0x044b050b010cc134 0xc112c142c043304d 0xe6db278f001cc01d 0xf9b6c9e3c0073007

def z418 : W := mkw 0x00000000011aa000 0x000000000046a800 0x04000000001ff000 0x010000000007fc00

def z419 : W := mkw 0x04000081008443b4 0xc1000020402110ed 0x0000000000000ffc 0x00000000000003ff

def z420 : W := mkw 0x044a0183018c8390 0x41128060c06320e4 0xfad82787139c0fe3 0x7eb609e1c4e703f8

def z421 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x97dc00001f9f0002 0xa5f7000007e7c000

def z422 : W := mkw 0x13b4b804be532c0b 0x04ed2e012f94cb02 0x0124d800ec633000 0x004936003b18cc00

def z423 : W := mkw 0x24ebc7ea4188c2a4 0xc93af1fa906230a9 0x28e3c7f00380c0e0 0x4a38f1fc00e03038

def z424 : W := mkw 0x0bfe82d01bfaa2c0 0x02ffa0b406fea8b0 0xbfffc7f01ffff0e2 0xeffff1fc07fffc38

def z425 : W := mkw 0x2001476a40000000 0x080051da90000000 0x200007f000000000 0x080001fc00000000

def z426 : W := mkw 0x0400018300840390 0x41000060c02100e4 0x4000238700000700 0x100008e1c00001c0

def z427 : W := mkw 0x044a0183018c8390 0x41128060c06320e4 0xdedb2387139cc702 0xf7b6c8e1c4e731c0

def z428 : W := mkw 0x23ffb74e80000000 0x08ffedd3a0000000 0xe2db278f00000001 0xf8b6c9e3c0000000

def z429 : W := mkw 0x005fcc38653bf86e 0x8017f30e194efe1b 0xad3fdc78ec7ff8ff 0xeb4ff71e3b1ffe3f

def z430 : W := mkw 0x03a03a5004200840 0x00e80e9401080210 0xebe03ff00c6008e3 0x7af80ffc03180238

def z431 : W := mkw 0x100008013f5fad1b 0x040002004fd7eb46 0x1c0000001fffff1e 0x0700000007ffffc7

def z432 : W := mkw 0x23ffc52edb5aa000 0x08fff14bb6d6a800 0x9fffc00ffffff002 0xe7fff003fffffc00

def z433 : W := mkw 0x13157c3dfc375d7f 0x84c55f0f7f0dd75f 0xf71c3c7ffc1f0fff 0xbdc70f1fff07c3ff

def z434 : W := mkw 0x0314300480000000 0x00c50c0120000000 0x4218200700000000 0x10860801c0000000

def z435 : W := mkw 0x004a010200000000 0x0012804080000000 0x42d8238700000000 0x10b608e1c0000000

def z436 : W := mkw 0x23fff76ec1088000 0x08fffddbb0422000 0xfffffffff39cc003 0xfffffffffce73000

def z437 : W := mkw 0x23b5fe7ce421586e 0x88ed7f9f3908561b 0xad27dc78ec63f8ff 0xeb49f71e3b18fe3f

def z438 : W := mkw 0x044b0d9b25addbfe 0xc112c366c96b76ff 0xfedb278f1fffffff 0xffb6c9e3c7ffffff

def z439 : W := mkw 0x0fffbfdb1ffeeff4 0xc3ffeff6c7ffbbfd 0xffffffff1fffffff 0xffffffffc7ffffff

def z440 : W := mkw 0x0300000018000000 0x00c0000006000000 0x930000001c000002 0x24c0000007000000

def z441 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z442 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0x2cdb078f039cc0fc 0xcb36c1e3c0e7303f

def z443 : W := mkw 0x2bfff7eedac00680 0x0afffdfbb6b001a0 0xf3fffffff3800701 0xfcfffffffce001c0

def z444 : W := mkw 0x0001443840205064 0x8000510e10081419 0xac23c4780060f8ff 0xeb08f11e00183e3f

def z445 : W := mkw 0x10014c397c375d7f 0x8400530e5f0dd75f 0xbd27dc78fc7fffff 0xef49f71e3f1fffff

def z446 : W := mkw 0x03ffcc386421586e 0x80fff30e1908561b 0xafffdc78ec63f8ff 0xebfff71e3b18fe3f

def z447 : W := mkw 0x1000080124050d1b 0x0400020049014346 0x0000000000000f1c 0x00000000000003c7

def z448 : W := mkw 0x13fe8005bb5fa11b 0x04ffa0016ed7e846 0x9fffc00ffffff01e 0xe7fff003fffffc07

def z449 : W := mkw 0x0000081004200840 0x0000020401080210 0x20001c70000008e1 0x0800071c00000238

def z450 : W := mkw 0x0000000001088000 0x0000000000422000 0x1c000000139cc002 0x0700000004e73000

def z451 : W := mkw 0x23ffc52ec0000000 0x08fff14bb0000000 0x83ffc00fe0000000 0xe0fff003f8000000

def z452 : W := mkw 0x0000089004a00ac0 0x00000224012802b0 0xfbe03ff01fe00fe3 0x7ef80ffc07f803f8

def z453 : W := mkw 0x1fff3fdfbfffcfff 0xc7ffcff7effff3ff 0xffff3fffffffcfff 0xffffcffffffff3ff

def z454 : W := mkw 0x13143804bc130c0b 0x04c50e012f04c302 0xd3043800fc030f03 0x34c10e003f00c3c0

def z455 : W := mkw 0x33b4fa65fc170d1b 0x0ced3e997f05c346 0xd73cf87ffc1f0f1f 0xb5cf3e1fff07c3c7

def z456 : W := mkw 0x0000000000000000 0x0000000000000000 0x0124c0000c633000 0x004930000318cc00

def z457 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x16dfc000139ff000 0x85b7f00004e7fc00

def z458 : W := mkw 0x0bea3ad01fe88ec0 0x02fa8eb407fa23b0 0xfffb3ff01ffccfe3 0xfffecffc07ff33f8

def z459 : W := mkw 0x044b058b008443b4 0xc112c162c02110ed 0xe2db278f00000ffd 0xf8b6c9e3c00003ff

def z460 : W := mkw 0x0fa03ad11feccff4 0xc3e80eb447fb33fd 0xffe03ff01ffccfff 0x7ff80ffc07ff33ff

def z461 : W := mkw 0x07ff858b1bdee3b4 0xc1ffe162c6f7b8ed 0xfedb278f139ccfff 0xffb6c9e3c4e733ff

def z462 : W := mkw 0x03a000001a400000 0x00e8000006900000 0x012000000c600000 0x0048000003180000

def z463 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0x641b278f001ccffd 0x9906c9e3c00733ff

def z464 : W := mkw 0x0001443840205064 0x8000510e10081419 0xa927dc78e060f0e1 0xea49f71e38183c38

def z465 : W := mkw 0x03157c3ce421586e 0x80c55f0f3908561b 0xef3ffc7fec63f8ff 0xfbcfff1ffb18fe3f

def z466 : W := mkw 0x004b4d3a6421586e 0x8012d34e9908561b 0xefffffffec63f8ff 0xfbfffffffb18fe3f

def z467 : W := mkw 0x1bb43a55be770d5b 0x06ed0e956f9dc356 0xd73c387ffc7f0f1f 0xb5cf0e1fff1fc3c7

def z468 : W := mkw 0x0000300480000000 0x00000c0120000000 0x4000380fe0000001 0x10000e03f8000000

def z469 : W := mkw 0x0000000000000000 0x0000000000000000 0xa1201c7000000001 0x6848071c00000000

def z470 : W := mkw 0x33ffff6efc130c0b 0x0cffffdbbf04c302 0xe3ffffffec030001 0xf8fffffffb00c000

def z471 : W := mkw 0x004b058a00800280 0x0012c162802000a0 0xfadb278f13800fe3 0xfeb6c9e3c4e003f8

def z472 : W := mkw 0x0ba032d002e002c0 0x02e80cb400b800b0 0xebe03ff003e000e1 0x7af80ffc00f80038

def z473 : W := mkw 0x044b4dbb65addbfe 0xc112d36ed96b76ff 0xfedb3ffff39ccfff 0xffb6cffffce733ff

def z474 : W := mkw 0x23fff76ee001502e 0x88fffddbb800540b 0xe7ffffffe003f01d 0xf9fffffff800fc07

def z475 : W := mkw 0x28ebc7fa42e002c0 0x0a3af1fe90b800b0 0x28e3c7f003e000e0 0x4a38f1fc00f80038

def z476 : W := mkw 0x0401058b008443b4 0xc1004162c02110ed 0xec03278f0000cfff 0xfb00c9e3c00033ff

def z477 : W := mkw 0x23feb34680000000 0x08ffacd1a0000000 0xe3f83ff700000001 0x78fe0ffdc0000000

def z478 : W := mkw 0x03b480001b5aa000 0x00ed200006d6a800 0x1d24c0001ffff002 0x0749300007fffc00

def z479 : W := mkw 0x080000801ac00680 0x0200002006b001a0 0x1000000013800700 0x0400000004e001c0

def z480 : W := mkw 0x244b77efc18cc3b4 0xc912ddfbf06330ed 0xfedb3ffff39ccfff 0xffb6cffffce733ff

def z481 : W := mkw 0x13153c0dbc174d3f 0x84c54f036f05d34f 0xff1f3c0ffc1fcfff 0xffc7cf03ff07f3ff

def z482 : W := mkw 0x205fc52ec0000000 0x0817f14bb0000000 0xa13fdc7fe0000001 0xe84ff71ff8000000

def z483 : W := mkw 0x04eb858a03c8e2a4 0xc13ae16280f238a9 0x28e3c78003e0f0e0 0x4a38f1e000f83c38

def z484 : W := mkw 0x0000000100040110 0x0000000040010044 0x14000000101c0f1e 0x05000000040703c7

def z485 : W := mkw 0x03ff84081b5ae024 0x80ffe10206d6b809 0xbfffc4081ffff8ff 0xeffff10207fffe3f

def z486 : W := mkw 0x2bfff7fec2e002c0 0x0afffdffb0b800b0 0xebffffffe3e000e1 0xfafffffff8f80038

def z487 : W := mkw 0x0000000100040110 0x0000000040010044 0x52182007101c0700 0x14860801c40701c0

def z488 : W := mkw 0x000048306421184a 0x0000120c19084612 0x8d27d870ec63f002 0xe349f61c3b18fc00

def z489 : W := mkw 0x2014c024c0000000 0x0805300930000000 0x0004c000e0000000 0x0001300038000000

def z490 : W := mkw 0x0314000018120000 0x00c5000006048000 0x010400000c030000 0x004100000300c000

def z491 : W := mkw 0x000048306421184a 0x0000120c19084612 0xa924dc70ec6338e3 0x6a49371c3b18ce38

def z492 : W := mkw 0x135f3d0fbc170d1b 0x04d7cf43ef05c346 0xf7df3f8ffc1f0f1f 0xfdf7cfe3ff07c3c7

def z493 : W := mkw 0x0800089004a00ec0 0x02000224012803b0 0x0000000000000fe0 0x00000000000003f8

def z494 : W := mkw 0x0000001000200040 0x0000000400080010 0x28200470006000e0 0x4a08011c00180038

def z495 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0x192018701fe00fe2 0x0648061c07f803f8

def z496 : W := mkw 0x23ffc76a5b5aa000 0x08fff1da96d6a800 0xbfffc7f01ffff002 0xeffff1fc07fffc00

def z497 : W := mkw 0x0001442840005024 0x8000510a10001409 0x0003c0000000f000 0x0000f00000003c00

def z498 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0x68c3278f0380cffd 0x5a30c9e3c0e033ff

def z499 : W := mkw 0x000008102421586e 0x800002040908561b 0xad201c700c63f8ff 0x6b48071c0318fe3f

def z500 : W := mkw 0x30017f6fe4050d1b 0x0c005fdbf9014346 0x60003fffe0000f1d 0x18000ffff80003c7

def z501 : W := mkw 0x13003805bc050d1b 0x04c00e016f014346 0xd300380ffc000f1f 0x34c00e03ff0003c7

def z502 : W := mkw 0x03a03a401c000c00 0x00e80e9007000300 0xf3e03ff01c000f03 0x7cf80ffc070003c0

def z503 : W := mkw 0x131438059c160d11 0x04c50e0167058344 0xd31838071c1c0f03 0x34c60e01c70703c0

def z504 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0xa9201c78ec6008ff 0x6a48071e3b18023f

def z505 : W := mkw 0x004a80000108a000 0x0012a00000422800 0x0003c0000000f000 0x0000f00000003c00

def z506 : W := mkw 0x20ebc76a40000000 0x083af1da90000000 0xe2fbe7ff00000001 0xf8bef9ffc0000000

def z507 : W := mkw 0x08a146f842e052e4 0x822851be10b814b9 0x28e3c7f003e0f0e0 0x4a38f1fc00f83c38

def z508 : W := mkw 0x0001442840000000 0x0000510a10000000 0x20001c78e0000001 0x0800071e38000000

def z509 : W := mkw 0x20017f7ee421586e 0x88005fdfb908561b 0x60003fffe00008fd 0x18000ffff800023f

def z510 : W := mkw 0x0000000018120000 0x0000000006048000 0x140000001c1f0002 0x050000000707c000

def z511 : W := mkw 0x00ebc4384368f064 0x803af10e10da3c19 0x28e3c47003e0f0e0 0x4a38f11c00f83c38

def z512 : W := mkw 0x0000000000004024 0x8000000000001009 0x0c0000000000c8fe 0x030000000000323f

def z513 : W := mkw 0x0400089125addbfe 0xc1000224496b76ff 0x1c0000001ffffffe 0x0700000007ffffff

def z514 : W := mkw 0x07ffcdbb7ffffbfe 0xc1fff36edffffeff 0xffffffffffffffff 0xffffffffffffffff

def z515 : W := mkw 0x03fe80000348a000 0x00ffa00000d22800 0x8bffc00003e0f000 0xe2fff00000f83c00

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0x840000080000081f 0xa100000200000207

def z517 : W := mkw 0x0ba03a501e600c40 0x02e80e9407980310 0xa9201c700c6008e3 0x6a48071c03180238

def z518 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0x56db238f139cc71c 0x95b6c8e3c4e731c7

def z519 : W := mkw 0x03fe800000000000 0x00ffa00000000000 0x8fffc0000c63f002 0xe3fff0000318fc00

def z520 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0x2c001c78ec63f8ff 0x0b00071e3b18fe3f

def z521 : W := mkw 0x035e8000191aa000 0x00d7a0000646a800 0x971fc0001c1ff002 0xa5c7f0000707fc00

def z522 : W := mkw 0x0000000000000000 0x0000000000000000 0xc218200f00000001 0xb0860803c0000000

def z523 : W := mkw 0x0000000000000000 0x0000000000000000 0x96180000101c0002 0xa586000004070000

def z524 : W := mkw 0x03feb2401b5aa000 0x00ffac9006d6a800 0xfffffff01ffff003 0xfffffffc07fffc00

def z525 : W := mkw 0x004a000001088000 0x0012800000422000 0x12d80000139c0000 0x04b6000004e70000

def z526 : W := mkw 0x20ea834200000000 0x083aa0d080000000 0x00c0038000000000 0x003000e000000000

def z527 : W := mkw 0x03fe800000000000 0x00ffa00000000000 0x02d8000000000000 0x00b6000000000000

def z528 : W := mkw 0x0000000000000000 0x0000000000000000 0x81041808e0000001 0xa041060238000000

def z529 : W := mkw 0x0fa13fdb1ee44ff4 0xc3e84ff6c7b913fd 0xfbe03fff1fe00fff 0x7ef80fffc7f803ff

def z530 : W := mkw 0x10140004a013000b 0x040500012804c002 0x00040000e0030000 0x000100003800c000

def z531 : W := mkw 0x0000008000800280 0x00000020002000a0 0x52c0238013800700 0x14b008e004e001c0

def z532 : W := mkw 0x0ba03a501e600c40 0x02e80e9407980310 0x9be018701fe00002 0x66f8061c07f80000

def z533 : W := mkw 0x13143805bf5fad1b 0x04c50e016fd7eb46 0xdf1c380fffffff1f 0xb7c70e03ffffffc7

def z534 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0x62fbe7f700000000 0x58bef9fdc0000000

def z535 : W := mkw 0x0314000118160110 0x00c5000046058044 0xd71c200f1c1f0f1f 0xb5c70803c707c3c7

def z536 : W := mkw 0x04eb858b03cce3b4 0xc13ae162c0f338ed 0xfefbe78f13fcffff 0xffbef9e3c4ff3fff

def z537 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x053fc0000c7ff000 0x814ff000031ffc00

def z538 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0x013fd87fe0000000 0x804ff61ff8000000

def z539 : W := mkw 0x1bb432c59ad60791 0x06ed0cb166b581e4 0x52d82387139c0700 0x14b608e1c4e701c0

def z540 : W := mkw 0x33ffff7ffc375d7f 0x8cffffdfff0dd75f 0xfffffffffc7fffff 0xffffffffff1fffff

def z541 : W := mkw 0x00ea80000348a000 0x003aa00000d22800 0x8de7c0000fe3f002 0xe379f00003f8fc00

def z542 : W := mkw 0x005e800000000000 0x0017a00000000000 0x001fc00000000000 0x8007f00000000000

def z543 : W := mkw 0x04000001010cc134 0xc10000004043304d 0x04000000001cc01c 0x0100000000073007

def z544 : W := mkw 0x08a0025002600040 0x0228009400980010 0x0020007000600000 0x0008001c00180000

def z545 : W := mkw 0x13143005a017011b 0x04c50c016805c046 0xc71c380fe01f001d 0xb1c70e03f807c007

def z546 : W := mkw 0x0ba032401a400400 0x02e80c9006900100 0x0000000000000000 0x0000000000000000

def z547 : W := mkw 0x0ba17ef85ee00ec0 0x02e85fbe17b803b0 0xfbe7fff8ffe00fe3 0xfef9fffe3ff803f8

def z548 : W := mkw 0x045f858b019ee3b4 0xc117e162c067b8ed 0xfedfe78f139fffff 0xffb7f9e3c4e7ffff

def z549 : W := mkw 0x0ba03ac01ec00e80 0x02e80eb007b003a0 0xd3c03b801f800f03 0x34f00ee007e003c0

def z550 : W := mkw 0x1ba03ad5bee50fdb 0x06e80eb56fb943f6 0xfbe03fffffe00fff 0x7ef80ffffff803ff

def z551 : W := mkw 0x205fcd3ee421586e 0x8817f34fb908561b 0xad3fdc7fec63f8ff 0xeb4ff71ffb18fe3f

def z552 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x9edb0000139cc002 0xe7b6c00004e73000

def z553 : W := mkw 0x13157c2dfc175d3f 0x84c55f0b7f05d74f 0xd71ff80ffc1fff1f 0xb5c7fe03ff07ffc7

def z554 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0x051c180fec1f001c 0x81470603fb07c007

def z555 : W := mkw 0x0000402040000000 0x0000100810000000 0x0124d870e0000000 0x0049361c38000000

def z556 : W := mkw 0x00ea80000348a000 0x003aa00000d22800 0x00c0000003800000 0x0030000000e00000

def z557 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0x42dfe38fe0000000 0x90b7f8e3f8000000

def z558 : W := mkw 0x004b4c386529d86e 0x8012d30e194a761b 0xbfffdc78fffff8ff 0xeffff71e3ffffe3f

def z559 : W := mkw 0x27fff7efdbdee3b4 0xc9fffdfbf6f7b8ed 0xffffffffffffffff 0xffffffffffffffff

def z560 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0x2823dc78e060f8fd 0x4a08f71e38183e3f

def z561 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0xa127dc78e00008fd 0xe849f71e3800023f

def z562 : W := mkw 0x0ba03ad01ffaaec0 0x02e80eb407feabb0 0xffe03ff01fffffe3 0x7ff80ffc07fffff8

def z563 : W := mkw 0x2bfebbd69ee00ec0 0x0affaef5a7b803b0 0xfbf83ff71fe00fe3 0x7efe0ffdc7f803f8

def z564 : W := mkw 0x100008013c170d1b 0x040002004f05c346 0xd618200f1c1f0f1f 0xb5860803c707c3c7

def z565 : W := mkw 0x000008102421586e 0x800002040908561b 0x8d041808ec63f8ff 0xa34106023b18fe3f

def z566 : W := mkw 0x1bb43ac5bed70f9b 0x06ed0eb16fb5c3e6 0xd7dc3b8fff9f0f1f 0xb5f70ee3ffe7c3c7

def z567 : W := mkw 0x00a0024000000000 0x0028009000000000 0x20e007f000000000 0x483801fc00000000

def z568 : W := mkw 0x00014c3844205864 0x8000530e11081619 0xa923dc700c60f8e3 0x6a48f71c03183e38

def z569 : W := mkw 0x23b4b24480000000 0x08ed2c9120000000 0x0000000000000000 0x0000000000000000

def z570 : W := mkw 0x0000008000800280 0x00000020002000a0 0x1800000013800fe2 0x0600000004e003f8

def z571 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c0300000000c002 0xe300c00000003000

def z572 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0x2407dc78e003f8fd 0x8901f71e3800fe3f

def z573 : W := mkw 0x0000000000000000 0x0000000000000000 0xa8000400000008e3 0x6a00010000000238

def z574 : W := mkw 0x000040206001100a 0x0000100818004402 0x0004c000e0033000 0x000130003800cc00

def z575 : W := mkw 0x00ebcc386769f86e 0x803af30e19da7e1b 0xade7dc78efe3f8ff 0xeb79f71e3bf8fe3f

def z576 : W := mkw 0x0001040800004024 0x8000410200001009 0xad27c4080c63f8ff 0xeb49f1020318fe3f

def z577 : W := mkw 0x24ebc7eb418cc3b4 0xc93af1fad06330ed 0xfefbe7ff139ccfff 0xffbef9ffc4e733ff

def z578 : W := mkw 0x03a1766840000000 0x00e85d9a10000000 0xe3e7fff8e0000001 0xf8f9fffe38000000

def z579 : W := mkw 0x0014800000122000 0x0005200000048800 0x0004c00000033000 0x000130000000cc00

def z580 : W := mkw 0x000048306421586e 0x8000120c1908561b 0x0d24d870ec63f8fe 0x0349361c3b18fe3f

def z581 : W := mkw 0x03b4c8307e73384a 0x00ed320c1f9cce12 0x0124d870ec633000 0x0049361c3b18cc00

def z582 : W := mkw 0x000000002001502e 0x800000000800540b 0x040000000003f01c 0x010000000000fc07

def z583 : W := mkw 0x07eb37cb018cc3b4 0xc1facdf2c06330ed 0xfffb3fff139ccfff 0xfffecfffc4e733ff

def z584 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x13fcc0001fff3000 0x04ff300007ffcc00

def z585 : W := mkw 0x10000005a005011b 0x0400000168014046 0x0000000fe000001c 0x00000003f8000007

def z586 : W := mkw 0x1014000580160111 0x0405000160058044 0x00180007001c0000 0x00060001c0070000

def z587 : W := mkw 0x000048306421184a 0x0000120c19084612 0x8524d878ec63381f 0xa149361e3b18ce07

def z588 : W := mkw 0x000144286001502e 0x8000510a1800540b 0x00000008e000001c 0x0000000238000007

def z589 : W := mkw 0x10140805a417091b 0x040502016905c246 0x851c180fec1f081f 0xa1470603fb07c207

def z590 : W := mkw 0x1314300598160511 0x04c50c0166058144 0xd31c380ff01c0701 0xb4c70e03fc0701c0

def z591 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0x4104380fec030f1d 0x10410e03fb00c3c7

def z592 : W := mkw 0x080002d000a002c0 0x020000b4002800b0 0x200007f0000000e0 0x080001fc00000038

def z593 : W := mkw 0x0ba07a707e611c4a 0x02e81e9c1f984712 0x0124d870ec633000 0x0049361c3b18cc00

def z594 : W := mkw 0x2bfffffefee15eee 0x8affffffbfb857bb 0xffffffffffe3ffff 0xfffffffffff8ffff

def z595 : W := mkw 0x0fea33c31bcc8790 0x43fa8cf0c6f321e4 0x52d82387139c0700 0x14b608e1c4e701c0

def z596 : W := mkw 0x23feb34680000000 0x08ffacd1a0000000 0xc3ffe38700000000 0xf0fff8e1c0000000

def z597 : W := mkw 0x175f3d0fbd1fcd3f 0xc5d7cf43ef47f34f 0xd71f380ffc1fcf1f 0xb5c7ce03ff07f3c7

def z598 : W := mkw 0x03fec8307f7bb84a 0x00ffb20c1fdeee12 0x9fffd870fffff002 0xe7fff61c3ffffc00

def z599 : W := mkw 0x0314000000000000 0x00c5000000000000 0x831c000000000000 0xa0c7000000000000

def z600 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0x15041800fc1f0f1e 0x054106003f07c3c7

def z601 : W := mkw 0x13143815bc375d7f 0x84c50e056f0dd75f 0xdf1c380ffc7fffff 0xb7c70e03ff1fffff

def z602 : W := mkw 0x1000300580040511 0x04000c0160010144 0x4000200700000700 0x10000801c00001c0

def z603 : W := mkw 0x0300300000000000 0x00c00c0000000000 0xc300380000000001 0x30c00e0000000000

def z604 : W := mkw 0x10003805a4050d1b 0x04000e0169014346 0xc504380fec030f1f 0xb1410e03fb00c3c7

def z605 : W := mkw 0x0001040900044134 0x800041024001104d 0xfe1b240f101ccfff 0xff86c903c40733ff

def z606 : W := mkw 0x100008003c130c0b 0x040002000f04c302 0x000000000c030000 0x000000000300c000

def z607 : W := mkw 0x33feb34798160511 0x0cffacd1e6058144 0x52d82387101c0700 0x14b608e1c40701c0

def z608 : W := mkw 0x23b4f264c0000000 0x08ed3c9930000000 0xc33cf87fe0000001 0xb0cf3e1ff8000000

def z609 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0x7adb2787139cc7e0 0x5eb6c9e1c4e731f8

def z610 : W := mkw 0x23fef264db5aa000 0x08ffbc9936d6a800 0x9fffd870fffff002 0xe7fff61c3ffffc00

def z611 : W := mkw 0x000000001b5aa000 0x0000000006d6a800 0x10000000139c0000 0x0400000004e70000

def z612 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x1ed800001ffff002 0x07b6000007fffc00

def z613 : W := mkw 0x0800009002e002c0 0x0200002400b800b0 0x0800000003e000e0 0x0200000000f80038

def z614 : W := mkw 0x0ba032c01ac00680 0x02e80cb006b001a0 0xfac0278013800fe3 0x7eb009e004e003f8

def z615 : W := mkw 0x23ebf76a40000000 0x08fafdda90000000 0xe3e3fff000000001 0x78f8fffc00000000

def z616 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0x61203ff00c600fe1 0x18480ffc031803f8

def z617 : W := mkw 0x0beabad01fe8aec0 0x02faaeb407fa2bb0 0xfbe3fff01fe0ffe3 0x7ef8fffc07f83ff8

def z618 : W := mkw 0x004b050a00000000 0x0012c14280000000 0x001b000f00000000 0x8006c003c0000000

def z619 : W := mkw 0x000008002401080a 0x0000020009004202 0x00001808e000081d 0x0000060238000207

def z620 : W := mkw 0x0bfeb2c01bdaa680 0x02ffacb006f6a9a0 0x52d82380139c0700 0x14b608e004e701c0

def z621 : W := mkw 0x33ffff6fe4050d1b 0x0cffffdbf9014346 0xe3ffffffe0000f1d 0xf8fffffff80003c7

def z622 : W := mkw 0x305fc52fe017011b 0x0c17f14bf805c046 0x041fc00fe01f001c 0x8107f003f807c007

def z623 : W := mkw 0x245fc5afc18cc3b4 0xc917f16bf06330ed 0xfedfe78ff39ccfff 0xffb7f9e3fce733ff

def z624 : W := mkw 0x23fef264c0000000 0x08ffbc9930000000 0x83ffd870e0000000 0xe0fff61c38000000

def z625 : W := mkw 0x235ff52ec0000000 0x08d7fd4bb0000000 0xc31ff80fe0000001 0xb0c7fe03f8000000

def z626 : W := mkw 0x0ba07af07ee11eca 0x02e81ebc1fb847b2 0xfbe4fff0ffe33fe3 0x7ef93ffc3ff8cff8

def z627 : W := mkw 0x08017ef864a15eee 0x82005fbe192857bb 0xed27fff8ec63ffff 0xfb49fffe3b18ffff

def z628 : W := mkw 0x105e8005a11fa11b 0x0417a0016847e846 0x041fc00fe01ff01c 0x8107f003f807fc07

def z629 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0x3cc30780139ccffe 0x4f30c1e004e733ff

def z630 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0x53e03bf01fe00700 0x14f80efc07f801c0

def z631 : W := mkw 0x0000080004000800 0x0000020001000200 0x810018000c000803 0x2040060003000200

def z632 : W := mkw 0x100008113c375d7f 0x840002044f0dd75f 0x1c0000001c7ffffe 0x07000000071fffff

def z633 : W := mkw 0x00ea800000000000 0x003aa00000000000 0x00e3c00000000000 0x4038f00000000000

def z634 : W := mkw 0x000008103f7bf86e 0x800002040fdefe1b 0x1c0000001ffff8fe 0x0700000007fffe3f

def z635 : W := mkw 0x20a0c26040000000 0x0828309810000000 0x0020c07000000000 0x0008301c00000000

def z636 : W := mkw 0x18003ad5a4a50fdb 0x06000eb5692943f6 0x60003fffe0000ffd 0x18000ffff80003ff

def z637 : W := mkw 0x0fea3bd31fec8fd0 0x43fa8ef4c7fb23f4 0xfbf83ff71ffc0fe3 0x7efe0ffdc7ff03f8

def z638 : W := mkw 0x0ba17e787e615c6e 0x82e85f9e1f98571b 0xad27dc78ec63f8ff 0xeb49f71e3b18fe3f

def z639 : W := mkw 0x00010488008042a4 0x80004122002010a9 0xfec327881380cfff 0xffb0c9e204e033ff

def z640 : W := mkw 0x23fff7eec0800280 0x08fffdfbb02000a0 0xfbfffffff3800fe3 0xfefffffffce003f8

def z641 : W := mkw 0x03a008101e600840 0x00e8020407980210 0xbbe01c701fe008e3 0x6ef8071c07f80238

def z642 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x93ffc000139c0000 0xe4fff00004e70000

def z643 : W := mkw 0x2bfeb3c69ac00680 0x0affacf1a6b001a0 0x52d8238713800700 0x14b608e1c4e001c0

def z644 : W := mkw 0x044b4d3b652dd97e 0xc112d34ed94b765f 0xad3fdc7fec7ff8ff 0xeb4ff71ffb1ffe3f

def z645 : W := mkw 0x07ff850b1b5ee134 0xc1ffe142c6d7b84d 0x9fffc00f1ffff01e 0xe7fff003c7fffc07

def z646 : W := mkw 0x03fe800018120000 0x00ffa00006048000 0x97ffc0001c1f0002 0xe5fff0000707c000

def z647 : W := mkw 0x0ba03ad004a00ec0 0x02e80eb4012803b0 0xe3e03ff000000fe1 0x78f80ffc000003f8

def z648 : W := mkw 0x080008101e600c40 0x0200020407980310 0x000000000c600000 0x0000000003180000

def z649 : W := mkw 0x23fff76fc0040110 0x08fffddbf0010044 0xf7fffffff01c0f1f 0xfdfffffffc0703c7

def z650 : W := mkw 0x27fff7eec188c2a4 0xc9fffdfbb06230a9 0xebffffffe380c0e1 0xfafffffff8e03038

def z651 : W := mkw 0x0ba03a501e600c40 0x02e80e9407980310 0xe3e03ff00c600001 0x78f80ffc03180000

def z652 : W := mkw 0x004b050b00040110 0x0012c142c0010044 0xf6db278f101c0f1f 0xfdb6c9e3c40703c7

def z653 : W := mkw 0x23ffc76a40000000 0x08fff1da90000000 0xa3ffc7f000000000 0xe8fff1fc00000000

def z654 : W := mkw 0x130038013c170d1b 0x04c00e004f05c346 0xd70038001c1f0f1f 0x35c00e000707c3c7

def z655 : W := mkw 0x0000081004200840 0x0000020401080210 0x080000000c6008e2 0x0200000003180238

def z656 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0xa5041c78ec0308ff 0xa941071e3b00c23f

def z657 : W := mkw 0x27fff76fc10cc134 0xc9fffddbf043304d 0xe7ffffffe01cc01d 0xf9fffffff8073007

def z658 : W := mkw 0x0001442840004024 0x8000510a10001009 0xad27dc78e000c8ff 0xeb49f71e3800323f

def z659 : W := mkw 0x205e810680000000 0x0817a041a0000000 0x0018000700000000 0x00060001c0000000

def z660 : W := mkw 0x04000081018cc3b4 0xc1000020406330ed 0xfec02780139ccfff 0x7fb009e004e733ff

def z661 : W := mkw 0x07ff858a1bdae2a4 0xc1ffe16286f6b8a9 0xbfffc7801ffff0e2 0xeffff1e007fffc38

def z662 : W := mkw 0x145f058fa19fc3bf 0xc517c163e867f0ef 0xfedf278ff39fcfff 0xffb7c9e3fce7f3ff

def z663 : W := mkw 0x1314300598160511 0x04c50c0166058144 0xd618200f101c0f1f 0xb5860803c40703c7

def z664 : W := mkw 0x044b0d8b258dcbbe 0xc112c362c96372ef 0xffdf3f8fff9fcfff 0xfff7cfe3ffe7f3ff

def z665 : W := mkw 0x00010c1804204864 0x8000430601081219 0xad231c780c60c8ff 0xeb48c71e0318323f

def z666 : W := mkw 0x0feb3fda1fe8cee4 0xc3facff687fa33b9 0xfbe33ff01fe0cfe3 0x7ef8cffc07f833f8

def z667 : W := mkw 0x031400001b5aa000 0x00c5000006d6a800 0x9f1c00001ffff002 0xa7c7000007fffc00

def z668 : W := mkw 0x0000000000000000 0x0000000000000000 0x892000000c600002 0x6248000003180000

def z669 : W := mkw 0x23ffff7ee421586e 0x88ffffdfb908561b 0xe3ffffffe00008fd 0xf8fffffff800023f

def z670 : W := mkw 0x0bfebad01ffaaec0 0x02ffaeb407feabb0 0xfbf83ff01ffc0fe3 0x7efe0ffc07ff03f8

def z671 : W := mkw 0x08017ef864a15eee 0x82005fbe192857bb 0x60003ff8e0000ffd 0x18000ffe380003ff

def z672 : W := mkw 0x0c4b3fdb05accff4 0xc312cff6c16b33fd 0xfedb3fff139ccfff 0xffb6cfffc4e733ff

def z673 : W := mkw 0x004b050a00004024 0x8012c14280001009 0xeedb278f0000c8ff 0xfbb6c9e3c000323f

def z674 : W := mkw 0x040000811bdee3b4 0xc100002046f7b8ed 0x1c0000001ffffffe 0x0700000007ffffff

def z675 : W := mkw 0x144b3d8fa58dcfbf 0xc512cf63e96373ef 0xfedb3f8ff39ccfff 0xffb6cfe3fce733ff

def z676 : W := mkw 0x000144286001502e 0x8000510a1800540b 0xac07c408e003f8ff 0xeb01f1023800fe3f

def z677 : W := mkw 0x145f050fa11fc13f 0xc517c143e847f04f 0x041f000fe01fc01c 0x8107c003f807f007

def z678 : W := mkw 0x08a14ef866e15aee 0x822853be19b856bb 0xade7dff8efe3f8ff 0xeb79f7fe3bf8fe3f

def z679 : W := mkw 0x10003804a4010c0b 0x04000e0129004302 0x00001800e0000000 0x0000060038000000

def z680 : W := mkw 0x044b0d9b05accbf4 0xc112c366c16b32fd 0xfffb3fff1ffccfff 0xfffecfffc7ff33ff

def z681 : W := mkw 0x03ffc4385b7af064 0x80fff10e16debc19 0xbfffc4701ffff0e2 0xeffff11c07fffc38

def z682 : W := mkw 0x0000000000000000 0x0000000000000000 0x850400000c030002 0xa14100000300c000

def z683 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c0000000c63f002 0x030000000318fc00

def z684 : W := mkw 0x03a0000000000000 0x00e8000000000000 0x83e0000000000000 0x60f8000000000000

def z685 : W := mkw 0x074b3d8b1d8ccfb4 0xc1d2cf62c76333ed 0xffdb3f8f1f9ccfff 0xfff6cfe3c7e733ff

def z686 : W := mkw 0x00014cb864a15aee 0x8000532e192856bb 0xffe7fff8ffe3ffff 0xfff9fffe3ff8ffff

def z687 : W := mkw 0x03a0324000000000 0x00e80c9000000000 0x0120187000000000 0x0048061c00000000

def z688 : W := mkw 0x005fc428611bf02e 0x8017f10a1846fc0b 0x041fc008e01ff01c 0x8107f0023807fc07

def z689 : W := mkw 0x0000081004200840 0x0000020401080210 0x012018700c600000 0x0048061c03180000

def z690 : W := mkw 0x07fe81831bdea390 0x41ffa060c6f7a8e4 0xdfffe3871ffff702 0xf7fff8e1c7fffdc0

def z691 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x1afbc00013fcf000 0x46bef00004ff3c00

def z692 : W := mkw 0x2bffff7ede600c40 0x0affffdfb7980310 0xe3ffffffec600001 0xf8fffffffb180000

def z693 : W := mkw 0x03a0324000000000 0x00e80c9000000000 0x42c0238000000000 0x10b008e000000000

def z694 : W := mkw 0x03feb8001f5aac00 0x00ffae0007d6ab00 0xdffff8001fffff03 0xf7fffe0007ffffc0

def z695 : W := mkw 0x335ffd2ffc170d1b 0x0cd7ff4bff05c346 0xd71ff80ffc1f0f1f 0xb5c7fe03ff07c3c7

def z696 : W := mkw 0x08003ad004a00ec0 0x02000eb4012803b0 0xe9203ff00c600fe3 0x7a480ffc031803f8

def z697 : W := mkw 0x10017c3de4255d7f 0x84005f0f7909575f 0x60003c7fe0000ffd 0x18000f1ff80003ff

def z698 : W := mkw 0x13feb0059b5ea511 0x04ffac0166d7a944 0xdfffe0071ffff702 0xf7fff801c7fffdc0

def z699 : W := mkw 0x0ba03ad11ee40fd0 0x02e80eb447b903f4 0xfff83fff1ffc0fff 0xfffe0fffc7ff03ff

def z700 : W := mkw 0x13feb805bc170d1b 0x04ffae016f05c346 0xd7fff80ffc1f0f1f 0xf5fffe03ff07c3c7

def z701 : W := mkw 0x0c013fdb04a44ff4 0xc3004ff6c12913fd 0x60003fff00000ffd 0x18000fffc00003ff

def z702 : W := mkw 0x1bfebad5bfffafdb 0x06ffaeb56fffebf6 0xffffffffffffffff 0xffffffffffffffff

def z703 : W := mkw 0x03feb24000000000 0x00ffac9000000000 0xe3fffff000000001 0xf8fffffc00000000

def z704 : W := mkw 0x14013d8fa4854fbf 0xc5004f63e92153ef 0x60003f8fe0000ffd 0x18000fe3f80003ff

def z705 : W := mkw 0x1314300498120401 0x04c50c0126048100 0x0000000000000000 0x0000000000000000

def z706 : W := mkw 0x1bb43ad59ef60fd1 0x06ed0eb567bd83f4 0xfbf83ff71ffc0fe3 0x7efe0ffdc7ff03f8

def z707 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0xfac03ff013800fe3 0x7eb00ffc04e003f8

def z708 : W := mkw 0x10140005a017011b 0x040500016805c046 0x561c200ff01f071c 0x95870803fc07c1c7

def z709 : W := mkw 0x23fff76ed91a8000 0x08fffddbb646a000 0xffffffffff9fc003 0xffffffffffe7f000

def z710 : W := mkw 0x04ebc5ba43e8f2e4 0xc13af16e90fa3cb9 0x28e3c7f003e0f0e0 0x4a38f1fc00f83c38

def z711 : W := mkw 0x2001776edb5aa000 0x08005ddbb6d6a800 0x7c003ffffffff003 0x1f000ffffffffc00

def z712 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0xf7dc3f8ffc1f0f1f 0xfdf70fe3ff07c3c7

def z713 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0xe2db3fffe0000001 0xf8b6cffff8000000

def z714 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0x561c380ff01f0f1d 0x95870e03fc07c3c7

def z715 : W := mkw 0x23fff76eda400000 0x08fffddbb6900000 0xf3fffffff3800001 0xfcfffffffce00000

def z716 : W := mkw 0x2015776ec0000000 0x08055ddbb0000000 0x601c3fffe0000001 0x98070ffff8000000

def z717 : W := mkw 0x23fff76ec11aa000 0x08fffddbb046a800 0xefffffffec7ff003 0xfbfffffffb1ffc00

def z718 : W := mkw 0x23a1776eda400000 0x08e85ddbb6900000 0xfbe03fffffe00003 0x7ef80ffffff80000

def z719 : W := mkw 0x03a03ac01c800e80 0x00e80eb0072003a0 0xfbe03ff01f800fe3 0x7ef80ffc07e003f8

def z720 : W := mkw 0x27b4f2e5c18cc3b4 0xc9ed3cb9706330ed 0x1d24d870f39ccffe 0x0749361c3ce733ff

def z721 : W := mkw 0x23b4f366c0000000 0x08ed3cd9b0000000 0x4124fbf7e0000000 0x10493efdf8000000

def z722 : W := mkw 0x23fff76ec2402000 0x08fffddbb0900800 0xe3ffffffe0603001 0xf8fffffff8180c00

def z723 : W := mkw 0x2315776ed8120000 0x08c55ddbb6048000 0xf71c3ffffc1f0003 0xbdc70fffff07c000

def z724 : W := mkw 0x044a0183018cc3b4 0xc1128060c06330ed 0x52d82387139c0ffc 0x14b608e1c4e703ff

def z725 : W := mkw 0x2301776ec0000000 0x08c05ddbb0000000 0xe3003fffe0000001 0x38c00ffff8000000

def z726 : W := mkw 0x13143815bc371d5b 0x04c50e056f0dc756 0xd71c380ffc7f3f1f 0xb5c70e03ff1fcfc7

def z727 : W := mkw 0x23fff76eda400000 0x08fffddbb6900000 0xe3ffffffec600001 0xf8fffffffb180000

def z728 : W := mkw 0x13b43805be570d1b 0x04ed0e016f95c346 0xdffff80fffffff1f 0xf7fffe03ffffffc7

def z729 : W := mkw 0x03b480001b5aa000 0x00ed200006d6a800 0x9d27c0001ffff002 0xe749f00007fffc00

def z730 : W := mkw 0x180008913ef75fff 0x860002244fbdd7ff 0x1c0000001ffffffe 0x0700000007ffffff

def z731 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x9fffc0081ffff81f 0xe7fff00207fffe07

def z732 : W := mkw 0x10140005a017011b 0x040500016805c046 0x441c200fe01f0f1d 0x91070803f807c3c7

def z733 : W := mkw 0x1800089124a50fdb 0x06000224492943f6 0x0000000000000ffc 0x00000000000003ff

def z734 : W := mkw 0x2cebc7fa43e8c2e4 0xcb3af1fe90fa30b9 0x28e3c7f003e0c0e0 0x4a38f1fc00f83038

def z735 : W := mkw 0x13b4b805be572d1b 0x04ed2e016f95cb46 0xdffcf80fffff3f1f 0xf7ff3e03ffffcfc7

def z736 : W := mkw 0x30ebcf6b7c170d1b 0x0c3af3dadf05c346 0x34e3c7f01c1f0f1e 0x4d38f1fc0707c3c7

def z737 : W := mkw 0x0c0008913feddffe 0xc30002244ffb77ff 0x1c0000001ffffffe 0x0700000007ffffff

def z738 : W := mkw 0x044a089125addbfe 0xc1128224496b76ff 0x9fffc0001ffffffe 0xe7fff00007ffffff

def z739 : W := mkw 0x03b5766cc0000000 0x00ed5d9b30000000 0xe3ffffffe0000001 0xf8fffffff8000000

def z740 : W := mkw 0x2001776ec0000000 0x08005ddbb0000000 0x6023ffffe0000001 0x5808fffff8000000

def z741 : W := mkw 0x180008913cb70fdb 0x060002244f2dc3f6 0x140000001c1f0ffe 0x050000000707c3ff

def z742 : W := mkw 0x13b43a45bc170d1b 0x04ed0e916f05c346 0xd73c387ffc1f0f1f 0xb5cf0e1fff07c3c7

def z743 : W := mkw 0x2bb4bad49ee00ec0 0x0aed2eb527b803b0 0xfbe03ff01fe00fe3 0x7ef80ffc07f803f8

def z744 : W := mkw 0x2015f76ec0000000 0x08057ddbb0000000 0x6004ffffe0000001 0x18013ffff8000000

def z745 : W := mkw 0x03ff374e80000000 0x00ffcdd3a0000000 0xe3ff3fffe0000001 0xf8ffcffff8000000

def z746 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0x63fffff7e0000000 0x58fffffdf8000000

def z747 : W := mkw 0x204b776ec0000000 0x0812dddbb0000000 0x62d83fffe0000001 0x18b60ffff8000000

def z748 : W := mkw 0x1bb4ba55be772d5b 0x06ed2e956f9dcb56 0xd73cf87ffc7f3f1f 0xb5cf3e1fff1fcfc7

def z749 : W := mkw 0x10140805bc170d1b 0x040502016f05c346 0xd61c200ffc1f0f1f 0xb5870803ff07c3c7

def z750 : W := mkw 0x0400089125addbfe 0xc1000224496b76ff 0x1c000000139ccffe 0x0700000004e733ff

def z751 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x1d3fc0001ffff002 0x874ff00007fffc00

def z752 : W := mkw 0x23fff76edb5aa000 0x08fffddbb6d6a800 0x72d83ffff39c0001 0x1cb60ffffce70000

def z753 : W := mkw 0x13143005b817051b 0x04c50c016e05c146 0xd71c200ffc1f071e 0xb5c70803ff07c1c7

def z754 : W := mkw 0x205ff76ec0000000 0x0817fddbb0000000 0x60183fffe0000001 0x18060ffff8000000

def z755 : W := mkw 0x031400001b5aa000 0x00c5000006d6a800 0x9f3fc0001ffff002 0xe7cff00007fffc00

def z756 : W := mkw 0x044b452b410cd134 0xc112d14ad043344d 0x041bc00f001cf01c 0x8106f003c0073c07

def z757 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0x61e7ffffe0000001 0x5879fffff8000000

def z758 : W := mkw 0x23fff76edb5ae024 0x88fffddbb6d6b809 0xfffffffffffff8ff 0xfffffffffffffe3f

def z759 : W := mkw 0x07b5858b1ad663b4 0xc1ed6162c6b598ed 0x6124e78f0c633ffd 0x184939e3c318cfff

def z760 : W := mkw 0x044b45ab418cc3b4 0xc112d16ad06330ed 0xfedb3ffff39ccfff 0xffb6cffffce733ff

def z761 : W := mkw 0x044a49b365ad9bda 0x4112926cd96b66f6 0x53fcfbf7ffff3700 0x14ff3efdffffcdc0

def z762 : W := mkw 0x000032c000800280 0x00000cb0002000a0 0xfac03ff013800fe3 0x7eb00ffc04e003f8

def z763 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0xefffffffe000c003 0xfbfffffff8003000

def z764 : W := mkw 0x10143805a4170d1b 0x04050e016905c346 0xc51c380fec1f0f1f 0xb1470e03fb07c3c7

def z765 : W := mkw 0x085ebad005baaec0 0x0217aeb4016eabb0 0x641ffff0001fffe1 0x9907fffc0007fff8

def z766 : W := mkw 0x004a80001b5aa000 0x0012a00006d6a800 0x1c03c0001ffff002 0x0700f00007fffc00

def z767 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0xffe03ff81fe00fff 0xfff80ffe07f803ff

def z768 : W := mkw 0x040144a9418cc3b4 0xc100512a506330ed 0xbd27dc78f39ccfff 0xef49f71e3ce733ff

def z769 : W := mkw 0x0001442840004024 0x8000510a10001009 0xad27dc78ec63f8ff 0xeb49f71e3b18fe3f

def z770 : W := mkw 0x204b776ec0000000 0x0812dddbb0000000 0xe3ffffffe0000001 0xf8fffffff8000000

def z771 : W := mkw 0x2001776ec0000000 0x08005ddbb0000000 0xe1043fffe0000001 0xb8410ffff8000000

def z772 : W := mkw 0x0000000100040110 0x0000000040010044 0xd71c380ff01c0f1f 0xb5c70e03fc0703c7

def z773 : W := mkw 0x10143805a4170d1b 0x04050e016905c346 0xd61c380ff01f0f1f 0xb5870e03fc07c3c7

def z774 : W := mkw 0x205ff76ec0000000 0x0817fddbb0000000 0xe13fffffe0000001 0xf84ffffff8000000

def z775 : W := mkw 0x00fe80001b5aa000 0x003fa00006d6a800 0x1cffc0001ffff002 0xc73ff00007fffc00

def z776 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0xe3ffffffec633001 0xf8fffffffb18cc00

def z777 : W := mkw 0x2bfff76eda400400 0x0afffddbb6900100 0xe3ffffffe0000001 0xf8fffffff8000000

def z778 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0xd318380ffc1c0f1f 0x34c60e03ff0703c7

def z779 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0xfff83ff01ffc0fe3 0xfffe0ffc07ff03f8

def z780 : W := mkw 0x23fff76ed8000000 0x08fffddbb6000000 0xf3fffffffc000003 0xfcffffffff000000

def z781 : W := mkw 0x18b402d5a2f703db 0x062d00b568bdc0f6 0x2cfc07ffe3ff00fc 0xcb3f01fff8ffc03f

def z782 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0xfedfe78f139fffff 0xffb7f9e3c4e7ffff

def z783 : W := mkw 0x23feb3469b5aa000 0x08ffacd1a6d6a800 0xdffffb8ffffff003 0xf7fffee3fffffc00

def z784 : W := mkw 0x1bb408913ef70fdb 0x06ed02244fbdc3f6 0x9ffc00001fff0ffe 0xe7ff000007ffc3ff

def z785 : W := mkw 0x03feb2401b5aa000 0x00ffac9006d6a800 0xdfffe3801ffff002 0xf7fff8e007fffc00

def z786 : W := mkw 0x03ffc52a40000000 0x00fff14a90000000 0xe3ffffffe0000001 0xf8fffffff8000000

def z787 : W := mkw 0x0ceb47fa43e8d2e4 0xc33ad1fe90fa34b9 0x28e3c7f003e0f0e0 0x4a38f1fc00f83c38

def z788 : W := mkw 0x23fff76ed8120000 0x08fffddbb6048000 0xfffffffffc7ff003 0xffffffffff1ffc00

def z789 : W := mkw 0x23febb56a421586e 0x88ffaed5a908561b 0x4ed823870c63f8fe 0x13b608e1c318fe3f

def z790 : W := mkw 0x0ba03ad006e00ec0 0x02e80eb401b803b0 0xebe03ff003e00fe1 0x7af80ffc00f803f8

def z791 : W := mkw 0x0bb4bad01ef22ec0 0x02ed2eb407bc8bb0 0xfffcfff01fff3fe3 0xffff3ffc07ffcff8

def z792 : W := mkw 0x244bc5ab418cc3b4 0xc912f16ad06330ed 0xfedbe78f139ccfff 0xffb6f9e3c4e733ff

def z793 : W := mkw 0x0bb4bad01ef22ec0 0x02ed2eb407bc8bb0 0xfbe03ff01fe00fe3 0x7ef80ffc07f803f8

def z794 : W := mkw 0x23fff76edb5aa000 0x08fffddbb6d6a800 0xf7ffffffff9f0003 0xfdffffffffe7c000

def z795 : W := mkw 0x1b143815be770d5b 0x06c50e056f9dc356 0xd71c380ffc7f0f1f 0xb5c70e03ff1fc3c7

def z796 : W := mkw 0x205fc52ec0000000 0x0817f14bb0000000 0xe3ffffffe0000001 0xf8fffffff8000000

def z797 : W := mkw 0x140008913dbfdfff 0xc50002244f6ff7ff 0x1c0000001ffffffe 0x0700000007ffffff

def z798 : W := mkw 0x0ba03ad01ef22ec0 0x02e80eb407bc8bb0 0xfbe03ff01fe33fe3 0x7ef80ffc07f8cff8

def z799 : W := mkw 0x044a0183018cc3b4 0xc1128060c06330ed 0xded8238f139ccfff 0xb7b608e3c4e733ff

def z800 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0x76db278f139ccffd 0x9db6c9e3c4e733ff

def z801 : W := mkw 0x285fcdbedee00ec0 0x0a17f36fb7b803b0 0x181fc00fffe00fe2 0x8607f003fff803f8

def z802 : W := mkw 0x03fe81021b5aa000 0x00ffa04086d6a800 0xdfffe3871ffff002 0xf7fff8e1c7fffc00

def z803 : W := mkw 0x0ba032d01ae006c0 0x02e80cb406b801b0 0x72c027f0138007e0 0x1cb009fc04e001f8

def z804 : W := mkw 0x0bb4bad01ee00ec0 0x02ed2eb407b803b0 0xfbe4fff01fe00fe3 0x7ef93ffc07f803f8

def z805 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0xfbe4fff01fe33fe3 0x7ef93ffc07f8cff8

def z806 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0x21ffdfffe0000000 0xc87ff7fff8000000

def z807 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0xfbe7fff01fe00fe3 0xfef9fffc07f803f8

def z808 : W := mkw 0x03feb0001b5aa400 0x00ffac0006d6a900 0xdfffe0001ffff702 0xf7fff80007fffdc0

def z809 : W := mkw 0x23fff76ec348a000 0x08fffddbb0d22800 0xfffffffff3fcf003 0xfffffffffcff3c00

def z810 : W := mkw 0x0ba032d002e002c0 0x02e80cb400b800b0 0xfbe03ff013e00fe3 0x7ef80ffc04f803f8

def z811 : W := mkw 0x245fc52fc11ee134 0xc917f14bf047b84d 0x041fc00fe01ff01c 0x8107f003f807fc07

def z812 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0xff27fc78fc63ffff 0xffc9ff1e3f18ffff

def z813 : W := mkw 0x23fff76edb488000 0x08fffddbb6d22000 0xfffffffffffcc003 0xffffffffffff3000

def z814 : W := mkw 0x0ba176e87ac156ae 0x82e85dba1eb055ab 0x56c7e388f383f71c 0x95b1f8e23ce0fdc7

def z815 : W := mkw 0x03a032c01ac00280 0x00e80cb006b000a0 0xfbe03ff01fe00fe3 0x7ef80ffc07f803f8

def z816 : W := mkw 0x0feb3f5b1f6ccd74 0xc3facfd6c7db335d 0x053b187f0c7cc01c 0x814ec61fc31f3007

def z817 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0x39e01ff01fe00fe2 0x4e7807fc07f803f8

def z818 : W := mkw 0x030038013c050d1a 0x00c00e004f014346 0xd71c380ffc1f0f1f 0xb5c70e03ff07c3c7

def z819 : W := mkw 0x03a000001b5aa000 0x00e8000006d6a800 0x9fe7c0001ffff002 0xe7f9f00007fffc00

def z820 : W := mkw 0x005e80001b5aa000 0x0017a00006d6a800 0x9d3fc0001ffff002 0xe74ff00007fffc00

def z821 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0x7ac03ff01fe00fe3 0x1eb00ffc07f803f8

def z822 : W := mkw 0x145f452fe11fd13f 0xc517d14bf847f44f 0x041fc00fe01ff01c 0x8107f003f807fc07

def z823 : W := mkw 0x08003ad004a00ec0 0x02000eb4012803b0 0x72c03ff013800fe1 0x1cb00ffc04e003f8

def z824 : W := mkw 0x13143815bc370d5b 0x04c50e056f0dc356 0xf71c3c7ffc1f0fff 0xbdc70f1fff07c3ff

def z825 : W := mkw 0x0000300580040110 0x00000c0160010044 0xd618380ff01c0f1f 0xb5860e03fc0703c7

def z826 : W := mkw 0x0ba03ad03ee11eca 0x02e80eb40fb847b2 0xfbe03ff01fe33fe3 0x7ef80ffc07f8cff8

def z827 : W := mkw 0x1c0008913fffcfff 0xc70002244ffff3ff 0x1c0000001fffcffe 0x0700000007fff3ff

def z828 : W := mkw 0x175f3d8ebd9bceaf 0xc5d7cf63af66f3ab 0x29c71f80ef83c0e0 0x4a71c7e03be0f038

def z829 : W := mkw 0x23fef366db5aa000 0x08ffbcd9b6d6a800 0xdffffbf7fffff002 0xf7fffefdfffffc00

def z830 : W := mkw 0x23b5f76ec0000000 0x08ed7ddbb0000000 0x60003fffe0000001 0x18000ffff8000000

def z831 : W := mkw 0x24ebc7fa41a8d2e4 0xc93af1fe906a34b9 0x28e3c7f003e0f0e0 0x4a38f1fc00f83c38

def z832 : W := mkw 0x23fff76edb5aa000 0x08fffddbb6d6a800 0xe7ffffffec7ff001 0xf9fffffffb1ffc00

def z833 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0xef3ffc7fec63f8ff 0xfbcfff1ffb18fe3f

def z834 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0x531c380ffc1f0f1d 0x14c70e03ff07c3c7

def z835 : W := mkw 0x204b776ec1088000 0x0812dddbb0422000 0xfedb3ffff39cc003 0xffb6cffffce73000

def z836 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0x62fbffffe0000001 0x58befffff8000000

def z837 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0x7be03ff01fe007e0 0x5ef80ffc07f801f8

def z838 : W := mkw 0x27feb3c79bdea390 0x49ffacf1e6f7a8e4 0x52d82387139c0700 0x14b608e1c4e701c0

def z839 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0xd73cf80ffc7f3f1f 0xb5cf3e03ff1fcfc7

def z840 : W := mkw 0x03a0324480000000 0x00e80c9120000000 0xe3e03fffe0000001 0x78f80ffff8000000

def z841 : W := mkw 0x23fff76ec0004024 0x88fffddbb0001009 0xe7ffffffe000c01d 0xf9fffffff8003007

def z842 : W := mkw 0x23fef366c0000000 0x08ffbcd9b0000000 0xc3fcfbffe0000001 0xb0ff3efff8000000

def z843 : W := mkw 0x0ba03ad49ee00ec0 0x02e80eb527b803b0 0xfbe03fffffe00fe3 0x7ef80ffffff803f8

def z844 : W := mkw 0x23feb2449b5aa000 0x08ffac9126d6a800 0x9fffc0001ffff002 0xe7fff00007fffc00

def z845 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x1efbc0001ffff002 0x47bef00007fffc00

def z846 : W := mkw 0x10140805a4170d1b 0x040502016905c346 0x041c000fe01f0f1c 0x81070003f807c3c7

def z847 : W := mkw 0x23fff76edb5aa000 0x08fffddbb6d6a800 0xebffffffefe3f001 0xfafffffffbf8fc00

def z848 : W := mkw 0x1314300598160511 0x04c50c0166058144 0xd71c380ff01c0f1f 0xb5c70e03fc0703c7

def z849 : W := mkw 0x0bb43ad49ee00ec0 0x02ed0eb527b803b0 0xfbe43ff0ffe00fe3 0x7ef90ffc3ff803f8

def z850 : W := mkw 0x08a03ad006e00ec0 0x02280eb401b803b0 0xe9e03ff00fe00fe3 0x7a780ffc03f803f8

def z851 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0x451c380fec1f0f1d 0x91470e03fb07c3c7

def z852 : W := mkw 0x235f776ec0000000 0x08d7dddbb0000000 0xe3df3fffe0000001 0xf8f7cffff8000000

def z853 : W := mkw 0x205ff76ec11aa000 0x0817fddbb046a800 0x641fffffe01ff001 0x9907fffff807fc00

def z854 : W := mkw 0x0bb43ad01ee00ec0 0x02ed0eb407b803b0 0xfbfc3ff01fe00fe3 0xfeff0ffc07f803f8

def z855 : W := mkw 0x13143a45bc170d1b 0x04c50e916f05c346 0xf71c3ffffc1f0f1f 0xbdc70fffff07c3c7

def z856 : W := mkw 0x180008913ee50fdb 0x060002244fb943f6 0x180000001fe00ffe 0x0600000007f803ff

def z857 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0xefe7fff8ec63f8ff 0xfbf9fffe3b18fe3f

def z858 : W := mkw 0x13b43a45bc170d1b 0x04ed0e916f05c346 0xd7dc3b8ffc1f0f1f 0xb5f70ee3ff07c3c7

def z859 : W := mkw 0x23a1776ec0000000 0x08e85ddbb0000000 0xe3e7ffffe0000001 0xf8f9fffff8000000

def z860 : W := mkw 0x10140005b817051b 0x040500016e05c146 0x141c000ff01f071c 0x85070003fc07c1c7

def z861 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0x613fffffe0000001 0x984ffffff8000000

def z862 : W := mkw 0x004a0081018c8390 0x00128020406320e4 0xfedb278f139ccfff 0xffb6c9e3c4e733ff

def z863 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0x7ae03ff013e00fe1 0x5eb80ffc04f803f8

def z864 : W := mkw 0x23fff76ec1088000 0x08fffddbb0422000 0xfffffffffffff003 0xfffffffffffffc00

def z865 : W := mkw 0x23feb34680000000 0x08ffacd1a0000000 0xe3fc3fffe0000001 0xf8ff0ffff8000000

def z866 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0xfbe43ff8ffe00fe3 0xfef90ffe3ff803f8

def z867 : W := mkw 0x23b5f76ec0000000 0x08ed7ddbb0000000 0xe127ffffe0000001 0xf849fffff8000000

def z868 : W := mkw 0x23fff76ec0004024 0x88fffddbb0001009 0xefffffffec63f8ff 0xfbfffffffb18fe3f

def z869 : W := mkw 0x23b4f264c0000000 0x08ed3c9930000000 0xe3fcffffe0000001 0xf8ff3ffff8000000

def z870 : W := mkw 0x3bb4fa74fe730c4b 0x0eed3e9d3f9cc312 0x0124d870ec630000 0x0049361c3b18c000

def z871 : W := mkw 0x00fe8000035aa000 0x003fa00000d6a800 0x8dffc0000ffff002 0xe37ff00003fffc00

def z872 : W := mkw 0x23eb776ec0000000 0x08fadddbb0000000 0xe3fb3fffe0000001 0xf8fecffff8000000

def z873 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0x2d27dc70ec63f8fe 0x4b49f71c3b18fe3f

def z874 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0xe3dc3fffe0000001 0xb8f70ffff8000000

def z875 : W := mkw 0x08003ad004a00ec0 0x02000eb4012803b0 0x68c03ff003800fe1 0x5a300ffc00e003f8

def z876 : W := mkw 0x0001452a40000000 0x0000514a90000000 0x60003fffe0000001 0x18000ffff8000000

def z877 : W := mkw 0x000008102421084a 0x0000020409084212 0xad27dc78ec63f8ff 0xeb49f71e3b18fe3f

def z878 : W := mkw 0x0314300598160110 0x00c50c0166058044 0xd71c380ffc1f0f1f 0xb5c70e03ff07c3c7

def z879 : W := mkw 0x23fff76eda522000 0x08fffddbb6948800 0xf7fffffffc7f3003 0xfdffffffff1fcc00

def z880 : W := mkw 0x244bc52b410cc134 0xc912f14ad043304d 0x041bc00f001cc01c 0x8106f003c0073007

def z881 : W := mkw 0x08a00ad006e00ac0 0x022802b401b802b0 0xfbe03ff01fe00fe3 0x7ef80ffc07f803f8

def z882 : W := mkw 0x044b858b018ce3b4 0xc112e162c06338ed 0xfedbe78f139cffff 0xffb6f9e3c4e73fff

def z883 : W := mkw 0x23fff76ec108a000 0x08fffddbb0422800 0xe3ffffffe000f001 0xf8fffffff8003c00

def z884 : W := mkw 0x03feb2449b5aa000 0x00ffac9126d6a800 0xfffffffffffff003 0xfffffffffffffc00

def z885 : W := mkw 0x00a002c000800280 0x002800b0002000a0 0xfae027f013800fe3 0x7eb809fc04e003f8

def z886 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0xfffb278f1ffccfff 0xfffec9e3c7ff33ff

def z887 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0xdf1c380ffc7fff1f 0xb7c70e03ff1fffc7

def z888 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0xff1c3c0ffc1f0fff 0xffc70f03ff07c3ff

def z889 : W := mkw 0x044b45aa4188c2a4 0xc112d16a906230a9 0x28e3c7f00380c0e0 0x4a38f1fc00e03038

def z890 : W := mkw 0x08003ad01ee00ec0 0x02000eb407b803b0 0xfac03ff01fe00fe3 0x7eb00ffc07f803f8

def z891 : W := mkw 0x10003805a4050d1b 0x04000e0169014346 0x4418380fe01c0f1d 0x91060e03f80703c7

def z892 : W := mkw 0x23fff76eda522000 0x08fffddbb6948800 0xfbffffffffe33003 0xfefffffffff8cc00

def z893 : W := mkw 0x0bfeb2401b5aa400 0x02ffac9006d6a900 0x9fffc0001ffff002 0xe7fff00007fffc00

def z894 : W := mkw 0x0b003ad01ca00ec0 0x02c00eb4072803b0 0xfbc03ff01f800fe3 0x7ef00ffc07e003f8

def z895 : W := mkw 0x20fff76ec0000000 0x083ffddbb0000000 0x60ffffffe0000001 0xd83ffffff8000000

def z896 : W := mkw 0x031408013c17091a 0x00c502004f05c246 0xd71c380ffc1f0f1f 0xb5c70e03ff07c3c7

def z897 : W := mkw 0x33b4ba45bc170d1b 0x0ced2e916f05c346 0xd71c380ffc1f0f1f 0xb5c70e03ff07c3c7

def z898 : W := mkw 0x00ea80001b5aa000 0x003aa00006d6a800 0x9de7c0001ffff002 0xe779f00007fffc00

def z899 : W := mkw 0x2001776ec0000000 0x08005ddbb0000000 0xe2c03fffe0000001 0x78b00ffff8000000

def z900 : W := mkw 0x23fff76ed91aa000 0x08fffddbb646a800 0xf7fffffffc1ff003 0xfdffffffff07fc00

def z901 : W := mkw 0x2001776ec0000000 0x08005ddbb0000000 0x6124ffffe0000001 0x18493ffff8000000

def z902 : W := mkw 0x23ebf76ec0000000 0x08fafddbb0000000 0xe3e3ffffe0000001 0x78f8fffff8000000

def z903 : W := mkw 0x08a002d002e002c0 0x022800b400b800b0 0x68e027f003e00fe1 0x5a3809fc00f803f8

def z904 : W := mkw 0x0314324480000000 0x00c50c9120000000 0xe31c3fffe0000001 0xb8c70ffff8000000

def z905 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0x151c180ffc1f0f1e 0x85470603ff07c3c7

def z906 : W := mkw 0x20a1f76ec0000000 0x08287ddbb0000000 0x6020ffffe0000001 0x18083ffff8000000

def z907 : W := mkw 0x13143815bc370d5b 0x04c50e056f0dc356 0xd73c387ffc7f0f1f 0xb5cf0e1fff1fc3c7

def z908 : W := mkw 0x0000324480000000 0x00000c9120000000 0x60003fffe0000001 0x18000ffff8000000

def z909 : W := mkw 0x204b776ec0000000 0x0812dddbb0000000 0x60c33fffe0000001 0x5830cffff8000000

def z910 : W := mkw 0x044b45ab418cc3b4 0xc112d16ad06330ed 0xfefbe7ff139ccfff 0xffbef9ffc4e733ff

def z911 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0xe7ffffffec030003 0xf9fffffffb00c000

def z912 : W := mkw 0x23fff76ec11aa000 0x08fffddbb046a800 0xe3ffffffe01c0001 0xf8fffffff8070000

def z913 : W := mkw 0x04000081018cc3b4 0xc1000020406330ed 0xfed8278f139ccfff 0xffb609e3c4e733ff

def z914 : W := mkw 0x0ba032c01ac00680 0x02e80cb006b001a0 0xfbe03ff013800fe3 0x7ef80ffc04e003f8

def z915 : W := mkw 0x13b43a55bc370d5b 0x04ed0e956f0dc356 0xfffc3ffffc7f0fff 0xffff0fffff1fc3ff

def z916 : W := mkw 0x004a00001b5aa000 0x0012800006d6a800 0x9fffc0001ffff002 0xe7fff00007fffc00

def z917 : W := mkw 0x13143005b817051b 0x04c50c016e05c146 0xd61c200ff01f0f1f 0xb5870803fc07c3c7

def z918 : W := mkw 0x0ba002d01ae002c0 0x02e800b406b800b0 0xfbe027f01fe00fe3 0x7ef809fc07f803f8

def z919 : W := mkw 0x0400089124a55bfe 0xc1000224492956ff 0x0c0000000c63fffe 0x030000000318ffff

def z920 : W := mkw 0x08a00ad006e00ec0 0x022802b401b803b0 0x28e007f003e00fe0 0x4a3801fc00f803f8

def z921 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0xfad8278f139c0fff 0x7eb609e3c4e703ff

def z922 : W := mkw 0x03ffcc387f7bf86e 0x80fff30e1fdefe1b 0x32d81c78f39c08fd 0x0cb6071e3ce7023f

def z923 : W := mkw 0x23fff76ec1088000 0x08fffddbb0422000 0xf3fffffff39c0001 0xfcfffffffce70000

def z924 : W := mkw 0x10140005a017011b 0x040500016805c046 0x141c000ff01f0f1e 0x85070003fc07c3c7

def z925 : W := mkw 0x0400089124a55bfe 0xc1000224492956ff 0x0000000000000ffc 0x00000000000003ff

def z926 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0x7edb2787139ccffe 0x5fb6c9e1c4e733ff

def z927 : W := mkw 0x03feb2401b5aa000 0x00ffac9006d6a800 0x9fffd8701ffff002 0xe7fff61c07fffc00

def z928 : W := mkw 0x13b43805be570d1b 0x04ed0e016f95c346 0xd73c380ffc7f0f1f 0xb5cf0e03ff1fc3c7

def z929 : W := mkw 0x13143805be570d1b 0x04c50e016f95c346 0xdf1c380fffff0f1f 0xb7c70e03ffffc3c7

def z930 : W := mkw 0x08a03ad01ee00ec0 0x02280eb407b803b0 0x78e03ff01fe00fe3 0x5e380ffc07f803f8

def z931 : W := mkw 0x03fe82401b5aa000 0x00ffa09006d6a800 0xbfffc7f01ffff002 0xeffff1fc07fffc00

def z932 : W := mkw 0x005e8000011aa000 0x0017a0000046a800 0x9fffc0001ffff002 0xe7fff00007fffc00

def z933 : W := mkw 0x03feb0001b5aa000 0x00ffac0006d6a800 0xdffff8001ffff003 0xf7fffe0007fffc00

def z934 : W := mkw 0x2001776ec0004024 0x88005ddbb0001009 0x60003fffe00008fd 0x18000ffff800023f

def z935 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0xbfffdc701ffff003 0xeffff71c07fffc00

def z936 : W := mkw 0x03feb0049b5aa000 0x00ffac0126d6a800 0xdfffe0071ffff002 0xf7fff801c7fffc00

def z937 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0xd71ff80ffc1fff1f 0xb5c7fe03ff07ffc7

def z938 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0xe7ffffffe003f001 0xf9fffffff800fc00

def z939 : W := mkw 0x00010489008443b4 0x80004122402110ed 0xfedb278f139ccfff 0xffb6c9e3c4e733ff

def z940 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0xffffe7801ffff003 0xfffff9e007fffc00

def z941 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0xffdf3f8ff39ccfff 0xfff7cfe3fce733ff

def z942 : W := mkw 0x1bb43a55be770d5b 0x06ed0e956f9dc356 0xdffc387fffff0f1f 0xf7ff0e1fffffc3c7

def z943 : W := mkw 0x13143805a4170d1b 0x04c50e016905c346 0xc71c380fe01f0f1d 0xb1c70e03f807c3c7

def z944 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0xfbe3fff01fe0ffe3 0x7ef8fffc07f83ff8

def z945 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0x2927dc78ec63f8fd 0x4a49f71e3b18fe3f

def z946 : W := mkw 0x20ebf76ec0000000 0x083afddbb0000000 0xe1e7ffffe0000001 0xf879fffff8000000

def z947 : W := mkw 0x030038901ca00ec0 0x00c00e24072803b0 0xfbe03ff01fe00fe3 0x7ef80ffc07f803f8

def z948 : W := mkw 0x1314b805bc172d1b 0x04c52e016f05cb46 0xd71cf80ffc1f3f1f 0xb5c73e03ff07cfc7

def z949 : W := mkw 0x0ba032d01ae006c0 0x02e80cb406b801b0 0xfbe03ff013e007e1 0x7ef80ffc04f801f8

def z950 : W := mkw 0x23fe83421b5aa000 0x08ffa0d086d6a800 0x9fffc3801ffff002 0xe7fff0e007fffc00

def z951 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0xdfffe00f1ffff003 0xf7fff803c7fffc00

def z952 : W := mkw 0x13143005b817051b 0x04c50c016e05c146 0xd71c380ff01f071d 0xb5c70e03fc07c1c7

def z953 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0x5618380ffc1f0f1f 0x15860e03ff07c3c7

def z954 : W := mkw 0x13feb0049b5aa401 0x04ffac0126d6a900 0x9fffc0001ffff002 0xe7fff00007fffc00

def z955 : W := mkw 0x0001452a40000000 0x0000514a90000000 0xe127ffffe0000001 0xf849fffff8000000

def z956 : W := mkw 0x345fc52fe11fc13f 0xcd17f14bf847f04f 0x041fc00fe01fc01c 0x8107f003f807f007

def z957 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0xdf3c380ffc7f0f1f 0xf7cf0e03ff1fc3c7

def z958 : W := mkw 0x1315743dd8365575 0x84c55d0f760d955d 0x7a3be477107cf7e0 0x5e8ef91dc41f3df8

def z959 : W := mkw 0x23fff76ed8000400 0x08fffddbb6000100 0xf3fffffff0000701 0xfcfffffffc0001c0

def z960 : W := mkw 0x0bb43ad49ee00ec0 0x02ed0eb527b803b0 0xfbf83ff71fe00fe3 0x7efe0ffdc7f803f8

def z961 : W := mkw 0x13140805bc170d1b 0x04c502016f05c346 0x971c000ffc1f0f1e 0xa5c70003ff07c3c7

def z962 : W := mkw 0x10eab805a74dad1b 0x043aae0169d36b46 0x48e3f80fe3e0ff1d 0x5238fe03f8f83fc7

def z963 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x0dffc0000ffff000 0xc37ff00003fffc00

def z964 : W := mkw 0x031438059c040d10 0x00c50e0167010344 0xd71c380ffc1c0f1f 0xb5c70e03ff0703c7

def z965 : W := mkw 0x13b43805be570d1b 0x04ed0e016f95c346 0xd7dc380fff9f0f1f 0xb5f70e03ffe7c3c7

def z966 : W := mkw 0x23fff76ec0120000 0x08fffddbb0048000 0xe7ffffffe01f0001 0xf9fffffff807c000

def z967 : W := mkw 0x03ea80001b5aa000 0x00faa00006d6a800 0x9fe3c0001ffff002 0x67f8f00007fffc00

def z968 : W := mkw 0x03ffc52a5b5aa000 0x00fff14a96d6a800 0xfffffffffffff003 0xfffffffffffffc00

def z969 : W := mkw 0x23fff76edb5aa000 0x08fffddbb6d6a800 0xf7fffffff39ff001 0xfdfffffffce7fc00

def z970 : W := mkw 0x23feb3469b5aa000 0x08ffacd1a6d6a800 0xfffffff71ffff003 0xfffffffdc7fffc00

def z971 : W := mkw 0x000000001b5aa000 0x0000000006d6a800 0x1c07c0001ffff002 0x8701f00007fffc00

def z972 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0xffe33ff01fe0cfe3 0xfff8cffc07f833f8

def z973 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x1edfc0001ffff002 0x87b7f00007fffc00

def z974 : W := mkw 0x0ba03ad03ee10eca 0x02e80eb40fb843b2 0xffe03ff01fe30fff 0x7ff80ffc07f8c3ff

def z975 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0xfbf83fff1fe00fe3 0xfefe0fffc7f803f8

def z976 : W := mkw 0x03feb0049b5aa000 0x00ffac0126d6a800 0x9fffd800fffff002 0xe7fff6003ffffc00

def z977 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0x2527dc78ec63f8fd 0x8949f71e3b18fe3f

def z978 : W := mkw 0x23a1776ec0000000 0x08e85ddbb0000000 0x62c03fffe0000001 0x18b00ffff8000000

def z979 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0xffe43ff01fe30fe3 0xfff90ffc07f8c3f8

def z980 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0xebffffffe00008e3 0xfafffffff8000238

def z981 : W := mkw 0x23fff76ed8120000 0x08fffddbb6048000 0xf3fffffff01c0001 0xfcfffffffc070000

def z982 : W := mkw 0x0bb4bad01ef22ec0 0x02ed2eb407bc8bb0 0xffe7fff01fe3ffe3 0xfff9fffc07f8fff8

def z983 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x1bffc0001ffff000 0x46fff00007fffc00

def z984 : W := mkw 0x13140005b817011b 0x04c500016e05c046 0xd71c200ffc1f0f1f 0xb5c70803ff07c3c7

def z985 : W := mkw 0x2001776ec0000000 0x08005ddbb0000000 0xed27ffffec63f003 0xfb49fffffb18fc00

def z986 : W := mkw 0x0000009000a002c0 0x00000024002800b0 0xfae027f013e00fe3 0x7eb809fc04f803f8

def z987 : W := mkw 0x10140805bc170d1b 0x040502016f05c346 0x951c180ffc1f0f1f 0xa5470603ff07c3c7

def z988 : W := mkw 0x235ff76ec0000000 0x08d7fddbb0000000 0xe31fffffe0000001 0xb8c7fffff8000000

def z989 : W := mkw 0x13143815bc370d5b 0x04c50e056f0dc356 0xff3ffc7ffc7fffff 0xffcfff1fff1fffff

def z990 : W := mkw 0x03b432449a520000 0x00ed0c9126948000 0xfffc3fffffff0003 0xffff0fffffffc000

def z991 : W := mkw 0x244b452fc10cc134 0xc912d14bf043304d 0x041b000fe01cc01c 0x8106c003f8073007

def z992 : W := mkw 0x03fe80049b5aa000 0x00ffa00126d6a800 0x9fffc00ffffff002 0xe7fff003fffffc00

def z993 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0x63fcffffe0000001 0x18ff3ffff8000000

def z994 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0xf73c3c7ffc1f0f1f 0xfdcf0f1fff07c3c7

def z995 : W := mkw 0x23fef366c0000000 0x08ffbcd9b0000000 0xc3fffbf7e0000000 0xf0fffefdf8000000

def z996 : W := mkw 0x08a00ad01ee00ec0 0x022802b407b803b0 0xb9e01ff01fe00fe3 0x6e7807fc07f803f8

def z997 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0xbfe7dc78ffe3f8ff 0xeff9f71e3ff8fe3f

def z998 : W := mkw 0x13b43805bc170d1b 0x04ed0e016f05c346 0xd7fc380ffc1f0f1f 0xf5ff0e03ff07c3c7

def z999 : W := mkw 0x0ba03ad03ee10eca 0x02e80eb40fb843b2 0xfbe03ff8ffe00fff 0x7ef80ffe3ff803ff

def z1000 : W := mkw 0x13003805bc050d1b 0x04c00e016f014346 0xd718380ffc1c0f1f 0xb5c60e03ff0703c7

def z1001 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0xf3fffffff0000f03 0xfcfffffffc0003c0

def z1002 : W := mkw 0x0bb43ad01ef20ec0 0x02ed0eb407bc83b0 0xfbf83ff01ffc0fe3 0x7efe0ffc07ff03f8

def z1003 : W := mkw 0x1bb4bad4bef32ecb 0x06ed2eb52fbccbb2 0xfbe4fff0ffe33fe3 0x7ef93ffc3ff8cff8

def z1004 : W := mkw 0x24ebc7ea43c8e2a4 0xc93af1fa90f238a9 0x28e3c7f003e0f0e0 0x4a38f1fc00f83c38

def z1005 : W := mkw 0x2001776ec0000000 0x08005ddbb0000000 0xe2183fffe0000001 0xb8860ffff8000000

def z1006 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0xf3e03ff013800fe1 0x7cf80ffc04e003f8

def z1007 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0xe3f83fffe0000001 0x78fe0ffff8000000

def z1008 : W := mkw 0x035e0000191a8000 0x00d780000646a000 0x9fffc0001ffff002 0xe7fff00007fffc00

def z1009 : W := mkw 0x33fff76ed8120401 0x0cfffddbb6048100 0xe3ffffffe0000001 0xf8fffffff8000000

def z1010 : W := mkw 0x000000001b5aa000 0x0000000006d6a800 0x1c23c0001ffff002 0x4708f00007fffc00

def z1011 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0xd73ff80ffc1f0f1f 0xf5cffe03ff07c3c7

def z1012 : W := mkw 0x13143005a017011b 0x04c50c016805c046 0xd71c380ff01f0f1f 0xb5c70e03fc07c3c7

def z1013 : W := mkw 0x23fff76edb48a000 0x08fffddbb6d22800 0xfbffffffffe0f003 0xfefffffffff83c00

def z1014 : W := mkw 0x044b452b610dd13e 0xc112d14ad843744f 0x041b000fe01cc01c 0x8106c003f8073007

def z1015 : W := mkw 0x204b776ec0000000 0x0812dddbb0000000 0x601b3fffe0000001 0x9806cffff8000000

def z1016 : W := mkw 0x20007366c0000000 0x08001cd9b0000000 0x40003bf7e0000000 0x10000efdf8000000

def z1017 : W := mkw 0x10003805a4050d1b 0x04000e0169014346 0x5218380ff01c0f1d 0x14860e03fc0703c7

def z1018 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0xdfffe0001fffff03 0xf7fff80007ffffc0

def z1019 : W := mkw 0x244bc5aa4188c2a4 0xc912f16a906230a9 0x28c3c7800380c0e0 0x4a30f1e000e03038

def z1020 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0x7adb278f139ccffd 0x5eb6c9e3c4e733ff

def z1021 : W := mkw 0x000000012005011a 0x0000000048014046 0xd61c200ff01f0f1f 0xb5870803fc07c3c7

def z1022 : W := mkw 0x20ebf76ec348a000 0x083afddbb0d22800 0x68e3ffffe3e0f001 0x5a38fffff8f83c00

def z1023 : W := mkw 0x205ff76ec0000000 0x0817fddbb0000000 0xe2dfffffe0000001 0xf8b7fffff8000000

def z1024 : W := mkw 0x10000005a005011b 0x0400000168014046 0xd618200ff01c0f1f 0xb5860803fc0703c7

def z1025 : W := mkw 0x03feb24480000000 0x00ffac9120000000 0xe3ffffffe0000001 0xf8fffffff8000000

def z1026 : W := mkw 0x045fc52b611ff13e 0xc117f14ad847fc4f 0x041fc00fe01ff01c 0x8107f003f807fc07

def z1027 : W := mkw 0x035f752ec0000000 0x00d7dd4bb0000000 0xe3ffffffe0000001 0xf8fffffff8000000

def z1028 : W := mkw 0x14017dbfe4a55fff 0xc5005f6ff92957ff 0x60003fffe0000ffd 0x18000ffff80003ff

def z1029 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0x7ae027f01fe00fe2 0x5eb809fc07f803f8

def z1030 : W := mkw 0x13b43a45be570d1b 0x04ed0e916f95c346 0xfffc3fffffff0f1f 0xffff0fffffffc3c7

def z1031 : W := mkw 0x13b4b805be572d1b 0x04ed2e016f95cb46 0xd71c380ffc1f0f1f 0xb5c70e03ff07c3c7

def z1032 : W := mkw 0x03143805a405091a 0x00c50e0169014246 0xd71c380ffc1f0f1f 0xb5c70e03ff07c3c7

def z1033 : W := mkw 0x23fef366c0000000 0x08ffbcd9b0000000 0xe3fcfff7e0000001 0x78ff3ffdf8000000

def z1034 : W := mkw 0x23fff76edb5aa000 0x08fffddbb6d6a800 0xfbfffffffffc0003 0xfeffffffffff0000

def z1035 : W := mkw 0x204bf76ec0000000 0x0812fddbb0000000 0x6003ffffe0000001 0x1800fffff8000000

def z1036 : W := mkw 0x23fff76ec0005024 0x88fffddbb0001409 0xe3ffffffe000f001 0xf8fffffff8003c00

def z1037 : W := mkw 0x2001776ec0000000 0x08005ddbb0000000 0xe1203fffe0000001 0x78480ffff8000000

def z1038 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0xdf1f380ffc1fcf1f 0xf7c7ce03ff07f3c7

def z1039 : W := mkw 0x044b45ba41a8d2e4 0xc112d16e906a34b9 0x28c307f00380c0e0 0x4a30c1fc00e03038

def z1040 : W := mkw 0x004b452a41088000 0x0012d14a90422000 0xfffffffffffff003 0xfffffffffffffc00

def z1041 : W := mkw 0x23fff76eda522000 0x08fffddbb6948800 0xefffffffec63f003 0xfbfffffffb18fc00

def z1042 : W := mkw 0x0bb43ad49ef20ec0 0x02ed0eb527bc83b0 0xfffc3fffffff0fe3 0xffff0fffffffc3f8

def z1043 : W := mkw 0x1bb43a55be770d5b 0x06ed0e956f9dc356 0xf7fc3ffffc7f0f1f 0xfdff0fffff1fc3c7

def z1044 : W := mkw 0x23fff76ec0004024 0x88fffddbb0001009 0xe3ffffffe00008fd 0xf8fffffff800023f

def z1045 : W := mkw 0x24017fffe4a55bfe 0xc9005ffff92956ff 0x60003fffe0000ffd 0x18000ffff80003ff

def z1046 : W := mkw 0x244b47ea4188c2a4 0xc912d1fa906230a9 0x28c307f00380c0e0 0x4a30c1fc00e03038

def z1047 : W := mkw 0x20ebf76ec0000000 0x083afddbb0000000 0x60c03fffe0000001 0x18300ffff8000000

def z1048 : W := mkw 0x044a0183018cc3b4 0xc1128060c06330ed 0xfed82787139ccfff 0x7fb609e1c4e733ff

def z1049 : W := mkw 0x23fef366db5aa000 0x08ffbcd9b6d6a800 0x53fcfbf7ffff3000 0x14ff3efdffffcc00

def z1050 : W := mkw 0x000008012405091a 0x0000020049014246 0xd618380ff01c0f1f 0xb5860e03fc0703c7

def z1051 : W := mkw 0x07fe88913ffffbfe 0xc1ffa2244ffffeff 0x9fffc0001ffffffe 0xe7fff00007ffffff

def z1052 : W := mkw 0x23fe81069b5aa000 0x08ffa041a6d6a800 0x9fffc0071ffff002 0xe7fff001c7fffc00

def z1053 : W := mkw 0x044b45ab418cd3b4 0xc112d16ad06334ed 0xfedbe78f139cffff 0xffb6f9e3c4e73fff

def z1054 : W := mkw 0x044b45ab418cc3b4 0xc112d16ad06330ed 0xffffffffffffffff 0xffffffffffffffff

def z1055 : W := mkw 0x18017efde4a55fff 0x86005fbf792957ff 0x60003fffe0000ffd 0x18000ffff80003ff

def z1056 : W := mkw 0x1bb4ba54be732c4b 0x06ed2e952f9ccb12 0x0124d870ec633000 0x0049361c3b18cc00

def z1057 : W := mkw 0x1bb43ad4bef30ecb 0x06ed0eb52fbcc3b2 0xfbfc3fffffe30fe3 0xfeff0ffffff8c3f8

def z1058 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0xd31c380ff01c0f1d 0xb4c70e03fc0703c7

def z1059 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0xbfffc4001ffff8e3 0xeffff10007fffe38

def z1060 : W := mkw 0x23fff76ec2400000 0x08fffddbb0900000 0xebffffffe3e00001 0xfafffffff8f80000

def z1061 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0xffffe78f139ccfff 0xfffff9e3c4e733ff

def z1062 : W := mkw 0x1bb47a74fe731c4b 0x06ed1e9d3f9cc712 0x0124d870ec633000 0x0049361c3b18cc00

def z1063 : W := mkw 0x044a0183018c8390 0x41128060c06320e4 0xfed8278f139c0fff 0xffb609e3c4e703ff

def z1064 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0xbf3fdc78fc7ff8ff 0xefcff71e3f1ffe3f

def z1065 : W := mkw 0x0401058b008443b4 0xc1004162c02110ed 0xfed8278f139c0fff 0xffb609e3c4e703ff

def z1066 : W := mkw 0x08a03ad006e00ec0 0x02280eb401b803b0 0x60c03ff003800fe1 0x18300ffc00e003f8

def z1067 : W := mkw 0x004b0d1a2421586e 0x8012c3468908561b 0xeedb278f0c63f8ff 0xfbb6c9e3c318fe3f

def z1068 : W := mkw 0x23fff76ec1088000 0x08fffddbb0422000 0xe7ffffffe01cc001 0xf9fffffff8073000

def z1069 : W := mkw 0x0ba0bad01ee02ec0 0x02e82eb407b80bb0 0xfbe0fff01fe03fe3 0x7ef83ffc07f80ff8

def z1070 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0xffdf278f1f9fcfff 0xfff7c9e3c7e7f3ff

def z1071 : W := mkw 0x004b452a40000000 0x0012d14a90000000 0xe2db3fffe0000001 0xf8b6cffff8000000

def z1072 : W := mkw 0x08a032d002e006c0 0x02280cb400b801b0 0x68e027f003e007e0 0x5a3809fc00f801f8

def z1073 : W := mkw 0x1bfe88913fffafdb 0x06ffa2244fffebf6 0x9fffc0001ffffffe 0xe7fff00007ffffff

def z1074 : W := mkw 0x0ba00ad01ee00ec0 0x02e802b407b803b0 0xbbe007f01fe00fe2 0x6ef801fc07f803f8

def z1075 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0x43fffbffe0000000 0x90fffefff8000000

def z1076 : W := mkw 0x23fff76ec0004024 0x88fffddbb0001009 0xebffffffe000c0e1 0xfafffffff8003038

def z1077 : W := mkw 0x03eb776a40000000 0x00faddda90000000 0xe3ffffffe0000001 0xf8fffffff8000000

def z1078 : W := mkw 0x1bb43ad4bef30ecb 0x06ed0eb52fbcc3b2 0xffe43ff8ffe30fff 0xfff90ffe3ff8c3ff

def z1079 : W := mkw 0x23fff76ec1088000 0x08fffddbb0422000 0xebffffffe380c001 0xfafffffff8e03000

def z1080 : W := mkw 0x08a03ad006e00ec0 0x02280eb401b803b0 0xfae03ff013e00fe3 0x7eb80ffc04f803f8

def z1081 : W := mkw 0x08a002d002e002c0 0x022800b400b800b0 0x38e007f013e00fe2 0x4e3801fc04f803f8

def z1082 : W := mkw 0x040008913ffffbfe 0xc10002244ffffeff 0x1c0000001ffffffe 0x0700000007ffffff

def z1083 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0xfffb3fff139ccfff 0xfffecfffc4e733ff

def z1084 : W := mkw 0x20ffc76ec0000000 0x083ff1dbb0000000 0xa1ffdfffe0000001 0xe87ff7fff8000000

def z1085 : W := mkw 0x0ba03ad004a00ec0 0x02e80eb4012803b0 0xfbe03ff013800fe3 0x7ef80ffc04e003f8

def z1086 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0x62dfffffe0000001 0x98b7fffff8000000

def z1087 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0xf3c03ff01f800fe3 0x3cf00ffc07e003f8

def z1088 : W := mkw 0x23fff76eda522000 0x08fffddbb6948800 0xe3ffffffe0000001 0xf8fffffff8000000

def z1089 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0xffe03ff01fe3ffe3 0x7ff80ffc07f8fff8

def z1090 : W := mkw 0x180008913fffafdb 0x060002244fffebf6 0x1c0000001ffffffe 0x0700000007ffffff

def z1091 : W := mkw 0x0ba032d01ae006c0 0x02e80cb406b801b0 0xfbe027f01fe007e2 0x7ef809fc07f801f8

def z1092 : W := mkw 0x10003805a4050d1b 0x04000e0169014346 0xd71c380ffc1f0f1f 0xb5c70e03ff07c3c7

def z1093 : W := mkw 0x23fef366c0000000 0x08ffbcd9b0000000 0x42d83bf7e0000000 0x10b60efdf8000000

def z1094 : W := mkw 0x23b5776ec0000000 0x08ed5ddbb0000000 0xe3fc3fffe0000001 0xf8ff0ffff8000000

def z1095 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0x73e03ff01fe00fe1 0x1cf80ffc07f803f8

def z1096 : W := mkw 0x2315776ec0000000 0x08c55ddbb0000000 0x61043fffe0000001 0x18410ffff8000000

def z1097 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0xfefbe78f13fcffff 0xffbef9e3c4ff3fff

def z1098 : W := mkw 0x08a002d002e002c0 0x022800b400b800b0 0x7ae027f013e007e0 0x5eb809fc04f801f8

def z1099 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0xe7ffffffe000081f 0xf9fffffff8000207

def z1100 : W := mkw 0x00ea80000348a000 0x003aa00000d22800 0x9fffc0001ffff002 0xe7fff00007fffc00

def z1101 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0xf7fffffff01c0003 0xfdfffffffc070000

def z1102 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0x7ed8278f139ccfff 0x1fb609e3c4e733ff

def z1103 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0xfedb278f1fffffff 0xffb6c9e3c7ffffff

def z1104 : W := mkw 0x044b452b410cc134 0xc112d14ad043304d 0x041fc00fe01cc01c 0x8107f003f8073007

def z1105 : W := mkw 0x0ba03ad01ef20ec0 0x02e80eb407bc83b0 0xffe03ff01fff0fe3 0x7ff80ffc07ffc3f8

def z1106 : W := mkw 0x20ebc76a40000000 0x083af1da90000000 0xe3ffffffe0000001 0xf8fffffff8000000

def z1107 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x9fffd808fffff003 0xe7fff6023ffffc00

def z1108 : W := mkw 0x1bb43ad4bef30ecb 0x06ed0eb52fbcc3b2 0xfffc3ff0ffff0fe3 0xffff0ffc3fffc3f8

def z1109 : W := mkw 0x0014000580040110 0x0005000160010044 0xd61c200ff01c0f1f 0xb5870803fc0703c7

def z1110 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0xf2db278f139c0ffd 0xfcb6c9e3c4e703ff

def z1111 : W := mkw 0x23fff76ec348a000 0x08fffddbb0d22800 0xefffffffefe3f003 0xfbfffffffbf8fc00

def z1112 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0x2d27dc78ec63f0fc 0xcb49f71e3b18fc3f

def z1113 : W := mkw 0x23a1776ec0000000 0x08e85ddbb0000000 0x61203fffe0000001 0x18480ffff8000000

def z1114 : W := mkw 0x044a0183018cc3b4 0xc1128060c06330ed 0xdedb2387139ccffe 0xf7b6c8e1c4e733ff

def z1115 : W := mkw 0x08003ad004a00ec0 0x02000eb4012803b0 0xfbe03ff01fe00fe3 0x7ef80ffc07f803f8

def z1116 : W := mkw 0x0ba032d01ae006c0 0x02e80cb406b801b0 0xfae027f013e00fe3 0x7eb809fc04f803f8

def z1117 : W := mkw 0x044b45aa4188d2a4 0xc112d16a906234a9 0x28c3c7800380f0e0 0x4a30f1e000e03c38

def z1118 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0xdfdc380fff9f0f1f 0xf7f70e03ffe7c3c7

def z1119 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0xfbfffffff3800003 0xfefffffffce00000

def z1120 : W := mkw 0x044b45ab418cc3b4 0xc112d16ad06330ed 0xfedfe78ff39ccfff 0xffb7f9e3fce733ff

def z1121 : W := mkw 0x23b5f76ec0000000 0x08ed7ddbb0000000 0xe3e4ffffe0000001 0x78f93ffff8000000

def z1122 : W := mkw 0x10003805bc170d1b 0x04000e016f05c346 0xd618380ffc1f0f1f 0xb5860e03ff07c3c7

def z1123 : W := mkw 0x000048306421586e 0x8000120c1908561b 0x8d27d870ec63f8fe 0xe349f61c3b18fe3f

def z1124 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0xebffffffec600003 0xfafffffffb180000

def z1125 : W := mkw 0x2001776ec0000000 0x08005ddbb0000000 0x6007ffffe0000001 0x9801fffff8000000

def z1126 : W := mkw 0x27fff76ec108c024 0xc9fffddbb0423009 0xe3ffffffe000c001 0xf8fffffff8003000

def z1127 : W := mkw 0x23fff76ec108c024 0x88fffddbb0423009 0xfffffffff39cc8ff 0xfffffffffce7323f

def z1128 : W := mkw 0x1b143a55bc370d5b 0x06c50e956f0dc356 0xd71c387ffc1f0f1f 0xb5c70e1fff07c3c7

def z1129 : W := mkw 0x23b5f76eda522000 0x08ed7ddbb6948800 0x6124ffffec633001 0x18493ffffb18cc00

def z1130 : W := mkw 0x00014c386421586e 0x8000530e1908561b 0x0d27d878ec63f8fe 0x8349f61e3b18fe3f

def z1131 : W := mkw 0x2001776ec0000000 0x08005ddbb0000000 0xe0033fffe0000001 0xf800cffff8000000

def z1132 : W := mkw 0x0000008000800280 0x00000020002000a0 0xfbe03ff013800fe3 0x7ef80ffc04e003f8

def z1133 : W := mkw 0x0ba03ad01ee00ec0 0x02e80eb407b803b0 0x69e03ff00fe00fe1 0x5a780ffc03f803f8

def z1134 : W := mkw 0x13b43815be770d5b 0x04ed0e056f9dc356 0xfffc3c7fffff0fff 0xffff0f1fffffc3ff

def z1135 : W := mkw 0x0000089004a00ac0 0x00000224012802b0 0xfac03ff013800fe3 0x7eb00ffc04e003f8

def z1136 : W := mkw 0x0c017ffb64a55ffe 0xc3005ffed92957ff 0x60003fffe0000ffd 0x18000ffff80003ff

def z1137 : W := mkw 0x23fff76ec0122000 0x08fffddbb0048800 0xe3ffffffe0033001 0xf8fffffff800cc00

def z1138 : W := mkw 0x23fff76ed8120000 0x08fffddbb6048000 0xe3ffffffec030001 0xf8fffffffb00c000

def z1139 : W := mkw 0x0000000001088000 0x0000000000422000 0x9d27c0001ffff002 0xe749f00007fffc00

def z1140 : W := mkw 0x20a1776ec0000000 0x08285ddbb0000000 0x60e03fffe0000001 0x58380ffff8000000

def z1141 : W := mkw 0x035e80001b5aa000 0x00d7a00006d6a800 0x9f1fc0001ffff002 0xa7c7f00007fffc00

def z1142 : W := mkw 0x04014cb964a55bfe 0xc100532e592956ff 0x20001c78e0000ffd 0x0800071e380003ff

def z1143 : W := mkw 0x03b400001a520000 0x00ed000006948000 0x9fffc0001ffff002 0xe7fff00007fffc00

def z1144 : W := mkw 0x13143805a4050d1b 0x04c50e0169014346 0xd71c380ff01c0f1f 0xb5c70e03fc0703c7

def z1145 : W := mkw 0x00014d3a6421586e 0x8000534e9908561b 0xed27ffffec63f8ff 0xfb49fffffb18fe3f

def z1146 : W := mkw 0x080002d000a002c0 0x020000b4002800b0 0xfac027f013800fe3 0x7eb009fc04e003f8

def z1147 : W := mkw 0x20ebf76ec0000000 0x083afddbb0000000 0xe2fbffffe0000001 0xf8befffff8000000

def z1148 : W := mkw 0x1bb43a45be570d1b 0x06ed0e916f95c346 0xd71c380ffc1f0f1f 0xb5c70e03ff07c3c7

def z1149 : W := mkw 0x13143805be572d1b 0x04c50e016f95cb46 0xd71c380ffc7f3f1f 0xb5c70e03ff1fcfc7

def z1150 : W := mkw 0x23fff76ec0000000 0x08fffddbb0000000 0xebffffffe060f001 0xfafffffff8183c00

def z1151 : W := mkw 0x10143005a017051b 0x04050c016805c146 0x441c200fe01f071c 0x91070803f807c1c7

def z1152 : W := mkw 0x23fff76ec348a000 0x08fffddbb0d22800 0xe3ffffffe3800001 0xf8fffffff8e00000

def z1153 : W := mkw 0x0ba03ad03ee10eca 0x02e80eb40fb843b2 0xffe7fff8ffe3ffff 0xfff9fffe3ff8ffff

def z1154 : W := mkw 0x0bb43ad01ef20ec0 0x02ed0eb407bc83b0 0xfffffff01fffffe3 0xfffffffc07fffff8

def z1155 : W := mkw 0x13b4b805be572d1b 0x04ed2e016f95cb46 0xdf3ff80ffc7fff1f 0xf7cffe03ff1fffc7

def z1156 : W := mkw 0x1bfeb2c59bdea791 0x06ffacb166f7a9e4 0x52d82387139c0700 0x14b608e1c4e701c0

def z1157 : W := mkw 0x005e80001b5aa000 0x0017a00006d6a800 0x9edfc0001ffff002 0xe7b7f00007fffc00

def z1158 : W := mkw 0x13143005b817051b 0x04c50c016e05c146 0x5218200ff01c071c 0x14860803fc0701c7

def z1159 : W := mkw 0x13143815bc370d5b 0x04c50e056f0dc356 0xdf1c380ffc7f0fff 0xb7c70e03ff1fc3ff

def z1160 : W := mkw 0x00ea80001b5aa000 0x003aa00006d6a800 0x9efbc0001ffff002 0xe7bef00007fffc00

def z1161 : W := mkw 0x23fff76ec35aa000 0x08fffddbb0d6a800 0xefffffffe3fff001 0xfbfffffff8fffc00

def z1162 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0x561c200ffc1f0f1e 0x95870803ff07c3c7

def z1163 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0xd618380ff01c0f1f 0xb5860e03fc0703c7

def z1164 : W := mkw 0x23fff76edb5aa000 0x08fffddbb6d6a800 0xfffffffff39cc003 0xfffffffffce73000

def z1165 : W := mkw 0x1ba03ad4bee10ecb 0x06e80eb52fb843b2 0xfbe03ff0ffe00fe3 0x7ef80ffc3ff803f8

def z1166 : W := mkw 0x004b058b00840390 0x0012c162c02100e4 0xfedb278f139c0fff 0xffb6c9e3c4e703ff

def z1167 : W := mkw 0x03ea00001b488000 0x00fa800006d22000 0x9fffc0001ffff002 0xe7fff00007fffc00

def z1168 : W := mkw 0x0bb43ad01ef20ec0 0x02ed0eb407bc83b0 0xfbe43ff01fe30fe3 0x7ef90ffc07f8c3f8

def z1169 : W := mkw 0x1bb43ad49ef20ec1 0x06ed0eb527bc83b0 0xfbe03ff01fe00fe3 0x7ef80ffc07f803f8

def z1170 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0x5edb238f139ccffe 0x97b6c8e3c4e733ff

def z1171 : W := mkw 0x0bb43ad4bee10eca 0x02ed0eb52fb843b2 0xfffc3fffffe30fff 0xffff0ffffff8c3ff

def z1172 : W := mkw 0x08a00ad01ee00ec0 0x022802b407b803b0 0xfae027f01fe00fe3 0x7eb809fc07f803f8

def z1173 : W := mkw 0x1ba03ad03ef30ecb 0x06e80eb40fbcc3b2 0xfbe03ff01fe30fe3 0x7ef80ffc07f8c3f8

def z1174 : W := mkw 0x03a008901ee00ac0 0x00e8022407b802b0 0xfbe03ff01fe00fe3 0x7ef80ffc07f803f8

def z1175 : W := mkw 0x080008901ee00ec0 0x0200022407b803b0 0xfbe03ff01fe00fe3 0x7ef80ffc07f803f8

def z1176 : W := mkw 0x23fff76eda400000 0x08fffddbb6900000 0xffffffffffe3f003 0xfffffffffff8fc00

def z1177 : W := mkw 0x23fff76edb5aa000 0x08fffddbb6d6a800 0xf3ffffffffff3001 0xfcffffffffffcc00

def z1178 : W := mkw 0x10143805a4170d1b 0x04050e016905c346 0x4018380fe01c0f1d 0x10060e03f80703c7

def z1179 : W := mkw 0x2315776ec0000000 0x08c55ddbb0000000 0x62183fffe0000001 0x18860ffff8000000

def z1180 : W := mkw 0x0ba03ad03ee10eca 0x02e80eb40fb843b2 0xfbe43ff0ffe30fe3 0x7ef90ffc3ff8c3f8

def z1181 : W := mkw 0x23fff76edb5aa000 0x08fffddbb6d6a800 0xfbfffffff3fcf001 0xfefffffffcff3c00

def z1182 : W := mkw 0x03fe800001088000 0x00ffa00000422000 0x9fffc0001ffff002 0xe7fff00007fffc00

def z1183 : W := mkw 0x100008013c170d1b 0x040002004f05c346 0xd71c380ffc1f0f1f 0xb5c70e03ff07c3c7

def z1184 : W := mkw 0x10143805bc170d1b 0x04050e016f05c346 0x541c380ffc1f0f1f 0x95070e03ff07c3c7

def z1185 : W := mkw 0x03a03ad004a00ac0 0x00e80eb4012802b0 0xfbe03ff01fe00fe3 0x7ef80ffc07f803f8

def z1186 : W := mkw 0x1bb43a55be770d5b 0x06ed0e956f9dc356 0xff3c3c7ffc7f0fff 0xffcf0f1fff1fc3ff

def z1187 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x1de7c0001ffff002 0x4779f00007fffc00

def z1188 : W := mkw 0x245fc52fe10dd13e 0xc917f14bf843744f 0x041fc00fe01ff01c 0x8107f003f807fc07

def z1189 : W := mkw 0x2315776ec0000000 0x08c55ddbb0000000 0xe33fffffe0000001 0xf8cffffff8000000

def z1190 : W := mkw 0x13143805bc170d1b 0x04c50e016f05c346 0x571c380ffc1f071c 0x95c70e03ff07c1c7

def z1191 : W := mkw 0x23fff76eda520000 0x08fffddbb6948000 0xffffffffffff0003 0xffffffffffffc000

def z1192 : W := mkw 0x13b4b805bc170d1b 0x04ed2e016f05c346 0xd73cf80ffc1f0f1f 0xb5cf3e03ff07c3c7

def z1193 : W := mkw 0x08a002d01ae006c0 0x022800b406b801b0 0x38e007f013e007e0 0x4e3801fc04f801f8

def z1194 : W := mkw 0x10140805a417091b 0x040502016905c246 0xd71c380ffc1f0f1f 0xb5c70e03ff07c3c7

def z1195 : W := mkw 0x0bb43ad03ef30eca 0x02ed0eb40fbcc3b2 0xfffc3ff8ffff0fff 0xffff0ffe3fffc3ff

def z1196 : W := mkw 0x03fe80001b5aa000 0x00ffa00006d6a800 0x17ffc0001ffff000 0x85fff00007fffc00

def z1197 : W := mkw 0x044b058b018cc3b4 0xc112c162c06330ed 0xf6d8278f139c0fff 0xbdb609e3c4e703ff

def z1198 : W := mkw 0x2001776ec0004024 0x88005ddbb0001009 0xec033fffe000c8ff 0xfb00cffff800323f

def z1199 : W := mkw 0x23b5f76ec0000000 0x08ed7ddbb0000000 0xe33cffffe0000001 0xb8cf3ffff8000000

def z1200 : W := mkw 0x23fff76ec11aa000 0x08fffddbb046a800 0xfffffffff39ff003 0xfffffffffce7fc00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z7,z8,z6]),(0,[z1,z2,z3,z4,z9,z8,z6]),(0,[z1,z10,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z11,z8,z6]),(0,[z12,z1,z2,z3,z4,z8,z13])],[(0,[z14,z1,z2,z3,z4,z8,z6]),(0,[z15,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z16,z4,z8,z6]),(1,[z1,z2,z3,z8,z17,z6])],[(0,[z1,z2,z3,z4,z8,z18,z6]),(0,[z19,z1,z2,z20,z4,z8,z6]),(0,[z1,z2,z21,z3,z4,z8,z6]),(0,[z1,z22,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z23,z24,z6]),(0,[z1,z2,z3,z4,z25,z8,z6])],[(0,[z26,z1,z2,z3,z4,z8,z6]),(0,[z27,z1,z2,z3,z4,z8,z6]),(0,[z28,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z29]),(0,[z1,z2,z3,z4,z8,z13,z30]),(0,[z1,z2,z3,z31,z4,z8,z6]),(0,[z1,z32,z2,z3,z4,z8,z6]),(0,[z33,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z34,z3,z4,z8,z6])],[(0,[z1,z2,z3,z35,z4,z8,z6]),(0,[z1,z2,z3,z4,z36,z8,z6]),(0,[z37,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z38,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z39]),(0,[z40,z1,z2,z3,z4,z8,z6])],[(0,[z41,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z42,z3,z4,z8,z6]),(0,[z1,z2,z43,z3,z4,z8,z39]),(0,[z1,z2,z44,z3,z4,z8,z6]),(0,[z1,z2,z3,z45,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z6,z46]),(0,[z1,z2,z3,z4,z8,z6,z47]),(0,[z48,z1,z2,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z49,z20,z8,z6]),(1,[z15,z2,z3,z50,z8,z6]),(0,[z12,z1,z51,z3,z4,z8,z6]),(0,[z52,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z53,z8,z6])],[(0,[z15,z1,z2,z3,z4,z8,z13]),(0,[z1,z54,z2,z3,z4,z8,z6]),(0,[z55,z1,z2,z3,z4,z8,z39]),(0,[z1,z2,z3,z56,z4,z8,z6]),(1,[z1,z57,z2,z3,z58,z6])],[(0,[z1,z59,z2,z3,z4,z8,z13])],[(0,[z60,z1,z2,z3,z4,z8,z6]),(0,[z61,z1,z2,z62,z4,z8,z6]),(0,[z1,z2,z3,z63,z4,z8,z6]),(0,[z1,z64,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z65,z6])],[(0,[z1,z2,z3,z4,z66,z8,z6]),(0,[z1,z67,z2,z3,z68,z8,z6])],[(0,[z1,z2,z3,z4,z69,z8,z6]),(0,[z1,z2,z3,z4,z8,z70,z6]),(0,[z1,z2,z71,z3,z4,z8,z6]),(0,[z1,z2,z72,z3,z4,z8,z39]),(0,[z55,z1,z67,z2,z3,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z73])],[(1,[z1,z2,z3,z49,z8,z6]),(0,[z74,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z8,z6]),(0,[z1,z2,z3,z4,z8,z75,z6]),(0,[z1,z76,z2,z3,z4,z8,z77]),(0,[z1,z78,z2,z3,z79,z8,z6]),(0,[z80,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z81,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z82]),(0,[z1,z2,z72,z56,z4,z8,z6]),(0,[z1,z2,z3,z24,z8,z58,z6]),(1,[z1,z2,z3,z4,z8,z83]),(0,[z84,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z85])]],
   [[(0,[z1,z2,z86,z3,z4,z8,z6]),(0,[z61,z1,z2,z3,z4,z8,z87]),(0,[z1,z2,z3,z88,z4,z8,z6]),(0,[z89,z1,z2,z3,z4,z23,z6]),(1,[z1,z2,z3,z90,z8,z6])],[(1,[z1,z2,z3,z91,z8,z6]),(0,[z92,z1,z2,z3,z4,z8,z6]),(0,[z61,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z56,z4,z8,z13]),(0,[z1,z2,z3,z4,z93,z8,z6]),(0,[z1,z94,z2,z3,z4,z8,z6]),(0,[z95,z1,z2,z3,z4,z8,z6])],[(0,[z2,z96,z3,z20,z4,z8,z6]),(0,[z1,z97,z2,z3,z98,z8,z6]),(0,[z99,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z56,z4,z100,z6]),(0,[z1,z2,z3,z4,z8,z6,z101])],[(0,[z102,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z103,z6]),(0,[z1,z2,z3,z104,z4,z24,z6]),(0,[z1,z105,z2,z3,z4,z8,z106])],[(0,[z1,z2,z107,z4,z108,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z109])],[(1,[z1,z2,z3,z110,z8,z6]),(0,[z1,z2,z3,z4,z69,z8,z13]),(0,[z1,z78,z3,z111,z4,z8,z6])],[(0,[z112,z1,z43,z3,z4,z8,z6]),(1,[z1,z2,z3,z113,z8,z6]),(0,[z1,z2,z3,z114,z4,z8,z6]),(0,[z1,z76,z2,z3,z4,z8,z115]),(0,[z116,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z106,z39])],[(0,[z0,z1,z2,z3,z4,z8,z117]),(0,[z1,z2,z3,z4,z8,z13,z118]),(0,[z1,z2,z3,z4,z8,z119,z6]),(0,[z1,z2,z3,z4,z8,z6,z120]),(0,[z1,z105,z2,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z121,z6]),(0,[z1,z2,z122,z96,z4,z8,z6]),(0,[z1,z123,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z124,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z125]),(0,[z1,z126,z2,z3,z4,z8,z70]),(0,[z1,z2,z3,z4,z8,z127,z6])],[(0,[z1,z2,z3,z111,z128,z8,z6]),(0,[z1,z2,z3,z4,z8,z129,z39]),(0,[z1,z130,z2,z3,z4,z8,z6])],[(0,[z1,z131,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z132,z4,z8,z39]),(0,[z1,z2,z3,z133,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z134])],[(0,[z1,z2,z3,z4,z135,z8,z6]),(0,[z14,z1,z2,z20,z4,z8,z6]),(1,[z1,z2,z3,z136,z8,z6]),(0,[z1,z2,z3,z4,z8,z137,z13])],[(0,[z1,z2,z3,z50,z8,z58,z6]),(0,[z89,z1,z2,z3,z4,z8,z39]),(0,[z1,z57,z2,z3,z104,z8,z6]),(0,[z138,z1,z2,z3,z4,z8,z6])],[(0,[z1,z139,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z140,z6]),(0,[z141,z1,z2,z3,z4,z8,z6]),(0,[z1,z67,z2,z3,z4,z8,z39]),(0,[z1,z142,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z143,z4,z8,z6]),(0,[z1,z144,z2,z3,z4,z8,z6])],[(0,[z0,z1,z145,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z146,z8,z6]),(0,[z12,z1,z3,z4,z8,z147,z6]),(0,[z148,z1,z2,z3,z4,z8,z39]),(0,[z1,z2,z72,z3,z4,z8,z13]),(0,[z89,z1,z2,z56,z4,z8,z6]),(0,[z1,z59,z2,z3,z4,z8,z149]),(0,[z1,z2,z150,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z151,z6])],[(0,[z1,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z152,z8,z6]),(0,[z1,z2,z3,z4,z153,z8,z6]),(0,[z1,z105,z2,z3,z4,z8,z13])]],
   [[(0,[z1,z2,z3,z154,z4,z8,z6]),(0,[z1,z2,z155,z3,z4,z8,z6]),(0,[z1,z2,z156,z3,z4,z8,z6]),(0,[z1,z97,z2,z3,z4,z8,z157]),(0,[z1,z51,z3,z4,z8,z6,z39]),(0,[z1,z2,z3,z4,z158,z8,z39]),(0,[z1,z2,z3,z4,z159,z8,z6])],[(0,[z1,z2,z3,z20,z4,z8,z39]),(1,[z1,z2,z3,z4,z8,z70]),(0,[z1,z2,z3,z4,z8,z160,z6]),(0,[z1,z3,z4,z79,z8,z6,z39]),(0,[z1,z2,z161,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z162,z8,z6]),(1,[z163,z1,z2,z3,z4,z6]),(0,[z1,z164,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z128,z79,z8,z6]),(1,[z1,z2,z3,z4,z8,z77]),(0,[z1,z2,z165,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z108,z8,z6]),(0,[z1,z59,z2,z4,z8,z6,z30])],[(0,[z1,z2,z3,z4,z8,z6,z166])],[(1,[z1,z167,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z13,z87]),(1,[z1,z2,z3,z4,z8,z168]),(0,[z1,z2,z3,z68,z4,z8,z39]),(0,[z55,z1,z2,z4,z108,z8,z6]),(0,[z1,z59,z2,z3,z4,z8,z30]),(0,[z1,z105,z2,z3,z4,z6,z169])],[(0,[z170,z15,z2,z3,z4,z8,z6]),(0,[z41,z171,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z24,z69,z6]),(0,[z1,z172,z2,z3,z4,z8,z6]),(0,[z173,z1,z2,z3,z4,z8,z6]),(0,[z174,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z13,z6]),(1,[z1,z2,z4,z8,z175,z6]),(0,[z1,z2,z3,z4,z8,z6,z176]),(0,[z1,z2,z3,z4,z158,z8,z106])],[(0,[z1,z177,z3,z20,z4,z8,z6]),(1,[z1,z2,z3,z4,z178,z6]),(0,[z1,z2,z179,z3,z4,z8,z6]),(0,[z1,z180,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z181,z6])],[(0,[z1,z182,z2,z3,z4,z8,z6]),(0,[z183,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z184,z6]),(0,[z1,z2,z3,z4,z128,z8,z39]),(0,[z1,z2,z3,z185,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z186,z6]),(0,[z1,z2,z187,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z39,z30]),(0,[z1,z188,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z189,z8,z6]),(0,[z1,z57,z2,z3,z4,z24,z6])]],
   [[(0,[z190,z1,z3,z4,z8,z191,z6]),(0,[z1,z76,z2,z3,z111,z8,z6]),(0,[z1,z192,z2,z3,z4,z8,z6]),(0,[z1,z193,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z194,z8,z6]),(0,[z89,z1,z105,z2,z3,z4,z6]),(1,[z1,z2,z3,z195,z8,z6]),(0,[z1,z2,z3,z4,z8,z196,z6])],[(0,[z1,z2,z197,z3,z4,z8,z6]),(0,[z198,z1,z2,z3,z4,z8,z6]),(0,[z89,z1,z2,z3,z4,z58,z6])],[(0,[z199,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z200,z3,z4,z8,z6]),(0,[z1,z201,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z115]),(0,[z1,z202,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z203,z6])],[(1,[z0,z1,z3,z4,z8,z39]),(0,[z112,z1,z2,z3,z4,z8,z39]),(0,[z14,z1,z2,z3,z4,z8,z204]),(0,[z1,z2,z205,z3,z4,z8,z6]),(0,[z1,z76,z2,z3,z4,z206,z6]),(0,[z207,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z208,z6])],[(0,[z1,z2,z209,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z210]),(0,[z1,z211,z97,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z212,z8,z39]),(0,[z1,z213,z2,z3,z4,z8,z6]),(0,[z214,z1,z2,z3,z4,z8,z6])],[(0,[z215,z1,z2,z3,z4,z8,z6]),(0,[z1,z216,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z217]),(0,[z174,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z218,z6]),(0,[z1,z2,z3,z4,z158,z58,z6])],[(0,[z219,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z50,z4,z8,z39]),(0,[z1,z220,z2,z3,z4,z8,z6]),(0,[z1,z2,z221,z3,z4,z8,z6])],[(0,[z0,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z222,z58,z6]),(0,[z61,z1,z2,z3,z4,z8,z191]),(0,[z1,z2,z223,z3,z4,z8,z6]),(0,[z224,z1,z2,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z225,z8,z6]),(0,[z19,z1,z2,z96,z4,z8,z6]),(0,[z1,z2,z107,z3,z4,z23,z6])],[(0,[z226,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z227,z8,z6]),(0,[z1,z228,z2,z3,z4,z8,z6]),(0,[z55,z1,z2,z72,z4,z8,z6])],[(1,[z1,z2,z3,z4,z229,z6]),(0,[z1,z2,z96,z3,z4,z8,z39]),(0,[z190,z1,z2,z3,z4,z8,z6]),(0,[z1,z230,z2,z3,z4,z8,z6]),(0,[z1,z216,z2,z3,z231,z8,z6]),(0,[z1,z2,z3,z4,z231,z8,z6]),(0,[z1,z97,z2,z3,z4,z8,z103]),(0,[z1,z232,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z24,z8,z6]),(0,[z233,z1,z2,z4,z8,z58,z6])],[(0,[z234,z1,z2,z3,z4,z8,z6]),(0,[z235,z1,z2,z122,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z236,z6]),(0,[z89,z1,z2,z3,z4,z147,z6])],[(0,[z0,z112,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z237,z8,z6]),(0,[z41,z1,z2,z3,z4,z69,z6]),(0,[z238,z1,z2,z3,z4,z8,z6])],[(0,[z171,z1,z2,z107,z3,z4,z6])],[(0,[z1,z2,z239,z3,z4,z8,z6]),(0,[z1,z2,z3,z240,z4,z8,z6]),(0,[z1,z22,z105,z3,z4,z8,z6])],[(0,[z0,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z241,z6]),(0,[z1,z2,z3,z242,z4,z8,z6]),(0,[z1,z243,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z68,z8,z244])]],
   [[(0,[z1,z2,z3,z4,z8,z245,z6]),(0,[z1,z2,z3,z4,z246,z8,z6]),(0,[z1,z78,z2,z3,z4,z8,z6]),(0,[z247,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z13,z127])],[(0,[z1,z2,z3,z4,z8,z6,z117]),(0,[z1,z248,z2,z3,z4,z8,z6]),(0,[z1,z2,z249,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z250,z6]),(1,[z1,z2,z3,z104,z24,z6])],[(0,[z1,z251,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z39,z118]),(0,[z1,z2,z3,z4,z24,z8,z13])],[(0,[z1,z2,z252,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z253,z8,z6]),(0,[z1,z2,z3,z4,z8,z39,z254]),(0,[z89,z1,z2,z3,z4,z255,z6]),(0,[z256,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z257,z3,z4,z8,z6]),(0,[z170,z2,z3,z4,z128,z8,z6]),(0,[z1,z2,z107,z3,z4,z8,z39]),(0,[z258,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z259,z4,z8,z6]),(0,[z1,z2,z260,z3,z4,z8,z6])],[(0,[z1,z261,z2,z3,z4,z8,z6]),(0,[z1,z216,z2,z3,z4,z262,z6]),(0,[z1,z2,z3,z4,z8,z263,z6]),(0,[z1,z2,z3,z4,z8,z264,z6]),(0,[z1,z2,z3,z108,z8,z17,z6])],[(1,[z1,z2,z3,z265,z8,z6]),(0,[z1,z2,z3,z4,z8,z266,z6]),(1,[z1,z2,z3,z267,z4,z6]),(0,[z1,z268,z2,z3,z4,z8,z6]),(0,[z269,z1,z2,z3,z4,z8,z6]),(0,[z1,z270,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z271,z4,z8,z6]),(0,[z1,z2,z272,z3,z4,z8,z6]),(1,[z1,z273,z2,z3,z8,z6]),(0,[z1,z67,z2,z3,z4,z274,z6])],[(0,[z1,z167,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z206,z6]),(0,[z1,z51,z2,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z275,z6]),(0,[z1,z2,z3,z4,z24,z6,z169]),(1,[z1,z276,z3,z4,z8,z6])]],
   [[(1,[z112,z1,z3,z4,z8,z39]),(0,[z1,z216,z2,z132,z4,z8,z6]),(0,[z277,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z278,z8,z6])],[(0,[z1,z2,z3,z279,z4,z8,z6]),(0,[z1,z2,z3,z280,z4,z8,z6]),(0,[z1,z2,z122,z3,z4,z8,z39])],[(0,[z2,z3,z4,z69,z8,z222,z6]),(0,[z1,z2,z281,z3,z4,z8,z6]),(0,[z1,z282,z2,z3,z4,z8,z6]),(0,[z283,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z13,z191]),(0,[z1,z76,z2,z3,z4,z8,z39]),(0,[z1,z2,z284,z3,z4,z8,z6]),(0,[z1,z2,z72,z3,z56,z8,z6]),(0,[z1,z2,z3,z285,z4,z8,z6]),(0,[z1,z2,z3,z4,z58,z6,z169])],[(0,[z1,z2,z3,z4,z286,z8,z6]),(0,[z61,z1,z2,z287,z4,z8,z6]),(0,[z1,z2,z3,z288,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z254]),(0,[z1,z2,z3,z259,z4,z8,z13])],[(0,[z1,z2,z3,z4,z8,z289,z6]),(0,[z1,z2,z3,z4,z23,z8,z39]),(0,[z1,z2,z3,z4,z8,z149,z39]),(0,[z1,z59,z2,z3,z4,z8,z6]),(1,[z1,z290,z3,z4,z8,z6]),(0,[z1,z2,z3,z291,z4,z8,z6])],[(0,[z1,z2,z3,z4,z79,z8,z6]),(0,[z1,z292,z2,z3,z4,z8,z6])],[(0,[z19,z2,z96,z3,z4,z8,z6]),(0,[z15,z1,z2,z3,z128,z8,z6]),(0,[z1,z2,z3,z4,z8,z39,z87]),(0,[z1,z78,z3,z4,z8,z6,z39]),(0,[z1,z2,z293,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z294])]],
   [[(0,[z1,z2,z3,z91,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z295]),(0,[z296,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z297]),(0,[z1,z298,z2,z3,z4,z8,z6]),(0,[z1,z299,z2,z3,z4,z8,z6]),(0,[z1,z300,z2,z3,z4,z8,z6])],[(0,[z14,z1,z2,z96,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z301]),(0,[z1,z2,z3,z4,z23,z222,z6]),(0,[z235,z1,z2,z3,z4,z8,z39]),(0,[z1,z302,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z303,z8,z6]),(0,[z1,z2,z107,z3,z4,z58,z6]),(0,[z1,z304,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z305,z6]),(0,[z1,z2,z3,z4,z8,z306,z39])],[(0,[z1,z2,z3,z307,z4,z8,z6]),(0,[z308,z1,z2,z3,z4,z8,z6]),(0,[z1,z309,z2,z3,z4,z8,z58])],[(0,[z1,z2,z3,z310,z4,z8,z6]),(0,[z1,z311,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z8,z6,z312]),(0,[z1,z2,z313,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z314,z6]),(0,[z1,z315,z2,z3,z4,z8,z6]),(0,[z1,z2,z107,z3,z4,z8,z13]),(1,[z1,z59,z2,z4,z8,z30]),(1,[z1,z67,z2,z3,z8,z118])],[(0,[z1,z2,z316,z3,z4,z8,z6]),(0,[z1,z126,z2,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z178,z6]),(0,[z1,z2,z3,z4,z79,z8,z13]),(0,[z89,z1,z2,z107,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z317,z6])],[(0,[z1,z2,z276,z3,z4,z8,z6])]],
   [[(0,[z0,z1,z126,z3,z4,z8,z6]),(0,[z1,z2,z3,z79,z8,z58,z6])],[(0,[z1,z2,z3,z4,z8,z318,z6]),(0,[z1,z2,z3,z4,z8,z6,z6]),(0,[z1,z2,z3,z319,z4,z8,z6]),(0,[z320,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z321]),(0,[z1,z2,z3,z4,z303,z8,z13]),(0,[z1,z2,z4,z8,z175,z58,z6])],[(0,[z19,z14,z2,z3,z4,z8,z6]),(0,[z1,z2,z43,z3,z4,z8,z6]),(0,[z1,z322,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z23,z58,z6]),(0,[z1,z2,z3,z4,z8,z255,z39]),(0,[z323,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z324,z8,z6])],[(0,[z0,z1,z2,z325,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z326,z6]),(0,[z112,z327,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z3,z4,z8,z6]),(0,[z1,z2,z3,z328,z4,z8,z6]),(0,[z1,z2,z107,z3,z4,z147,z6]),(0,[z1,z2,z3,z4,z8,z329,z6]),(0,[z1,z2,z3,z4,z8,z330,z6]),(0,[z1,z331,z2,z3,z4,z8,z6])],[(1,[z1,z177,z3,z4,z8,z6]),(0,[z1,z332,z2,z3,z4,z8,z6]),(0,[z1,z211,z2,z3,z4,z23,z6]),(0,[z1,z2,z3,z333,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z334,z6])],[(0,[z1,z2,z20,z132,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z335,z6]),(0,[z1,z2,z3,z104,z4,z8,z39])],[(0,[z1,z2,z145,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z336,z6]),(0,[z1,z2,z3,z4,z8,z337,z6]),(0,[z1,z2,z3,z4,z8,z338,z6]),(0,[z1,z2,z3,z4,z8,z137,z6]),(0,[z1,z2,z3,z4,z8,z39,z339])],[(0,[z1,z340,z2,z3,z4,z8,z6]),(0,[z1,z2,z341,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z39]),(0,[z1,z342,z2,z3,z4,z8,z6]),(0,[z1,z57,z2,z3,z8,z58,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z6,z343])],[(0,[z19,z1,z2,z3,z4,z8,z39]),(0,[z170,z1,z2,z3,z4,z8,z39]),(0,[z1,z344,z2,z3,z4,z8,z6]),(0,[z1,z345,z2,z3,z4,z8,z39]),(0,[z1,z2,z72,z3,z4,z8,z6]),(0,[z1,z346,z2,z3,z4,z8,z6])],[(0,[z0,z1,z327,z3,z4,z8,z6]),(0,[z1,z347,z3,z20,z4,z8,z6]),(0,[z1,z2,z348,z3,z4,z8,z6]),(0,[z1,z2,z43,z3,z4,z8,z13]),(0,[z1,z76,z2,z3,z4,z38,z6]),(1,[z1,z2,z3,z349,z8,z6]),(0,[z1,z2,z3,z4,z8,z13,z350]),(0,[z1,z67,z2,z3,z4,z8,z244]),(0,[z1,z2,z3,z351,z4,z8,z6])],[(0,[z1,z2,z352,z3,z4,z8,z6]),(0,[z1,z2,z96,z4,z8,z6,z30]),(0,[z1,z353,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z354,z8,z6]),(0,[z1,z211,z2,z3,z4,z8,z82]),(0,[z1,z2,z3,z4,z8,z326,z13]),(0,[z355,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z356,z6]),(0,[z1,z2,z107,z3,z4,z255,z6])],[(0,[z171,z1,z2,z3,z4,z8,z39]),(0,[z1,z2,z3,z357,z4,z8,z6]),(0,[z1,z358,z2,z3,z4,z6,z30])],[(0,[z1,z167,z2,z3,z20,z4,z8]),(0,[z1,z2,z3,z4,z8,z359,z6]),(0,[z1,z2,z3,z4,z8,z191,z39]),(0,[z360,z1,z2,z3,z4,z8,z6]),(0,[z1,z3,z111,z4,z79,z8,z6]),(0,[z55,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z361,z3,z4,z8,z6])],[(1,[z170,z2,z3,z128,z8,z6]),(0,[z362,z1,z2,z3,z4,z8,z6]),(0,[z1,z363,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z6,z339]),(0,[z1,z2,z3,z364,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z365]),(0,[z1,z2,z3,z4,z8,z366,z6]),(0,[z1,z2,z3,z4,z367,z8,z6]),(0,[z1,z2,z368,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z244,z39]),(0,[z1,z67,z2,z72,z3,z8,z6])]],
   [[(0,[z1,z369,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z370]),(0,[z171,z1,z2,z3,z4,z222,z6]),(1,[z1,z76,z3,z79,z8,z6]),(0,[z1,z211,z2,z3,z4,z8,z39]),(0,[z1,z371,z2,z3,z4,z8,z6])],[(0,[z1,z2,z372,z3,z4,z8,z6]),(0,[z1,z2,z3,z373,z4,z8,z6]),(0,[z1,z2,z3,z68,z4,z8,z244])],[(0,[z1,z2,z20,z4,z8,z6,z30]),(0,[z235,z2,z3,z4,z8,z191,z6]),(0,[z1,z374,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z104,z4,z58,z6]),(0,[z1,z2,z3,z68,z4,z8,z118])],[(0,[z1,z2,z3,z4,z8,z321,z6]),(0,[z1,z2,z375,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z376])],[(0,[z1,z2,z177,z3,z4,z8,z6]),(0,[z377,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z378]),(0,[z1,z2,z3,z4,z379,z8,z6]),(0,[z1,z380,z2,z3,z4,z8,z6])],[(0,[z327,z2,z145,z3,z4,z8,z6]),(0,[z381,z1,z2,z3,z4,z8,z6]),(0,[z1,z382,z2,z3,z4,z8,z6]),(0,[z1,z216,z2,z43,z4,z8,z6]),(0,[z1,z76,z3,z4,z79,z8,z6]),(0,[z1,z2,z3,z4,z8,z129,z6]),(1,[z55,z1,z2,z212,z8,z6]),(0,[z1,z2,z3,z4,z8,z83,z6])],[(0,[z0,z1,z2,z3,z4,z8,z245]),(0,[z112,z1,z145,z3,z4,z8,z6]),(1,[z1,z3,z4,z8,z383,z6]),(0,[z1,z2,z3,z4,z8,z384,z6])],[(0,[z1,z385,z2,z3,z4,z8,z6]),(1,[z1,z51,z3,z4,z8,z39]),(0,[z1,z2,z2,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z6,z386]),(0,[z1,z2,z3,z4,z387,z8,z6])]],
   [[(0,[z170,z1,z2,z3,z4,z388,z6]),(0,[z1,z2,z3,z4,z8,z6,z389]),(0,[z390,z1,z2,z3,z4,z8,z6]),(0,[z391,z1,z2,z3,z4,z8,z6]),(0,[z89,z1,z2,z3,z4,z8,z6]),(0,[z1,z392,z2,z3,z4,z8,z6]),(0,[z393,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z6,z394]),(0,[z1,z395,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z217,z6]),(0,[z1,z57,z2,z3,z4,z8,z39]),(1,[z12,z1,z3,z4,z8,z13]),(1,[z1,z2,z72,z56,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z396]),(1,[z1,z309,z2,z3,z4,z8]),(0,[z1,z67,z2,z3,z4,z8,z6])],[(0,[z148,z1,z2,z3,z4,z8,z6]),(1,[z14,z2,z20,z4,z8,z6]),(0,[z12,z1,z3,z4,z8,z13,z6]),(0,[z1,z2,z56,z4,z212,z8,z6]),(0,[z1,z2,z107,z3,z4,z108,z6]),(0,[z397,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z398,z6])],[(0,[z0,z1,z2,z352,z4,z8,z6]),(0,[z1,z399,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z400,z6]),(0,[z1,z2,z3,z4,z401,z8,z6]),(0,[z1,z105,z2,z3,z4,z158,z6])],[(0,[z1,z402,z2,z3,z4,z8,z6]),(0,[z1,z327,z2,z3,z4,z8,z39]),(0,[z1,z2,z43,z20,z4,z8,z6]),(1,[z41,z2,z3,z4,z222,z6]),(0,[z61,z1,z2,z122,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z403,z39]),(0,[z1,z2,z3,z4,z404,z8,z6]),(0,[z1,z2,z3,z4,z158,z8,z6])],[(0,[z1,z216,z2,z3,z4,z178,z6]),(0,[z1,z78,z2,z3,z4,z8,z405])],[(0,[z406,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z407,z6]),(0,[z1,z2,z3,z132,z4,z8,z13]),(1,[z1,z2,z3,z4,z38,z6]),(0,[z1,z408,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z409,z8,z6]),(0,[z1,z2,z3,z4,z8,z410,z13]),(1,[z1,z2,z3,z411,z8,z6])],[(0,[z1,z3,z4,z8,z147,z6,z39]),(0,[z1,z2,z3,z4,z8,z39,z412]),(0,[z1,z2,z3,z4,z8,z6,z413])]],
   [[(0,[z1,z2,z3,z4,z4,z8,z6]),(0,[z41,z1,z2,z3,z110,z8,z6]),(0,[z1,z2,z3,z4,z414,z8,z6]),(0,[z89,z1,z2,z3,z4,z8,z13]),(0,[z1,z415,z2,z3,z4,z8,z6]),(0,[z1,z416,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z68,z4,z8,z6]),(0,[z1,z2,z417,z3,z4,z8,z6])],[(0,[z41,z1,z2,z3,z113,z8,z6]),(0,[z418,z1,z2,z3,z4,z8,z6]),(0,[z1,z67,z2,z3,z4,z8,z13])],[(0,[z1,z2,z3,z136,z4,z8,z6]),(0,[z1,z2,z72,z3,z79,z8,z6]),(0,[z1,z2,z419,z3,z4,z8,z39])],[(0,[z1,z2,z3,z4,z128,z8,z6]),(0,[z1,z2,z420,z3,z4,z8,z6]),(0,[z1,z421,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z422,z6]),(0,[z1,z2,z3,z4,z8,z6,z30]),(1,[z1,z2,z3,z4,z6,z423]),(0,[z1,z2,z3,z4,z424,z8,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z216,z2,z3,z4,z8,z217]),(0,[z12,z1,z78,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z425,z6]),(0,[z1,z2,z3,z4,z158,z8,z13])],[(0,[z1,z2,z426,z3,z4,z8,z6]),(0,[z1,z2,z3,z20,z4,z8,z13]),(0,[z55,z15,z1,z2,z3,z8,z6]),(1,[z1,z78,z3,z111,z8,z6]),(0,[z1,z2,z3,z111,z8,z58,z6])],[(0,[z1,z2,z427,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z383,z6])],[(0,[z112,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z325,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z428,z6]),(0,[z1,z3,z4,z8,z191,z383,z6]),(0,[z1,z429,z2,z3,z4,z8,z6]),(0,[z1,z211,z2,z3,z4,z147,z6]),(0,[z1,z2,z3,z8,z6,z312,z30]),(0,[z1,z2,z3,z4,z106,z6,z169])]],
   [[(0,[z1,z2,z3,z68,z4,z8,z13]),(1,[z1,z2,z3,z4,z274,z6])],[(0,[z1,z430,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z431,z8,z6]),(0,[z1,z2,z3,z4,z8,z432,z6])],[(0,[z1,z2,z3,z4,z8,z433,z6]),(0,[z1,z2,z3,z50,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z222,z39]),(0,[z1,z2,z3,z4,z8,z115,z6])],[(0,[z1,z2,z3,z4,z8,z6,z204]),(0,[z1,z2,z3,z4,z128,z8,z13]),(0,[z1,z434,z2,z3,z4,z8,z6]),(0,[z235,z1,z59,z2,z3,z4,z8])],[(0,[z1,z435,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z436]),(0,[z1,z2,z3,z4,z8,z425,z13]),(0,[z1,z2,z3,z4,z8,z437,z6])],[(0,[z1,z2,z3,z438,z4,z8,z6]),(0,[z1,z2,z3,z4,z439,z8,z6]),(1,[z1,z3,z4,z8,z147,z39]),(0,[z1,z2,z72,z3,z104,z8,z6])],[(0,[z1,z2,z96,z3,z4,z8,z6]),(0,[z1,z440,z2,z3,z4,z8,z6]),(0,[z441,z1,z2,z3,z4,z8,z39]),(0,[z1,z2,z442,z3,z4,z8,z6])],[(0,[z112,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z6,z443]),(0,[z1,z2,z4,z108,z8,z255,z6]),(0,[z444,z1,z2,z3,z4,z8,z6]),(0,[z1,z67,z2,z3,z8,z6,z118]),(0,[z1,z2,z3,z4,z445,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z388,z8,z6]),(0,[z1,z97,z2,z3,z4,z23,z6]),(0,[z1,z2,z446,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z447,z8,z39]),(0,[z1,z2,z3,z4,z212,z8,z13]),(0,[z1,z2,z3,z195,z108,z8,z6]),(0,[z1,z2,z3,z4,z8,z448,z6])],[(0,[z0,z1,z3,z4,z8,z6,z39]),(0,[z449,z1,z2,z3,z4,z8,z6])],[(1,[z0,z145,z3,z4,z8,z6]),(0,[z1,z2,z3,z50,z4,z8,z13]),(0,[z61,z1,z2,z3,z4,z8,z39]),(0,[z450,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z451,z6]),(0,[z55,z1,z2,z3,z56,z8,z6]),(1,[z233,z1,z2,z4,z8,z6])],[(0,[z452,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z58,z39]),(0,[z1,z2,z3,z4,z8,z453,z6]),(0,[z1,z2,z3,z4,z454,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z455])],[(0,[z456,z1,z2,z3,z4,z8,z6]),(0,[z1,z457,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z23,z69,z6]),(0,[z1,z2,z3,z4,z458,z8,z6]),(0,[z1,z2,z459,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z460,z8,z6]),(0,[z1,z105,z2,z3,z90,z8,z6])],[(0,[z1,z2,z3,z461,z4,z8,z6]),(0,[z61,z2,z3,z4,z8,z6,z87]),(0,[z1,z462,z2,z3,z4,z8,z6]),(0,[z1,z2,z463,z3,z4,z8,z6]),(0,[z1,z59,z2,z122,z4,z8,z6]),(0,[z464,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z96,z3,z4,z8,z13]),(0,[z1,z2,z3,z104,z50,z8,z6]),(0,[z1,z2,z3,z287,z4,z8,z6]),(1,[z1,z3,z4,z8,z13,z39]),(0,[z1,z2,z3,z4,z8,z6,z350]),(0,[z1,z2,z3,z4,z8,z6,z118]),(0,[z1,z465,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z411,z4,z8,z6])],[(0,[z1,z2,z3,z111,z4,z8,z39]),(0,[z1,z466,z2,z3,z4,z8,z6])]],
   [[(1,[z1,z2,z3,z4,z467,z6]),(0,[z1,z2,z107,z3,z4,z8,z6])],[(1,[z190,z1,z3,z4,z8,z6]),(0,[z1,z216,z43,z3,z4,z8,z6]),(0,[z468,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z151,z6])],[(0,[z170,z1,z2,z3,z50,z8,z6]),(0,[z469,z1,z2,z3,z4,z8,z6]),(0,[z1,z211,z3,z4,z23,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z470])],[(1,[z1,z2,z3,z4,z8,z117]),(0,[z12,z1,z3,z4,z79,z8,z6]),(0,[z1,z2,z3,z4,z8,z17,z6]),(0,[z1,z290,z67,z3,z4,z8,z6]),(0,[z1,z471,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z472,z4,z8,z6])],[(0,[z1,z2,z3,z473,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z474]),(0,[z1,z97,z2,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z6,z475])],[(0,[z1,z2,z476,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z477,z6]),(0,[z323,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z147,z39]),(0,[z89,z1,z2,z3,z4,z108,z6]),(0,[z1,z478,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z479,z4,z8,z6]),(0,[z1,z78,z2,z3,z111,z8,z6]),(0,[z1,z2,z3,z4,z8,z13,z480])],[(0,[z1,z2,z3,z4,z8,z481,z6]),(0,[z1,z2,z3,z4,z8,z482,z6]),(0,[z1,z43,z3,z132,z4,z8,z6]),(0,[z1,z2,z3,z483,z4,z8,z6]),(0,[z1,z76,z2,z3,z4,z8,z6]),(0,[z1,z97,z2,z3,z349,z8,z6]),(0,[z441,z1,z2,z3,z4,z8,z13]),(0,[z484,z1,z2,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z485,z3,z4,z8,z6]),(0,[z235,z61,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z87,z30]),(0,[z1,z126,z3,z132,z4,z8,z6]),(1,[z1,z78,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z6,z486])],[(0,[z1,z2,z96,z132,z4,z8,z6]),(0,[z487,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z23,z8,z6]),(0,[z1,z2,z3,z4,z8,z149,z6])],[(0,[z14,z2,z3,z20,z4,z8,z6])],[(0,[z1,z2,z3,z50,z79,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z87]),(0,[z488,z1,z2,z3,z4,z8,z6]),(0,[z1,z51,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z489,z6]),(0,[z1,z2,z3,z4,z100,z8,z6])],[(0,[z1,z2,z3,z68,z104,z8,z6])],[(0,[z1,z490,z2,z3,z4,z8,z6]),(0,[z1,z2,z122,z3,z4,z8,z13]),(0,[z491,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z492,z6])],[(0,[z1,z2,z3,z4,z8,z13,z39]),(0,[z1,z2,z3,z493,z4,z8,z39]),(0,[z1,z2,z3,z4,z274,z8,z6])],[(0,[z494,z1,z2,z3,z4,z8,z6]),(0,[z1,z76,z2,z3,z4,z8,z13]),(0,[z1,z3,z4,z8,z13,z6,z39]),(0,[z1,z2,z3,z495,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z496,z6])]],
   [[(0,[z112,z1,z126,z3,z4,z8,z6]),(0,[z497,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z498,z3,z4,z8,z6]),(0,[z12,z1,z211,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z13,z47]),(0,[z55,z1,z2,z3,z4,z8,z6]),(0,[z499,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z500])],[(0,[z1,z126,z216,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z157]),(0,[z1,z2,z3,z4,z23,z8,z13])],[(0,[z1,z126,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z501,z8,z6]),(0,[z1,z2,z3,z4,z90,z8,z6]),(0,[z1,z502,z2,z3,z4,z8,z6])],[(0,[z170,z1,z2,z72,z3,z8,z6]),(0,[z1,z2,z3,z4,z503,z8,z6]),(0,[z171,z1,z2,z3,z4,z69,z6]),(0,[z504,z1,z2,z3,z4,z8,z6]),(0,[z1,z505,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z506,z6]),(0,[z1,z2,z3,z4,z158,z24,z6])],[(0,[z2,z3,z50,z4,z128,z8,z6]),(0,[z1,z2,z3,z507,z4,z8,z6]),(0,[z508,z1,z2,z3,z4,z8,z13])],[(0,[z0,z1,z2,z3,z91,z8,z6]),(0,[z1,z2,z3,z4,z8,z229,z6]),(1,[z61,z2,z3,z4,z8,z87]),(0,[z1,z2,z3,z4,z8,z509,z6]),(0,[z235,z1,z2,z3,z4,z8,z13]),(0,[z510,z1,z2,z3,z4,z8,z6]),(0,[z1,z211,z2,z3,z4,z8,z321])],[(0,[z1,z511,z2,z3,z4,z8,z6]),(0,[z512,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z513,z3,z4,z8,z6]),(0,[z1,z216,z2,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z147,z13]),(0,[z1,z67,z2,z3,z4,z8,z118]),(0,[z1,z105,z2,z3,z4,z8,z169])],[(0,[z1,z2,z3,z514,z4,z8,z6]),(0,[z15,z2,z3,z50,z4,z8,z6])]],
   [[(0,[z1,z347,z2,z3,z4,z8,z6]),(0,[z452,z1,z2,z3,z20,z8,z6]),(0,[z1,z2,z3,z4,z113,z8,z6]),(0,[z1,z515,z2,z3,z4,z8,z6])],[(0,[z516,z1,z2,z3,z4,z8,z6]),(1,[z1,z347,z3,z4,z8,z6]),(0,[z1,z2,z3,z517,z4,z8,z6]),(0,[z1,z2,z518,z3,z4,z8,z6]),(0,[z1,z519,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z104,z4,z8,z6])],[(0,[z1,z2,z145,z3,z4,z8,z6]),(0,[z112,z1,z327,z3,z4,z8,z6]),(0,[z1,z126,z2,z3,z4,z8,z13]),(0,[z520,z1,z2,z3,z4,z8,z6]),(0,[z1,z521,z2,z3,z4,z8,z6])],[(1,[z1,z2,z3,z4,z8,z6]),(0,[z1,z97,z2,z3,z4,z147,z6]),(0,[z1,z3,z4,z23,z8,z147,z6]),(0,[z522,z1,z2,z3,z4,z8,z6])],[(0,[z523,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z72,z3,z212,z8,z6]),(0,[z1,z67,z524,z3,z4,z8,z6])],[(0,[z1,z525,z2,z3,z4,z8,z6]),(0,[z170,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z526,z6]),(0,[z1,z216,z2,z3,z136,z8,z6]),(0,[z1,z345,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z106,z6])],[(0,[z1,z527,z2,z3,z4,z8,z6]),(0,[z89,z41,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z8,z255,z13]),(0,[z1,z2,z3,z104,z24,z8,z6])],[(0,[z528,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z529,z8,z6]),(0,[z1,z2,z3,z4,z530,z8,z6])]],
   [[(0,[z1,z2,z3,z267,z20,z4,z6]),(0,[z531,z1,z2,z3,z4,z8,z6]),(0,[z171,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z231,z8,z6]),(0,[z1,z2,z3,z532,z4,z8,z6]),(0,[z1,z76,z2,z3,z79,z8,z6]),(0,[z1,z2,z3,z4,z8,z533,z6])],[(1,[z1,z2,z3,z4,z388,z6]),(0,[z1,z2,z3,z4,z8,z534,z6]),(0,[z1,z2,z3,z4,z8,z191,z6]),(0,[z1,z2,z3,z132,z4,z8,z6]),(0,[z1,z535,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z410,z6]),(0,[z1,z78,z2,z3,z4,z8,z39]),(0,[z1,z2,z3,z536,z4,z8,z6]),(0,[z1,z2,z3,z104,z4,z8,z13]),(0,[z1,z537,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z538,z6]),(0,[z1,z2,z122,z3,z4,z8,z149]),(0,[z1,z2,z3,z4,z8,z539,z6])],[(0,[z1,z2,z145,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z6,z540]),(0,[z1,z541,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z206,z6]),(0,[z1,z542,z2,z3,z4,z8,z6]),(0,[z1,z2,z543,z3,z4,z8,z6]),(0,[z1,z2,z3,z544,z4,z8,z6]),(0,[z1,z2,z3,z4,z545,z8,z6])],[(0,[z1,z2,z3,z546,z4,z8,z6]),(0,[z1,z2,z3,z128,z8,z58,z6]),(0,[z1,z2,z3,z4,z547,z8,z6]),(0,[z1,z2,z3,z548,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z56,z4,z467,z6]),(0,[z1,z2,z3,z4,z8,z244,z6])],[(0,[z1,z2,z3,z549,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z550,z6]),(0,[z12,z1,z2,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z13,z169]),(1,[z1,z2,z3,z4,z100,z6]),(0,[z1,z2,z3,z4,z8,z551,z6])],[(0,[z1,z552,z2,z3,z4,z8,z6]),(0,[z19,z1,z2,z3,z4,z8,z13]),(0,[z170,z1,z2,z3,z4,z8,z13]),(0,[z55,z170,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z4,z8,z553,z6]),(0,[z1,z126,z2,z132,z4,z8,z6]),(0,[z1,z2,z3,z4,z554,z8,z6])],[(0,[z555,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z107,z4,z108,z6])],[(0,[z1,z556,z2,z3,z4,z8,z6]),(0,[z1,z2,z122,z3,z4,z8,z30])]],
   [[(0,[z1,z2,z3,z20,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z557,z6]),(0,[z171,z1,z2,z3,z4,z8,z13]),(0,[z1,z558,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z39,z559]),(0,[z1,z2,z3,z4,z8,z467,z6]),(1,[z1,z2,z3,z4,z158,z106])],[(0,[z55,z1,z2,z3,z79,z8,z6]),(0,[z560,z1,z2,z3,z4,z8,z6]),(0,[z561,z1,z2,z3,z4,z8,z6])],[(1,[z1,z2,z3,z4,z8,z370]),(0,[z163,z1,z2,z3,z20,z4,z6]),(0,[z41,z1,z2,z3,z4,z8,z39])],[(0,[z1,z2,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z562,z8,z6]),(0,[z89,z1,z2,z4,z8,z255,z6]),(0,[z1,z105,z276,z3,z4,z8,z6])],[(0,[z61,z1,z59,z2,z3,z4,z8]),(0,[z1,z211,z2,z3,z4,z8,z13])],[(0,[z14,z1,z2,z3,z4,z8,z39]),(0,[z15,z1,z2,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z6,z563]),(0,[z1,z2,z3,z4,z564,z8,z6]),(0,[z565,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z566,z6]),(0,[z1,z216,z2,z3,z4,z8,z210]),(0,[z1,z59,z2,z3,z4,z8,z39]),(0,[z1,z567,z2,z3,z4,z8,z6]),(0,[z568,z1,z2,z3,z4,z8,z6])],[(1,[z1,z2,z3,z4,z8,z266]),(0,[z1,z2,z3,z4,z8,z569,z6]),(0,[z1,z292,z2,z3,z4,z8,z39]),(0,[z570,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z107,z3,z4,z24,z6]),(0,[z1,z2,z3,z104,z8,z6,z118])]],
   [[(0,[z1,z327,z2,z3,z4,z8,z6]),(0,[z571,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z111,z50,z8,z6]),(0,[z572,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z72,z3,z8,z58,z6])],[(1,[z19,z2,z96,z4,z8,z6]),(0,[z1,z78,z2,z3,z4,z8,z168]),(0,[z1,z2,z3,z4,z8,z39,z39]),(0,[z1,z57,z2,z3,z4,z58,z6])],[(0,[z573,z1,z2,z3,z4,z8,z6]),(0,[z574,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z104,z79,z8,z6]),(0,[z1,z575,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z480])],[(0,[z576,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z412]),(0,[z1,z2,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z212,z8,z6]),(0,[z1,z105,z2,z3,z68,z4,z8]),(0,[z1,z2,z3,z4,z8,z6,z577])],[(0,[z1,z2,z513,z3,z20,z4,z8]),(1,[z1,z2,z3,z4,z184,z6]),(0,[z1,z578,z2,z3,z4,z8,z6]),(0,[z89,z171,z1,z2,z3,z4,z6]),(0,[z2,z3,z4,z8,z191,z6,z87]),(0,[z1,z579,z2,z3,z4,z8,z6]),(0,[z55,z1,z2,z3,z104,z8,z6]),(0,[z580,z1,z2,z3,z4,z8,z6])],[(0,[z1,z581,z2,z3,z4,z8,z6]),(0,[z14,z1,z2,z3,z4,z8,z365]),(0,[z582,z1,z2,z3,z4,z8,z6]),(1,[z171,z2,z3,z4,z69,z6]),(0,[z1,z2,z3,z4,z8,z6,z82]),(0,[z1,z2,z3,z56,z4,z8,z39]),(0,[z1,z57,z2,z3,z4,z8,z13]),(0,[z55,z1,z2,z4,z212,z8,z6]),(0,[z1,z2,z3,z8,z58,z6,z118]),(0,[z1,z2,z3,z583,z4,z8,z6])],[(0,[z0,z1,z2,z3,z4,z229,z6]),(0,[z1,z584,z2,z3,z4,z8,z6]),(0,[z170,z1,z2,z3,z4,z184,z6]),(0,[z1,z2,z419,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z585,z8,z6])],[(0,[z1,z2,z3,z4,z586,z8,z6]),(0,[z587,z1,z2,z3,z4,z8,z6])]],
   [[(0,[z588,z1,z2,z3,z4,z8,z6]),(0,[z1,z327,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z589,z8,z6]),(0,[z1,z2,z3,z4,z590,z8,z6]),(0,[z1,z2,z3,z4,z591,z8,z6]),(0,[z1,z2,z3,z592,z4,z8,z6]),(0,[z1,z2,z3,z4,z158,z106,z6])],[(0,[z1,z2,z3,z4,z593,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z594]),(0,[z1,z2,z3,z4,z69,z8,z39]),(0,[z1,z2,z3,z4,z595,z8,z6])],[(0,[z1,z2,z3,z4,z8,z596,z6]),(0,[z1,z2,z3,z4,z8,z597,z6]),(1,[z89,z1,z2,z4,z255,z6])],[],[(0,[z468,z1,z2,z3,z4,z8,z6])],[(0,[z163,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z598,z3,z4,z8,z6]),(0,[z1,z126,z2,z3,z4,z8,z436]),(0,[z1,z599,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z600,z8,z6])],[(0,[z1,z2,z3,z4,z8,z365,z6]),(0,[z14,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z222,z6]),(0,[z1,z2,z3,z4,z8,z601,z6])],[(1,[z1,z2,z325,z4,z8,z6]),(0,[z1,z2,z3,z4,z602,z8,z6]),(0,[z1,z327,z2,z3,z4,z8,z370]),(0,[z1,z2,z21,z3,z4,z8,z13]),(0,[z1,z603,z2,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z265,z8,z6]),(0,[z1,z2,z3,z4,z604,z8,z6]),(0,[z605,z1,z2,z3,z4,z8,z6])],[(0,[z112,z1,z3,z4,z8,z6,z39]),(0,[z1,z2,z3,z4,z8,z6,z405]),(0,[z1,z2,z3,z4,z606,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z607])],[(0,[z441,z1,z2,z3,z4,z8,z6]),(0,[z0,z1,z2,z3,z265,z8,z6]),(0,[z1,z2,z3,z4,z8,z608,z6])],[(0,[z1,z2,z609,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z191,z30]),(0,[z1,z105,z2,z3,z4,z8,z39]),(0,[z1,z2,z122,z4,z8,z149,z6])],[(0,[z1,z327,z2,z3,z4,z8,z266]),(0,[z1,z2,z3,z4,z447,z8,z6]),(0,[z1,z2,z3,z4,z8,z610,z6])],[(0,[z611,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z204])],[(0,[z0,z1,z43,z3,z4,z8,z6]),(0,[z41,z1,z2,z107,z3,z4,z6]),(0,[z1,z2,z3,z4,z8,z222,z13]),(0,[z1,z2,z3,z4,z69,z58,z6]),(0,[z1,z612,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z436]),(0,[z1,z51,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z195,z4,z8,z6]),(0,[z1,z2,z3,z4,z6,z423,z30]),(0,[z1,z2,z3,z613,z4,z8,z6])],[(0,[z1,z2,z3,z614,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z39,z169]),(0,[z1,z2,z3,z4,z8,z58,z6]),(0,[z1,z2,z3,z68,z8,z58,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z6,z77]),(0,[z1,z2,z122,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z615,z6]),(0,[z1,z105,z67,z2,z3,z4,z8])],[(0,[z1,z2,z3,z616,z4,z8,z6]),(0,[z1,z2,z56,z4,z108,z8,z6])],[(1,[z452,z1,z2,z3,z8,z6]),(0,[z1,z126,z2,z43,z4,z8,z6]),(0,[z1,z2,z3,z4,z147,z58,z6]),(0,[z1,z2,z3,z4,z617,z8,z6]),(0,[z1,z618,z2,z3,z4,z8,z6]),(0,[z1,z290,z2,z3,z4,z8,z6])],[(0,[z619,z1,z2,z3,z4,z8,z6]),(1,[z112,z327,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z149,z87]),(0,[z1,z2,z3,z111,z4,z8,z6]),(0,[z1,z2,z3,z4,z620,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z621]),(0,[z1,z2,z3,z4,z8,z13,z244]),(0,[z55,z1,z2,z3,z8,z244,z6]),(0,[z1,z2,z3,z4,z8,z6,z622])],[(0,[z1,z2,z3,z4,z8,z6,z623])],[(0,[z1,z2,z3,z4,z8,z624,z6]),(0,[z1,z2,z3,z4,z8,z175,z6])],[(1,[z1,z2,z287,z4,z8,z6]),(0,[z61,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z108,z8,z39]),(0,[z1,z2,z3,z4,z8,z6,z312]),(0,[z1,z2,z3,z4,z8,z625,z6])],[(0,[z1,z2,z3,z4,z5,z8,z6]),(0,[z508,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z626,z8,z6]),(0,[z235,z1,z2,z3,z4,z8,z87]),(1,[z1,z126,z132,z4,z8,z6]),(0,[z1,z2,z3,z627,z4,z8,z6]),(0,[z1,z2,z3,z4,z628,z8,z6]),(0,[z99,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z58,z13]),(0,[z1,z2,z72,z3,z8,z244,z6]),(0,[z1,z2,z629,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z630,z4,z8,z6]),(0,[z631,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z632,z8,z6]),(0,[z1,z2,z3,z4,z69,z147,z6]),(0,[z235,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z405]),(0,[z1,z97,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z169])],[(0,[z171,z2,z3,z4,z69,z8,z6]),(0,[z1,z2,z3,z4,z8,z147,z6]),(0,[z1,z2,z3,z4,z8,z306,z6])],[(1,[z1,z2,z3,z4,z8,z245]),(0,[z1,z2,z3,z4,z8,z6,z210]),(1,[z1,z216,z43,z4,z8,z6]),(0,[z1,z633,z2,z3,z4,z8,z6]),(0,[z89,z1,z2,z3,z4,z24,z6])],[(0,[z634,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z111,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z635,z6]),(0,[z1,z2,z3,z4,z8,z636,z6])],[(0,[z1,z2,z3,z4,z637,z8,z6]),(0,[z1,z78,z76,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z638,z8,z6]),(0,[z1,z2,z107,z3,z4,z106,z6])],[(0,[z1,z2,z43,z96,z4,z8,z6]),(1,[z1,z2,z3,z98,z8,z6])],[(0,[z1,z202,z2,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z13,z106]),(0,[z1,z2,z3,z4,z8,z6,z423]),(1,[z1,z524,z3,z4,z8,z6])],[(1,[z1,z2,z352,z4,z8,z6]),(0,[z639,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z262,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z640]),(0,[z89,z55,z1,z2,z4,z8,z6])]],
   [[(0,[z1,z641,z2,z3,z4,z8,z6]),(1,[z1,z2,z62,z4,z8,z6]),(0,[z1,z642,z2,z3,z4,z8,z6]),(0,[z1,z97,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z6,z643])],[(0,[z12,z112,z1,z3,z4,z8,z6]),(0,[z1,z2,z3,z644,z4,z8,z6]),(0,[z1,z2,z3,z645,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z255,z6]),(0,[z1,z646,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z493,z4,z8,z6]),(0,[z1,z2,z3,z647,z4,z8,z6]),(0,[z1,z2,z3,z648,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z649]),(0,[z1,z2,z3,z4,z8,z6,z650]),(0,[z1,z2,z3,z651,z4,z8,z6]),(0,[z1,z105,z2,z3,z411,z8,z6]),(0,[z1,z652,z2,z3,z4,z8,z6])],[(0,[z0,z1,z2,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z653,z6]),(0,[z55,z1,z2,z3,z212,z8,z6])],[(0,[z1,z2,z3,z4,z349,z8,z6]),(0,[z1,z67,z2,z3,z4,z151,z6]),(0,[z1,z2,z3,z4,z654,z8,z6])],[(1,[z1,z2,z513,z3,z4,z8]),(0,[z655,z1,z2,z3,z4,z8,z6]),(0,[z656,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z657]),(0,[z658,z1,z2,z3,z4,z8,z6])],[(0,[z15,z1,z2,z3,z50,z8,z6]),(0,[z1,z2,z3,z4,z24,z8,z39])],[(0,[z1,z2,z3,z104,z128,z8,z6]),(0,[z1,z2,z3,z4,z8,z659,z6]),(0,[z1,z2,z3,z4,z108,z8,z13]),(0,[z1,z105,z2,z107,z3,z4,z6]),(0,[z1,z2,z660,z3,z4,z8,z6])]],
   [[(0,[z19,z1,z2,z3,z4,z8,z6]),(0,[z41,z2,z3,z4,z8,z222,z6]),(1,[z1,z22,z3,z4,z8,z6])],[(0,[z1,z2,z3,z661,z4,z8,z6]),(0,[z1,z2,z4,z8,z149,z6,z30])],[(0,[z1,z2,z122,z20,z4,z8,z6]),(0,[z1,z2,z3,z4,z24,z222,z6]),(1,[z1,z3,z4,z79,z8,z39]),(0,[z1,z2,z3,z4,z8,z13,z13]),(0,[z1,z2,z3,z4,z8,z662,z6]),(1,[z1,z105,z2,z3,z4,z169])],[(0,[z1,z2,z3,z49,z4,z8,z6]),(0,[z1,z2,z3,z4,z663,z8,z6]),(0,[z170,z1,z2,z3,z128,z8,z6]),(0,[z1,z2,z3,z664,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z157]),(1,[z1,z211,z3,z4,z23,z6])],[(0,[z665,z1,z2,z3,z4,z8,z6])],[(0,[z0,z12,z1,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z666,z8,z6]),(0,[z1,z667,z2,z3,z4,z8,z6])],[(0,[z668,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z669]),(0,[z1,z2,z3,z4,z670,z8,z6]),(0,[z55,z1,z2,z3,z111,z8,z6]),(1,[z1,z97,z3,z4,z147,z6]),(0,[z1,z2,z524,z3,z4,z8,z6]),(0,[z1,z67,z2,z3,z4,z158,z8]),(0,[z1,z2,z3,z68,z8,z244,z6])],[(0,[z1,z2,z3,z671,z4,z8,z6]),(0,[z1,z211,z2,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z672,z8,z6]),(0,[z258,z1,z2,z3,z4,z8,z39])],[(0,[z1,z673,z2,z3,z4,z8,z6]),(0,[z1,z2,z674,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z675,z6]),(0,[z676,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z677,z6])],[(0,[z1,z2,z3,z4,z8,z149,z191]),(0,[z1,z216,z2,z3,z4,z8,z13]),(0,[z1,z2,z72,z3,z111,z8,z6]),(0,[z1,z273,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z678,z4,z8,z6])],[(0,[z1,z2,z3,z4,z679,z8,z6]),(0,[z1,z2,z3,z4,z8,z275,z39]),(0,[z1,z2,z3,z8,z244,z6,z118]),(0,[z1,z2,z3,z4,z158,z8,z169])],[(0,[z1,z2,z3,z680,z4,z8,z6]),(0,[z1,z2,z681,z3,z4,z8,z6]),(0,[z1,z2,z62,z3,z4,z8,z6])],[(0,[z682,z1,z2,z3,z4,z8,z6]),(0,[z683,z1,z2,z3,z4,z8,z6]),(0,[z0,z2,z145,z3,z4,z8,z6]),(0,[z1,z684,z2,z3,z4,z8,z6]),(0,[z1,z273,z2,z3,z8,z6,z30]),(1,[z1,z358,z2,z3,z4,z6]),(0,[z1,z2,z3,z685,z4,z8,z6]),(0,[z1,z2,z3,z68,z4,z158,z8])],[(0,[z1,z2,z3,z4,z222,z147,z6]),(0,[z235,z1,z2,z3,z4,z8,z191]),(1,[z1,z2,z3,z4,z262,z6]),(0,[z1,z686,z2,z3,z4,z8,z6]),(0,[z1,z687,z2,z3,z4,z8,z6])],[(0,[z1,z688,z2,z3,z4,z8,z6]),(0,[z15,z1,z2,z72,z3,z8,z6]),(0,[z1,z2,z3,z111,z104,z8,z6]),(0,[z1,z2,z3,z98,z4,z8,z6]),(1,[z1,z211,z3,z4,z8,z39]),(0,[z55,z1,z2,z3,z8,z58,z6]),(0,[z1,z358,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z83,z58])]],
   [[(0,[z689,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z690,z4,z8,z6]),(0,[z1,z691,z2,z3,z4,z8,z6]),(0,[z12,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z692]),(0,[z1,z57,z2,z3,z4,z8,z6])],[(0,[z1,z693,z2,z3,z4,z8,z6]),(0,[z41,z1,z2,z3,z4,z222,z6]),(0,[z1,z2,z694,z3,z4,z8,z6]),(0,[z233,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z695])],[(0,[z1,z2,z3,z4,z79,z8,z39])],[(0,[z1,z2,z3,z696,z4,z8,z6]),(0,[z1,z2,z3,z110,z4,z8,z6]),(0,[z1,z2,z3,z4,z697,z8,z6]),(0,[z1,z2,z3,z4,z8,z698,z6]),(0,[z1,z2,z3,z4,z8,z403,z6]),(0,[z1,z2,z3,z4,z699,z8,z6])],[(0,[z1,z2,z3,z4,z8,z6,z559]),(0,[z1,z2,z3,z4,z8,z168,z6]),(0,[z1,z2,z3,z4,z8,z700,z6]),(0,[z1,z309,z2,z3,z4,z8,z6])],[(0,[z1,z78,z2,z3,z4,z8,z13]),(1,[z1,z2,z3,z4,z8,z103]),(0,[z1,z2,z3,z4,z24,z147,z6]),(0,[z1,z2,z3,z4,z701,z8,z6])],[(0,[z1,z2,z3,z267,z4,z8,z6]),(0,[z41,z1,z2,z3,z4,z8,z6]),(1,[z235,z2,z3,z4,z8,z191]),(0,[z1,z2,z3,z4,z8,z702,z6]),(0,[z1,z2,z703,z3,z4,z8,z6]),(0,[z1,z97,z3,z4,z8,z147,z6]),(0,[z1,z211,z3,z4,z8,z6,z39]),(0,[z1,z2,z3,z4,z8,z13,z149]),(0,[z1,z2,z3,z4,z8,z704,z6])],[(0,[z1,z2,z3,z4,z705,z8,z6]),(0,[z1,z2,z3,z4,z8,z706,z6]),(0,[z89,z1,z2,z3,z4,z106,z6]),(1,[z1,z2,z122,z4,z8,z149])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z707,z8,z6]),(0,[z1,z2,z3,z4,z708,z6]),(0,[z1,z345,z2,z4,z8,z30]),(0,[z1,z2,z3,z4,z8,z709])],[(0,[z0,z145,z3,z265,z8,z6]),(0,[z1,z2,z3,z710,z4,z6]),(0,[z1,z385,z3,z111,z8,z6]),(0,[z1,z2,z3,z110,z8,z13]),(0,[z1,z2,z72,z56,z8,z39]),(0,[z12,z1,z3,z4,z8,z711]),(0,[z1,z2,z3,z4,z712,z6]),(0,[z1,z2,z3,z90,z6,z169])],[(0,[z1,z2,z3,z4,z8,z713]),(0,[z1,z2,z3,z4,z714,z6]),(0,[z1,z3,z4,z8,z433,z39]),(0,[z1,z2,z3,z4,z8,z715]),(0,[z14,z2,z20,z4,z8,z39]),(0,[z1,z2,z3,z113,z8,z13]),(0,[z1,z2,z419,z4,z8,z306]),(0,[z1,z2,z3,z4,z8,z716])],[(0,[z1,z2,z325,z265,z8,z6]),(0,[z1,z3,z4,z8,z245,z39]),(0,[z1,z2,z3,z4,z8,z717]),(0,[z1,z78,z3,z4,z8,z718]),(0,[z1,z2,z3,z195,z8,z39]),(0,[z1,z719,z2,z3,z8,z6]),(0,[z1,z2,z4,z8,z149,z720])],[(0,[z41,z2,z3,z4,z222,z39]),(0,[z1,z2,z3,z8,z13,z312]),(0,[z1,z67,z2,z3,z90,z8])],[(0,[z1,z2,z3,z4,z8,z721]),(0,[z41,z2,z3,z110,z222,z6]),(0,[z1,z541,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z722]),(0,[z1,z524,z3,z4,z8,z6]),(0,[z1,z3,z4,z8,z723,z39]),(0,[z1,z2,z724,z4,z8,z6]),(0,[z1,z2,z122,z4,z8,z720]),(0,[z1,z2,z3,z4,z8,z725]),(0,[z1,z2,z3,z90,z158,z6])],[(0,[z406,z1,z3,z4,z8,z39]),(0,[z163,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z726,z6]),(0,[z1,z2,z3,z4,z8,z727]),(0,[z1,z2,z3,z4,z8,z77]),(0,[z1,z2,z3,z4,z38,z39]),(0,[z1,z2,z3,z411,z8,z39])],[(0,[z1,z2,z3,z4,z728,z6]),(0,[z1,z2,z3,z136,z8,z13]),(0,[z1,z2,z3,z4,z158,z615])]],
   [[(0,[z0,z1,z352,z4,z8,z39]),(0,[z1,z729,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z730]),(0,[z1,z209,z3,z4,z8,z13]),(0,[z1,z3,z4,z8,z448,z39])],[(0,[z1,z2,z3,z91,z5,z6]),(0,[z1,z731,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z732,z6]),(0,[z12,z1,z3,z4,z8,z168]),(0,[z1,z2,z3,z349,z147,z6]),(0,[z1,z2,z3,z98,z8,z157]),(0,[z1,z2,z3,z4,z8,z733]),(0,[z1,z2,z4,z8,z175,z6]),(0,[z1,z2,z3,z4,z6,z734])],[(0,[z1,z2,z3,z265,z8,z117]),(0,[z14,z2,z20,z4,z8,z365]),(0,[z1,z347,z513,z3,z4,z8]),(0,[z1,z2,z3,z4,z178,z6]),(0,[z1,z2,z3,z4,z151,z13]),(0,[z1,z2,z3,z4,z735,z6]),(0,[z1,z2,z72,z8,z6,z623]),(0,[z1,z276,z3,z68,z4,z8]),(0,[z1,z2,z3,z4,z8,z736])],[(0,[z1,z167,z2,z122,z4,z8]),(0,[z1,z2,z3,z4,z737,z8]),(0,[z1,z2,z72,z8,z175,z6])],[(0,[z1,z2,z513,z3,z4,z8]),(0,[z1,z97,z3,z98,z147,z6]),(0,[z1,z2,z3,z58,z6,z294])],[(0,[z452,z14,z2,z20,z8,z6]),(0,[z1,z2,z738,z3,z4,z8]),(0,[z1,z739,z2,z3,z4,z8]),(0,[z1,z322,z2,z3,z58,z6]),(0,[z1,z3,z4,z147,z275,z39]),(0,[z1,z211,z3,z4,z409,z6]),(0,[z1,z524,z3,z4,z8,z13])],[(0,[z1,z2,z20,z4,z8,z204]),(0,[z163,z1,z2,z3,z4,z13]),(0,[z198,z2,z3,z128,z8,z6]),(0,[z1,z2,z3,z4,z8,z740]),(0,[z1,z2,z3,z4,z8,z115]),(0,[z1,z2,z3,z4,z8,z741]),(0,[z233,z1,z2,z4,z23,z6]),(0,[z1,z2,z3,z4,z742,z6])],[(0,[z0,z1,z3,z4,z8,z39]),(0,[z1,z167,z2,z4,z8,z30]),(0,[z1,z2,z3,z8,z6,z743]),(0,[z1,z2,z3,z231,z178,z6]),(0,[z1,z76,z3,z79,z38,z6]),(0,[z1,z22,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z744]),(0,[z1,z2,z745,z3,z4,z8])]],
   [[(0,[z1,z2,z3,z4,z8,z746]),(0,[z1,z2,z3,z4,z8,z747]),(0,[z1,z2,z3,z4,z748,z6]),(0,[z1,z2,z3,z4,z749,z6]),(0,[z1,z2,z3,z68,z158,z58])],[(0,[z1,z2,z750,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z217]),(0,[z1,z216,z43,z4,z262,z6]),(0,[z1,z3,z4,z79,z8,z39]),(0,[z1,z2,z4,z8,z175,z13]),(0,[z1,z751,z3,z4,z8,z6]),(0,[z1,z299,z2,z3,z58,z6]),(0,[z1,z309,z2,z3,z90,z8]),(0,[z1,z105,z2,z3,z4,z169])],[(0,[z1,z3,z4,z8,z752,z39]),(0,[z1,z2,z3,z4,z753,z6]),(0,[z1,z2,z3,z4,z8,z754]),(0,[z1,z2,z3,z4,z178,z13]),(0,[z1,z2,z3,z4,z8,z157])],[(0,[z1,z755,z3,z4,z8,z6]),(0,[z1,z2,z3,z756,z8,z6]),(0,[z1,z2,z3,z4,z8,z757])],[(0,[z1,z2,z3,z195,z8,z13]),(0,[z1,z358,z2,z3,z6,z312])],[(0,[z1,z2,z3,z4,z8,z758]),(0,[z1,z2,z759,z4,z8,z6]),(0,[z1,z2,z107,z4,z422,z6]),(0,[z1,z2,z3,z4,z303,z106]),(0,[z1,z57,z2,z3,z83,z58]),(0,[z233,z1,z2,z4,z8,z83])],[(0,[z1,z2,z3,z265,z8,z245]),(0,[z1,z2,z3,z231,z8,z217]),(0,[z89,z1,z2,z291,z4,z6])],[(0,[z0,z145,z3,z91,z8,z6]),(0,[z12,z1,z3,z4,z229,z6]),(0,[z1,z2,z760,z4,z8,z6]),(0,[z163,z1,z347,z3,z4,z6]),(0,[z1,z3,z4,z8,z13,z432])]],
   [[(0,[z2,z761,z3,z4,z8,z6])],[(0,[z1,z2,z325,z91,z8,z6]),(0,[z1,z457,z3,z4,z8,z39]),(0,[z1,z273,z2,z3,z8,z39]),(0,[z762,z1,z2,z3,z8,z6])],[(0,[z1,z2,z3,z4,z8,z763]),(0,[z0,z145,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z764,z6]),(0,[z1,z2,z3,z4,z206,z39]),(1,[z1,z3,z765,z8,z6]),(0,[z1,z97,z3,z4,z147,z157]),(0,[z233,z1,z2,z4,z8,z39]),(0,[z1,z766,z3,z4,z8,z6])],[(0,[z1,z2,z352,z265,z8,z6]),(0,[z1,z2,z3,z767,z8,z6]),(0,[z1,z3,z50,z79,z8,z39]),(0,[z1,z2,z287,z4,z8,z191]),(0,[z1,z2,z768,z3,z4,z8]),(0,[z769,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z98,z8,z103]),(0,[z1,z2,z107,z3,z90,z6]),(0,[z1,z2,z3,z4,z158,z736])],[(0,[z1,z2,z3,z4,z8,z770]),(0,[z1,z385,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z771]),(0,[z772,z1,z2,z3,z4,z6]),(0,[z508,z1,z3,z4,z8,z383]),(0,[z1,z2,z3,z4,z773,z6])],[(0,[z1,z78,z3,z111,z8,z168]),(0,[z1,z211,z3,z4,z8,z723]),(0,[z1,z59,z273,z2,z8,z30])],[(0,[z1,z2,z3,z4,z229,z13]),(0,[z1,z2,z3,z4,z8,z774]),(0,[z148,z2,z3,z4,z8,z403]),(0,[z99,z2,z3,z4,z8,z326]),(0,[z1,z775,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z776]),(0,[z1,z2,z3,z4,z8,z777]),(0,[z1,z2,z3,z259,z8,z137]),(0,[z1,z276,z3,z4,z8,z106])]],
   [[(0,[z1,z2,z3,z4,z778,z6]),(0,[z1,z347,z3,z267,z4,z6]),(0,[z1,z2,z3,z4,z467,z39])],[(0,[z190,z1,z3,z4,z8,z39]),(0,[z1,z2,z3,z779,z8,z6]),(0,[z1,z2,z3,z4,z8,z780]),(0,[z1,z2,z3,z104,z781,z6])],[(0,[z1,z2,z3,z265,z8,z6]),(0,[z1,z2,z782,z4,z8,z6]),(0,[z1,z3,z4,z8,z783,z6]),(0,[z1,z202,z3,z4,z147,z39]),(0,[z1,z202,z2,z3,z4,z254]),(0,[z1,z2,z3,z4,z8,z784])],[(0,[z1,z785,z3,z4,z8,z6]),(0,[z89,z1,z2,z664,z4,z6]),(0,[z1,z76,z3,z79,z206,z6]),(0,[z1,z293,z3,z4,z8,z13])],[(0,[z112,z1,z3,z4,z8,z39]),(0,[z1,z2,z786,z3,z4,z8]),(0,[z1,z2,z3,z4,z787,z6]),(1,[z1,z3,z4,z8,z711])],[(0,[z1,z3,z4,z8,z229,z39]),(0,[z1,z344,z2,z3,z58,z6]),(0,[z1,z2,z3,z4,z8,z788]),(0,[z235,z2,z3,z4,z8,z191]),(0,[z61,z2,z3,z4,z8,z789]),(0,[z1,z3,z4,z8,z509,z39]),(0,[z1,z2,z3,z790,z8,z6]),(0,[z1,z2,z3,z104,z24,z13])],[(0,[z1,z2,z3,z133,z24,z6]),(0,[z1,z2,z3,z791,z8,z6])],[(0,[z170,z686,z2,z3,z8,z6]),(0,[z1,z2,z72,z81,z8,z6]),(0,[z1,z2,z107,z3,z113,z6]),(1,[z2,z3,z4,z8,z789]),(0,[z1,z2,z3,z8,z39,z312]),(0,[z1,z2,z4,z8,z6,z792])]],
   [[(0,[z1,z2,z3,z793,z8,z6]),(0,[z1,z2,z3,z4,z8,z794]),(0,[z1,z2,z3,z4,z795,z6]),(0,[z1,z59,z358,z2,z4,z30])],[(0,[z1,z2,z3,z4,z8,z796]),(0,[z1,z2,z3,z4,z8,z797]),(0,[z1,z2,z3,z128,z184,z6]),(0,[z1,z126,z132,z4,z8,z436]),(0,[z1,z2,z3,z798,z8,z6]),(0,[z1,z290,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z447,z275])],[(0,[z1,z2,z3,z265,z8,z13]),(0,[z1,z2,z3,z267,z4,z13]),(0,[z1,z10,z2,z3,z58,z6]),(0,[z1,z2,z799,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z789]),(0,[z1,z273,z2,z3,z8,z13])],[(0,[z1,z2,z800,z4,z8,z6]),(0,[z1,z2,z3,z4,z206,z13]),(0,[z1,z276,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z13,z423]),(0,[z1,z2,z3,z8,z244,z801])],[(0,[z1,z2,z3,z91,z8,z245]),(0,[z1,z2,z761,z4,z8,z6]),(0,[z1,z802,z3,z4,z8,z6]),(0,[z1,z372,z3,z4,z8,z39]),(0,[z1,z97,z3,z4,z147,z103]),(0,[z1,z2,z3,z803,z8,z6])],[(0,[z1,z2,z3,z804,z8,z6]),(0,[z247,z1,z3,z4,z8,z39])],[(0,[z1,z2,z3,z805,z8,z6]),(0,[z1,z2,z3,z4,z8,z806]),(0,[z1,z2,z3,z4,z158,z151])],[(0,[z15,z2,z3,z50,z8,z6])]],
   [[(0,[z1,z2,z3,z807,z8,z6]),(0,[z1,z808,z3,z4,z8,z6]),(0,[z1,z2,z3,z113,z69,z6]),(0,[z1,z2,z3,z8,z6,z312]),(0,[z1,z2,z3,z4,z8,z809]),(0,[z1,z2,z3,z810,z8,z6])],[(0,[z1,z2,z352,z91,z8,z6]),(0,[z55,z1,z2,z3,z184,z6]),(0,[z233,z1,z2,z4,z147,z6]),(0,[z1,z2,z3,z8,z39,z811]),(0,[z1,z290,z3,z4,z8,z13]),(0,[z812,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z813]),(0,[z1,z59,z2,z4,z8,z30])],[(0,[z2,z761,z20,z4,z8,z6]),(0,[z15,z2,z3,z814,z8,z6]),(0,[z1,z2,z72,z56,z467,z6]),(0,[z1,z2,z3,z68,z90,z8])],[(0,[z1,z347,z3,z49,z8,z6]),(0,[z1,z815,z2,z3,z8,z6]),(0,[z1,z646,z3,z4,z8,z39]),(0,[z55,z1,z2,z816,z8,z6]),(0,[z1,z2,z3,z817,z8,z6])],[(0,[z1,z818,z2,z3,z4,z6]),(0,[z1,z819,z3,z4,z8,z6]),(0,[z1,z820,z3,z4,z8,z6])],[(0,[z1,z2,z3,z821,z8,z6]),(0,[z1,z2,z3,z49,z8,z6]),(0,[z1,z2,z3,z8,z822,z6]),(0,[z89,z1,z2,z4,z218,z6]),(0,[z1,z273,z2,z3,z6,z423])],[(0,[z1,z126,z759,z4,z8,z6]),(0,[z1,z216,z43,z136,z8,z6]),(0,[z1,z2,z3,z4,z8,z82]),(0,[z12,z1,z3,z4,z8,z321]),(0,[z1,z309,z2,z107,z3,z4]),(0,[z1,z2,z3,z4,z8,z83])],[(0,[z0,z145,z3,z4,z5,z6]),(0,[z1,z2,z3,z823,z8,z6]),(0,[z1,z2,z107,z124,z4,z6])]],
   [[(0,[z1,z2,z3,z91,z8,z6]),(0,[z1,z177,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z824,z6]),(0,[z825,z1,z2,z3,z4,z6])],[(0,[z1,z347,z3,z4,z8,z39]),(0,[z1,z167,z2,z3,z267,z4]),(0,[z170,z2,z3,z128,z8,z39]),(0,[z1,z2,z3,z765,z8,z6]),(0,[z1,z22,z3,z90,z8,z6])],[(0,[z0,z112,z3,z4,z8,z39]),(0,[z1,z2,z325,z4,z229,z6]),(0,[z1,z2,z3,z49,z267,z6]),(0,[z1,z2,z3,z826,z8,z6]),(0,[z1,z2,z3,z4,z8,z827]),(0,[z1,z2,z4,z8,z828,z6]),(0,[z1,z67,z276,z3,z4,z8])],[(0,[z1,z2,z3,z4,z8,z829]),(0,[z1,z347,z3,z4,z8,z830]),(0,[z1,z2,z3,z4,z6,z831]),(0,[z1,z76,z3,z79,z8,z39]),(0,[z1,z211,z3,z4,z23,z82]),(0,[z1,z2,z3,z4,z8,z832]),(0,[z1,z2,z4,z108,z467,z6]),(0,[z833,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z834,z6]),(0,[z27,z1,z3,z4,z8,z39]),(0,[z1,z2,z96,z4,z8,z204]),(0,[z1,z2,z3,z110,z8,z6]),(0,[z1,z2,z3,z4,z8,z835])],[(0,[z1,z2,z3,z4,z8,z836]),(0,[z1,z2,z3,z837,z8,z6]),(0,[z1,z2,z3,z49,z8,z13]),(0,[z1,z2,z3,z113,z8,z6]),(0,[z2,z3,z4,z8,z39,z838]),(0,[z89,z55,z1,z2,z58,z6])],[(0,[z1,z2,z3,z4,z839,z6]),(0,[z1,z2,z3,z349,z8,z6]),(0,[z1,z840,z2,z3,z4,z8]),(0,[z1,z3,z4,z424,z8,z39])],[(0,[z1,z2,z3,z4,z8,z841]),(0,[z235,z2,z150,z3,z4,z8])]],
   [[(0,[z1,z2,z3,z91,z8,z13]),(0,[z1,z2,z3,z4,z5,z117]),(0,[z1,z2,z3,z4,z8,z842]),(0,[z1,z177,z3,z4,z8,z13]),(0,[z825,z1,z2,z3,z4,z13]),(0,[z1,z2,z3,z843,z8,z13]),(0,[z1,z144,z3,z4,z8,z13])],[(0,[z1,z3,z4,z8,z383,z39]),(0,[z1,z3,z4,z8,z844,z6]),(0,[z1,z2,z3,z4,z388,z39]),(0,[z1,z845,z3,z4,z8,z6]),(0,[z1,z216,z43,z4,z178,z6]),(0,[z99,z1,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z846,z6]),(0,[z1,z2,z21,z4,z8,z149]),(0,[z1,z2,z3,z4,z8,z847]),(0,[z89,z1,z309,z2,z3,z4])],[(0,[z452,z1,z177,z3,z8,z6]),(0,[z1,z2,z3,z4,z848,z6]),(0,[z1,z2,z3,z136,z8,z6]),(0,[z1,z2,z3,z849,z8,z6])],[(0,[z1,z2,z3,z850,z8,z6]),(0,[z1,z2,z3,z4,z851,z6]),(0,[z1,z2,z3,z4,z8,z852]),(0,[z1,z2,z3,z4,z8,z853]),(0,[z1,z2,z3,z854,z8,z6]),(0,[z1,z2,z3,z4,z8,z711]),(0,[z1,z2,z3,z4,z158,z275]),(0,[z1,z309,z2,z4,z8,z175])],[(0,[z772,z1,z2,z287,z4,z6]),(0,[z61,z1,z3,z4,z8,z383]),(0,[z1,z2,z3,z4,z100,z39])],[(0,[z1,z2,z3,z4,z855,z6]),(0,[z1,z2,z3,z4,z8,z856]),(0,[z857,z2,z3,z4,z8,z6]),(1,[z1,z2,z4,z828,z6]),(0,[z1,z2,z3,z4,z151,z6])],[(0,[z2,z3,z4,z814,z8,z6]),(0,[z1,z2,z3,z4,z858,z6]),(0,[z2,z3,z4,z8,z6,z838]),(0,[z1,z2,z3,z349,z8,z13]),(0,[z1,z2,z107,z4,z108,z39])],[(0,[z1,z2,z3,z4,z8,z859]),(0,[z2,z3,z814,z128,z8,z6]),(0,[z1,z2,z3,z4,z860,z6]),(0,[z1,z2,z3,z4,z8,z861]),(0,[z1,z216,z43,z4,z8,z210]),(0,[z1,z862,z2,z4,z8,z6]),(0,[z1,z2,z107,z3,z17,z6])]],
   [[(0,[z1,z2,z3,z863,z8,z6]),(0,[z1,z347,z3,z4,z8,z864]),(0,[z658,z2,z20,z4,z8,z6]),(0,[z170,z2,z3,z128,z388,z6]),(0,[z1,z2,z3,z4,z8,z865]),(0,[z1,z2,z3,z866,z8,z6]),(0,[z1,z2,z3,z4,z8,z70]),(0,[z1,z216,z43,z4,z8,z217]),(1,[z1,z2,z4,z8,z720])],[(0,[z1,z2,z3,z4,z8,z867]),(0,[z1,z2,z3,z4,z8,z868]),(0,[z55,z1,z2,z212,z8,z6]),(0,[z1,z2,z3,z4,z8,z869]),(0,[z1,z309,z2,z3,z4,z158]),(0,[z1,z2,z4,z8,z6,z870]),(0,[z1,z67,z2,z3,z274,z118])],[(0,[z1,z43,z325,z4,z8,z6]),(0,[z1,z3,z4,z8,z596,z39]),(0,[z1,z2,z3,z4,z8,z864]),(0,[z170,z2,z3,z128,z8,z13]),(0,[z1,z871,z3,z4,z8,z6]),(0,[z171,z2,z3,z333,z4,z6]),(0,[z1,z2,z3,z4,z8,z872]),(0,[z873,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z8,z801])],[(0,[z1,z2,z3,z4,z8,z874]),(0,[z1,z167,z2,z3,z4,z8]),(0,[z41,z142,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z8,z168]),(0,[z1,z51,z3,z4,z8,z39]),(0,[z1,z3,z4,z8,z13,z610]),(0,[z1,z2,z3,z875,z8,z6])],[(0,[z14,z347,z20,z4,z8,z6]),(0,[z876,z1,z2,z3,z4,z8]),(0,[z1,z76,z3,z79,z8,z13]),(0,[z877,z2,z3,z4,z8,z6]),(0,[z1,z878,z2,z3,z4,z39]),(0,[z55,z1,z524,z3,z8,z6])],[(0,[z1,z2,z3,z4,z229,z245]),(0,[z452,z1,z167,z2,z3,z8]),(0,[z1,z261,z2,z3,z58,z6]),(0,[z1,z2,z122,z287,z4,z8]),(0,[z99,z2,z3,z4,z8,z191]),(0,[z12,z1,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z855,z13]),(0,[z1,z2,z3,z4,z8,z879]),(0,[z1,z59,z2,z4,z8,z720])],[(0,[z0,z145,z3,z4,z8,z117]),(0,[z14,z2,z20,z4,z8,z6]),(0,[z190,z235,z3,z4,z8,z191]),(0,[z1,z2,z3,z4,z39,z423]),(0,[z1,z2,z4,z108,z828,z6])],[(0,[z1,z2,z3,z4,z5,z39]),(0,[z1,z416,z3,z4,z147,z6]),(0,[z1,z3,z4,z8,z13,z496]),(0,[z1,z2,z3,z195,z8,z6]),(0,[z1,z2,z3,z8,z6,z880])]],
   [[(0,[z1,z3,z4,z265,z8,z39]),(0,[z1,z2,z3,z881,z8,z6]),(0,[z2,z3,z50,z814,z8,z6]),(0,[z1,z2,z882,z4,z8,z6]),(0,[z1,z78,z3,z111,z8,z39]),(0,[z1,z2,z3,z68,z8,z801])],[(0,[z19,z2,z96,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z883]),(0,[z1,z3,z4,z8,z39,z350]),(0,[z55,z1,z2,z212,z8,z13]),(0,[z397,z1,z2,z3,z58,z6])],[(0,[z1,z2,z352,z4,z229,z6]),(0,[z1,z2,z3,z136,z262,z6]),(0,[z1,z2,z72,z367,z8,z6]),(0,[z1,z537,z3,z111,z8,z6]),(0,[z1,z346,z3,z4,z23,z6]),(0,[z1,z2,z3,z411,z8,z6]),(0,[z1,z884,z3,z4,z8,z58]),(0,[z1,z885,z2,z3,z8,z6])],[(0,[z1,z2,z886,z4,z8,z6]),(0,[z1,z2,z3,z4,z887,z6]),(0,[z1,z2,z3,z4,z888,z6]),(0,[z1,z2,z889,z287,z4,z6]),(0,[z1,z2,z3,z4,z8,z210]),(0,[z1,z2,z3,z890,z8,z6]),(0,[z1,z51,z3,z4,z8,z711]),(0,[z1,z2,z3,z4,z274,z39]),(0,[z1,z2,z3,z4,z891,z6]),(0,[z1,z2,z3,z4,z8,z892])],[(0,[z26,z1,z3,z4,z8,z39]),(0,[z576,z2,z20,z4,z8,z6]),(0,[z1,z3,z4,z893,z8,z6]),(0,[z1,z691,z3,z4,z8,z39]),(0,[z1,z2,z3,z894,z8,z6]),(0,[z1,z2,z3,z4,z8,z895]),(0,[z233,z1,z57,z2,z58,z6])],[(0,[z1,z896,z2,z3,z4,z6]),(0,[z112,z249,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z6,z897]),(0,[z171,z2,z3,z4,z69,z39]),(0,[z1,z898,z3,z4,z8,z6]),(0,[z1,z2,z72,z56,z8,z13]),(0,[z1,z2,z3,z4,z8,z899]),(0,[z1,z2,z8,z175,z17,z6])],[(0,[z14,z2,z20,z4,z8,z13]),(0,[z1,z2,z72,z56,z100,z6]),(0,[z1,z2,z3,z4,z8,z900])],[(0,[z1,z2,z3,z4,z8,z901]),(0,[z1,z2,z3,z4,z8,z902]),(0,[z1,z2,z3,z104,z554,z6])]],
   [[(0,[z41,z2,z3,z4,z222,z13]),(0,[z1,z2,z3,z231,z8,z210]),(0,[z1,z2,z3,z903,z8,z6]),(0,[z1,z904,z2,z3,z4,z8]),(0,[z1,z130,z3,z4,z8,z39])],[(0,[z1,z2,z3,z4,z229,z6]),(0,[z1,z2,z513,z3,z49,z8]),(0,[z1,z3,z111,z765,z8,z6]),(0,[z1,z213,z3,z4,z147,z6]),(0,[z1,z2,z3,z4,z905,z6]),(0,[z1,z2,z3,z4,z8,z906])],[(0,[z1,z2,z3,z4,z907,z6]),(0,[z1,z2,z3,z104,z589,z6]),(0,[z1,z2,z3,z4,z38,z13]),(0,[z908,z1,z2,z3,z4,z8]),(0,[z1,z2,z3,z411,z8,z13]),(0,[z1,z667,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z909]),(0,[z1,z2,z107,z195,z108,z6])],[(0,[z1,z2,z910,z4,z8,z6]),(0,[z1,z759,z132,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z911]),(0,[z568,z2,z3,z4,z69,z6]),(0,[z1,z519,z3,z4,z8,z39]),(0,[z55,z1,z2,z8,z17,z6])],[(0,[z163,z14,z2,z20,z4,z6]),(0,[z1,z220,z3,z4,z8,z39]),(0,[z1,z478,z3,z4,z8,z13]),(0,[z1,z2,z107,z4,z6,z577])],[(0,[z0,z1,z3,z4,z8,z752]),(0,[z1,z2,z3,z4,z8,z912]),(0,[z173,z2,z3,z50,z8,z6]),(0,[z1,z346,z3,z4,z8,z39]),(0,[z1,z2,z913,z4,z8,z6]),(0,[z1,z2,z3,z68,z8,z244])],[(0,[z1,z2,z325,z4,z8,z39]),(0,[z1,z43,z473,z4,z8,z6]),(0,[z1,z2,z3,z914,z8,z6]),(0,[z1,z2,z3,z4,z915,z6]),(0,[z1,z3,z4,z628,z8,z39]),(0,[z1,z57,z2,z3,z781,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z13]),(0,[z1,z916,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z917,z6]),(0,[z1,z3,z4,z69,z147,z39]),(0,[z198,z1,z3,z4,z8,z39]),(0,[z1,z2,z3,z104,z24,z6])],[(0,[z1,z2,z3,z918,z8,z6]),(0,[z1,z2,z919,z3,z4,z8]),(0,[z1,z78,z3,z111,z8,z13]),(0,[z1,z3,z4,z8,z147,z39]),(0,[z1,z3,z4,z8,z711,z39]),(0,[z1,z2,z3,z920,z8,z39])],[(0,[z1,z2,z921,z4,z8,z6]),(0,[z922,z145,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z923]),(0,[z1,z2,z72,z3,z467,z6]),(0,[z1,z2,z3,z4,z924,z6])],[(0,[z1,z2,z3,z4,z262,z210]),(0,[z1,z3,z4,z8,z39,z500])],[(0,[z0,z558,z3,z4,z8,z6]),(0,[z1,z2,z925,z3,z4,z8]),(0,[z1,z2,z926,z4,z8,z6]),(0,[z1,z2,z3,z4,z262,z217]),(0,[z1,z2,z3,z4,z274,z13]),(0,[z1,z927,z3,z4,z8,z6])],[(0,[z1,z2,z3,z267,z4,z6]),(0,[z1,z273,z2,z3,z8,z6]),(0,[z1,z2,z107,z4,z828,z6]),(0,[z1,z67,z524,z3,z8,z118]),(0,[z1,z67,z2,z3,z8,z801])],[(0,[z0,z145,z3,z4,z8,z6]),(0,[z52,z2,z96,z4,z8,z6]),(0,[z1,z2,z3,z4,z928,z6]),(0,[z1,z2,z3,z4,z206,z6]),(0,[z1,z2,z3,z4,z929,z6]),(0,[z1,z2,z3,z930,z8,z6]),(0,[z1,z276,z3,z4,z8,z6])],[(0,[z0,z1,z3,z265,z8,z39]),(0,[z235,z2,z3,z4,z8,z789]),(0,[z1,z931,z3,z4,z8,z6])]],
   [[(0,[z1,z932,z3,z4,z8,z6]),(0,[z1,z933,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z934]),(0,[z1,z935,z3,z4,z8,z6])],[(0,[z0,z1,z3,z4,z8,z370]),(0,[z452,z1,z2,z3,z8,z39]),(0,[z1,z2,z122,z4,z8,z366]),(0,[z170,z2,z3,z814,z8,z6]),(0,[z1,z936,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z937,z6]),(0,[z1,z2,z3,z4,z8,z938]),(0,[z112,z327,z3,z4,z8,z39]),(0,[z939,z1,z2,z4,z8,z6]),(0,[z1,z3,z765,z4,z8,z6]),(0,[z1,z940,z3,z4,z8,z6])],[(1,[z2,z761,z4,z8,z6]),(0,[z1,z2,z941,z4,z8,z6]),(0,[z1,z3,z4,z8,z383,z30]),(0,[z1,z2,z3,z4,z942,z6]),(0,[z1,z2,z3,z4,z943,z6]),(0,[z1,z2,z3,z493,z8,z129]),(0,[z1,z331,z3,z4,z8,z39]),(0,[z1,z2,z122,z4,z8,z306]),(0,[z1,z2,z3,z4,z467,z6]),(0,[z55,z1,z2,z583,z8,z6])],[(0,[z1,z2,z3,z944,z8,z6]),(0,[z1,z642,z3,z4,z8,z39]),(0,[z945,z2,z3,z4,z8,z6]),(0,[z1,z537,z3,z4,z8,z39])],[(0,[z0,z145,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z946]),(0,[z1,z947,z2,z3,z8,z6]),(0,[z1,z2,z287,z4,z8,z39]),(0,[z1,z2,z3,z4,z948,z6]),(0,[z1,z202,z3,z4,z147,z6]),(0,[z233,z1,z2,z4,z8,z13])],[(0,[z1,z2,z3,z4,z8,z117]),(0,[z1,z211,z3,z4,z8,z157]),(0,[z1,z309,z2,z3,z4,z151])]],
   [[(0,[z658,z2,z3,z4,z8,z87])],[(0,[z1,z2,z3,z949,z8,z6]),(0,[z1,z3,z4,z8,z950,z6]),(0,[z2,z3,z4,z8,z789,z6]),(0,[z1,z392,z3,z4,z8,z39]),(0,[z1,z951,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z952,z6]),(0,[z1,z216,z43,z4,z8,z39])],[(0,[z1,z167,z2,z287,z4,z8]),(0,[z468,z1,z2,z3,z4,z350])],[(0,[z1,z2,z3,z4,z953,z6]),(0,[z1,z3,z4,z8,z954,z6]),(0,[z955,z1,z2,z3,z4,z8]),(0,[z1,z54,z2,z3,z58,z6]),(0,[z1,z415,z3,z4,z23,z6]),(0,[z1,z2,z3,z4,z467,z13]),(0,[z1,z2,z3,z8,z6,z956]),(0,[z1,z67,z2,z3,z8,z118])],[(0,[z1,z2,z3,z4,z957,z6]),(0,[z1,z164,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z958,z6]),(0,[z190,z1,z3,z4,z8,z13]),(0,[z1,z2,z3,z98,z8,z39])],[(0,[z1,z2,z3,z4,z8,z959]),(0,[z1,z2,z3,z960,z8,z6]),(0,[z1,z292,z3,z79,z8,z39]),(0,[z1,z2,z3,z4,z961,z6]),(0,[z1,z3,z4,z962,z147,z6]),(0,[z1,z2,z724,z4,z8,z39])],[(0,[z1,z2,z352,z4,z8,z39]),(0,[z1,z3,z671,z4,z8,z39]),(0,[z1,z963,z3,z4,z8,z6]),(0,[z1,z964,z2,z3,z4,z6]),(0,[z1,z2,z107,z4,z175,z6]),(0,[z1,z524,z3,z4,z8,z137]),(1,[z1,z2,z3,z4,z736])]],
   [[(0,[z2,z922,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z965,z6]),(0,[z14,z2,z20,z4,z8,z204]),(0,[z1,z2,z62,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z966]),(0,[z1,z2,z3,z4,z8,z321]),(0,[z1,z2,z442,z3,z58,z6]),(0,[z1,z967,z3,z4,z8,z6])],[(0,[z14,z2,z513,z20,z4,z8]),(0,[z1,z2,z968,z3,z4,z8])],[(0,[z1,z2,z3,z4,z8,z969]),(0,[z1,z3,z4,z8,z970,z6]),(0,[z971,z1,z3,z4,z8,z6]),(0,[z1,z97,z3,z4,z962,z6])],[(0,[z1,z2,z3,z972,z8,z6]),(0,[z1,z2,z3,z843,z8,z6])],[(0,[z1,z2,z325,z4,z5,z6]),(0,[z12,z1,z3,z4,z8,z245]),(0,[z1,z973,z3,z4,z8,z6]),(0,[z1,z2,z3,z974,z8,z6]),(0,[z1,z126,z132,z4,z8,z70]),(0,[z1,z2,z3,z975,z8,z6]),(0,[z1,z976,z3,z4,z8,z6])],[(0,[z0,z1,z3,z91,z8,z39]),(0,[z0,z228,z3,z4,z8,z6]),(0,[z327,z922,z3,z4,z8,z6]),(0,[z977,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z8,z6,z811]),(0,[z1,z2,z3,z4,z8,z723]),(0,[z1,z211,z3,z4,z23,z321])],[(0,[z1,z2,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z978]),(0,[z1,z3,z4,z8,z718,z39]),(0,[z1,z2,z3,z4,z961,z13]),(0,[z1,z57,z2,z175,z58,z6])],[(0,[z1,z2,z3,z979,z8,z6]),(0,[z112,z1,z3,z4,z8,z370]),(0,[z1,z2,z3,z4,z8,z980]),(0,[z1,z2,z3,z79,z206,z6]),(0,[z233,z1,z2,z79,z8,z6]),(0,[z1,z2,z3,z4,z828,z6]),(0,[z1,z502,z2,z3,z58,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z981]),(0,[z1,z2,z3,z4,z8,z830]),(0,[z1,z3,z690,z4,z8,z39]),(0,[z1,z2,z3,z982,z8,z6]),(0,[z1,z415,z3,z4,z8,z39]),(0,[z1,z22,z3,z4,z8,z39]),(0,[z1,z524,z3,z4,z151,z6])],[(0,[z1,z983,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z984,z6]),(0,[z89,z1,z2,z3,z90,z6]),(0,[z1,z309,z2,z3,z8,z118])],[(0,[z1,z2,z3,z136,z178,z6]),(0,[z1,z78,z3,z4,z8,z77]),(1,[z1,z2,z816,z8,z6])],[(0,[z1,z2,z3,z4,z8,z985]),(0,[z986,z1,z2,z3,z8,z6]),(0,[z1,z3,z4,z8,z698,z39]),(0,[z1,z2,z3,z231,z8,z39]),(0,[z1,z211,z3,z4,z23,z39])],[(0,[z1,z2,z3,z4,z987,z6]),(0,[z1,z2,z3,z4,z8,z988]),(0,[z1,z3,z765,z79,z8,z6]),(0,[z1,z2,z3,z4,z989,z6]),(0,[z1,z3,z4,z8,z168,z39]),(0,[z1,z990,z2,z3,z4,z8]),(0,[z1,z2,z3,z8,z13,z991])],[(0,[z170,z2,z3,z128,z8,z6]),(0,[z1,z3,z104,z79,z8,z39]),(0,[z1,z3,z4,z24,z147,z39]),(0,[z1,z282,z3,z4,z8,z39]),(0,[z1,z992,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z993]),(0,[z0,z1,z3,z4,z8,z436]),(0,[z1,z2,z3,z4,z8,z365]),(0,[z163,z1,z167,z2,z3,z4]),(0,[z1,z2,z3,z4,z994,z6]),(0,[z41,z2,z3,z4,z958,z6]),(0,[z235,z1,z3,z4,z8,z383]),(0,[z1,z3,z4,z8,z149,z383]),(0,[z1,z3,z4,z8,z702,z39]),(0,[z1,z2,z3,z349,z8,z157]),(0,[z1,z97,z3,z4,z147,z39])],[(0,[z1,z2,z3,z4,z8,z995]),(0,[z1,z2,z3,z996,z8,z6]),(0,[z997,z2,z3,z4,z8,z6]),(0,[z1,z76,z3,z79,z8,z6]),(0,[z1,z2,z3,z4,z998,z6])]],
   [[(0,[z1,z2,z3,z999,z8,z6]),(0,[z112,z3,z4,z8,z403,z39]),(0,[z1,z3,z4,z9,z8,z39]),(0,[z1,z612,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z1000,z6]),(0,[z1,z2,z3,z4,z8,z1001])],[(0,[z1,z2,z3,z1002,z8,z6]),(0,[z14,z2,z267,z20,z4,z6]),(0,[z1,z2,z3,z136,z8,z217]),(0,[z1,z97,z3,z349,z147,z6]),(0,[z1,z2,z3,z8,z1003,z6]),(0,[z1,z345,z2,z4,z8,z559]),(0,[z1,z2,z3,z4,z39,z1004]),(0,[z174,z1,z2,z3,z8,z47]),(0,[z48,z1,z2,z3,z58,z6]),(0,[z1,z2,z3,z4,z8,z1005])],[(0,[z0,z145,z325,z4,z8,z6]),(0,[z1,z2,z3,z1006,z8,z6]),(0,[z1,z2,z3,z4,z8,z752]),(0,[z61,z466,z2,z3,z4,z8]),(0,[z1,z524,z3,z4,z158,z8])],[(0,[z1,z2,z3,z4,z8,z1007]),(0,[z1,z3,z4,z25,z8,z39]),(0,[z1,z2,z3,z104,z545,z6])],[(0,[z1,z1008,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1009]),(0,[z1010,z1,z3,z4,z8,z6]),(0,[z1,z3,z31,z4,z8,z39])],[(0,[z1,z2,z3,z4,z1011,z6]),(0,[z1,z3,z4,z8,z383,z6]),(0,[z1,z347,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z388,z6]),(0,[z15,z2,z3,z644,z8,z6]),(0,[z89,z1,z2,z3,z113,z6]),(0,[z1,z358,z2,z3,z4,z39]),(0,[z1,z2,z3,z4,z1012,z6]),(0,[z1,z2,z3,z4,z8,z1013])],[(0,[z1,z2,z3,z1014,z8,z6]),(0,[z1,z2,z3,z4,z262,z39]),(0,[z1,z44,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z1015]),(0,[z1,z2,z3,z68,z8,z625]),(0,[z1,z2,z3,z4,z158,z334])],[(0,[z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z5,z245]),(0,[z1,z2,z3,z4,z8,z1016]),(0,[z1,z2,z3,z4,z1017,z6]),(0,[z1,z435,z2,z4,z8,z30]),(0,[z1,z1018,z3,z4,z8,z6]),(0,[z1,z59,z2,z8,z312,z30]),(0,[z1,z2,z3,z4,z6,z1019])]],
   [[(0,[z1,z2,z1020,z4,z8,z6]),(0,[z1021,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z8,z1022]),(0,[z1,z633,z3,z4,z8,z39]),(0,[z1,z2,z72,z56,z8,z6]),(0,[z1,z309,z2,z3,z4,z8]),(0,[z1,z276,z3,z90,z8,z6]),(0,[z1,z2,z3,z4,z6,z736])],[(0,[z0,z922,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1023]),(0,[z1,z2,z3,z4,z1024,z6])],[(0,[z163,z1,z177,z3,z4,z6]),(0,[z488,z2,z96,z4,z8,z6]),(0,[z1,z353,z3,z4,z8,z39]),(0,[z1,z2,z1025,z3,z4,z8])],[(0,[z1,z2,z325,z4,z8,z117]),(0,[z1,z2,z3,z1026,z8,z6]),(0,[z41,z2,z3,z4,z222,z6]),(0,[z1,z2,z3,z4,z178,z210]),(0,[z1,z2,z3,z68,z8,z129]),(0,[z55,z1,z2,z3,z151,z6])],[(0,[z1,z2,z352,z4,z5,z6]),(0,[z1,z1027,z2,z3,z4,z8]),(0,[z1,z2,z3,z231,z8,z13]),(0,[z1,z2,z3,z4,z178,z217]),(0,[z1,z2,z3,z4,z158,z106])],[(0,[z1,z3,z4,z8,z1028,z6]),(0,[z1,z2,z3,z4,z388,z13]),(0,[z1,z2,z3,z1029,z8,z6]),(0,[z1,z59,z2,z287,z4,z8]),(0,[z61,z2,z3,z4,z8,z127]),(0,[z1,z2,z3,z4,z38,z6]),(0,[z1,z2,z3,z104,z253,z6]),(0,[z1,z2,z3,z4,z1030,z39]),(0,[z1,z2,z3,z472,z24,z6])],[(0,[z1,z2,z3,z4,z8,z370]),(0,[z1,z2,z3,z4,z1031,z6]),(0,[z163,z1,z2,z3,z49,z6]),(0,[z504,z1,z3,z4,z8,z39]),(0,[z1,z232,z3,z4,z8,z39]),(0,[z1,z515,z3,z4,z8,z39]),(0,[z1,z309,z2,z72,z3,z8]),(0,[z1,z466,z2,z4,z8,z30])],[(0,[z1,z1032,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z184,z39]),(0,[z258,z2,z3,z4,z8,z87]),(0,[z1,z505,z3,z4,z8,z39]),(0,[z1,z22,z3,z411,z8,z6])]],
   [[(0,[z1,z167,z2,z3,z49,z8]),(0,[z235,z3,z4,z8,z191,z383]),(0,[z1,z878,z2,z3,z4,z6]),(0,[z1,z2,z3,z349,z8,z103]),(0,[z1,z2,z3,z4,z100,z13])],[(0,[z1,z2,z3,z4,z8,z1033]),(0,[z163,z452,z1,z2,z3,z6]),(0,[z1,z2,z3,z8,z17,z39]),(0,[z1,z2,z3,z8,z244,z657])],[(0,[z1,z2,z3,z4,z8,z1034]),(0,[z141,z1,z2,z3,z58,z6]),(0,[z1,z211,z3,z4,z962,z6]),(0,[z1,z292,z2,z3,z8,z118]),(0,[z1,z2,z107,z4,z108,z13]),(0,[z1,z2,z3,z4,z6,z423]),(1,[z1,z2,z3,z781,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z266]),(0,[z112,z1,z3,z4,z8,z436]),(0,[z80,z2,z3,z4,z222,z6]),(0,[z1,z2,z56,z8,z17,z6]),(0,[z1,z2,z3,z8,z781,z6]),(0,[z1,z2,z3,z4,z8,z1035])],[(0,[z1,z2,z3,z4,z8,z1036]),(0,[z171,z2,z3,z4,z958,z6]),(0,[z1,z78,z3,z111,z8,z6])],[(0,[z0,z145,z3,z4,z8,z245]),(0,[z19,z2,z96,z4,z8,z6]),(0,[z1,z347,z167,z3,z4,z8]),(0,[z1,z3,z4,z147,z58,z39]),(0,[z1,z3,z4,z617,z8,z39]),(0,[z89,z1,z2,z4,z255,z39]),(0,[z1,z2,z816,z212,z8,z6]),(0,[z1,z2,z694,z3,z58,z6])],[(0,[z0,z1,z3,z4,z229,z39]),(1,[z922,z3,z4,z8,z6]),(0,[z170,z2,z3,z128,z184,z6]),(0,[z1,z2,z3,z259,z8,z244]),(0,[z1,z2,z3,z454,z58,z6]),(0,[z1,z2,z4,z828,z255,z6])],[(0,[z1,z2,z325,z4,z8,z245]),(0,[z1,z2,z3,z4,z8,z1037]),(0,[z116,z2,z3,z4,z69,z6]),(0,[z1,z2,z3,z4,z274,z6])]],
   [[(0,[z15,z2,z3,z50,z8,z39])],[(0,[z1,z922,z3,z4,z8,z6]),(0,[z1,z57,z2,z3,z58,z39]),(0,[z1,z2,z3,z4,z106,z736])],[(0,[z1,z2,z3,z4,z1038,z6]),(0,[z0,z145,z352,z4,z8,z6]),(0,[z1,z2,z3,z4,z206,z77])],[(0,[z1,z2,z3,z1039,z4,z6]),(0,[z1,z3,z4,z135,z8,z39]),(0,[z1,z177,z3,z49,z8,z6]),(0,[z1,z1040,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z1041]),(0,[z1,z2,z3,z1042,z8,z39]),(0,[z1,z2,z3,z4,z1043,z6]),(0,[z1,z309,z2,z3,z4,z169])],[(0,[z190,z1,z3,z4,z8,z245]),(0,[z1,z2,z3,z4,z8,z1044]),(0,[z1,z3,z4,z8,z6,z1045]),(0,[z1,z2,z3,z4,z13,z1046]),(0,[z1,z290,z3,z4,z151,z6])],[(0,[z19,z2,z96,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z1047])],[(0,[z112,z922,z3,z4,z8,z6]),(0,[z1,z925,z177,z3,z4,z8]),(0,[z1,z2,z1048,z4,z8,z6]),(0,[z2,z3,z4,z69,z958,z6]),(0,[z1,z211,z3,z4,z147,z39]),(0,[z258,z2,z3,z4,z8,z339]),(0,[z55,z1,z2,z8,z175,z6])],[(0,[z1,z2,z3,z4,z8,z1049]),(0,[z84,z2,z3,z50,z8,z6]),(0,[z2,z3,z4,z8,z958,z6]),(0,[z1,z2,z3,z889,z4,z6]),(0,[z1,z673,z2,z4,z8,z30]),(0,[z1,z213,z3,z79,z8,z6])]],
   [[(0,[z1050,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z184,z13]),(0,[z1,z2,z3,z90,z8,z39])],[(0,[z1,z347,z325,z4,z8,z6]),(0,[z1,z123,z3,z4,z8,z39]),(0,[z171,z2,z3,z4,z69,z13]),(0,[z233,z1,z2,z4,z8,z6])],[(0,[z1,z2,z3,z1051,z4,z8]),(0,[z1,z2,z3,z4,z206,z115]),(0,[z1,z290,z3,z4,z8,z168]),(0,[z1,z165,z3,z4,z8,z39]),(0,[z1,z2,z4,z8,z83,z175])],[(0,[z1,z2,z325,z4,z8,z6]),(0,[z1,z2,z352,z4,z8,z117]),(1,[z1,z3,z4,z229,z39]),(0,[z1,z3,z4,z8,z1052,z6]),(0,[z1,z2,z1053,z4,z8,z6]),(0,[z1,z3,z4,z962,z8,z6])],[(0,[z1,z2,z1054,z4,z8,z39])],[(0,[z1,z3,z4,z8,z1055,z6]),(0,[z1,z2,z4,z8,z1056,z6]),(0,[z1,z3,z4,z8,z13,z39]),(0,[z89,z1,z2,z3,z17,z6]),(0,[z1,z2,z3,z8,z1057,z6]),(0,[z1,z309,z884,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z801])],[(0,[z1,z2,z3,z4,z1058,z6]),(0,[z1,z1059,z3,z4,z8,z6]),(0,[z1,z2,z3,z113,z8,z39]),(0,[z89,z1,z2,z4,z255,z13])],[(0,[z1,z2,z3,z4,z8,z1060]),(0,[z1,z2,z3,z4,z106,z650])]],
   [[(0,[z1,z2,z1061,z4,z8,z6]),(0,[z190,z1,z3,z4,z8,z6]),(0,[z1,z2,z4,z8,z1062,z6]),(0,[z1,z2,z1063,z4,z8,z6]),(0,[z1064,z2,z3,z4,z8,z6]),(0,[z1,z243,z3,z79,z8,z6]),(0,[z1,z2,z1065,z4,z8,z6]),(0,[z89,z1,z3,z4,z147,z39]),(0,[z508,z2,z3,z4,z8,z127]),(0,[z1,z2,z3,z8,z6,z991])],[(0,[z1,z2,z3,z265,z229,z6]),(0,[z452,z1,z2,z513,z3,z8]),(0,[z1,z2,z3,z1066,z8,z6]),(0,[z1,z1067,z2,z3,z4,z8]),(0,[z1,z197,z3,z4,z8,z39]),(0,[z1,z3,z79,z8,z129,z39])],[(0,[z1,z2,z3,z4,z8,z1068]),(0,[z1,z126,z132,z4,z8,z39]),(0,[z1,z2,z3,z1069,z8,z6])],[(0,[z1,z2,z325,z4,z8,z13]),(0,[z1,z2,z1070,z4,z8,z6]),(0,[z2,z3,z4,z8,z789,z87]),(0,[z55,z1,z309,z2,z3,z8]),(0,[z1,z2,z3,z6,z312,z423])],[(0,[z1,z1071,z2,z3,z4,z8]),(0,[z55,z1,z2,z680,z8,z6]),(0,[z1,z43,z759,z4,z8,z6])],[(0,[z1,z2,z3,z1072,z8,z6]),(1,[z2,z3,z4,z958,z6]),(0,[z1,z3,z759,z4,z8,z6]),(0,[z1,z78,z3,z765,z8,z6]),(0,[z1,z3,z4,z8,z13,z711]),(0,[z1,z2,z56,z816,z8,z6]),(0,[z1,z2,z3,z4,z8,z1073])],[(0,[z1,z2,z3,z1074,z8,z6]),(0,[z1,z202,z2,z3,z4,z169])],[(0,[z112,z327,z3,z4,z8,z6]),(0,[z1,z2,z352,z4,z8,z245]),(1,[z1,z3,z265,z8,z39]),(0,[z1,z2,z3,z4,z8,z1075]),(0,[z19,z2,z761,z4,z8,z6]),(0,[z1,z78,z3,z4,z8,z39]),(0,[z89,z1,z276,z3,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z1076]),(0,[z14,z167,z2,z20,z4,z8]),(0,[z1,z1077,z2,z3,z4,z8]),(0,[z1,z2,z3,z8,z1078,z6]),(0,[z1,z2,z3,z4,z8,z1079]),(0,[z1,z2,z3,z1080,z8,z6]),(0,[z89,z1,z2,z4,z467,z6]),(0,[z1,z2,z3,z1081,z8,z6])],[(0,[z1,z2,z1082,z3,z4,z8]),(0,[z1,z2,z1083,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1084]),(0,[z1,z2,z3,z1085,z8,z6]),(0,[z1,z524,z3,z4,z8,z39]),(0,[z323,z1,z2,z4,z8,z480])],[(0,[z1,z2,z3,z4,z8,z1086]),(0,[z1,z2,z3,z1087,z8,z6]),(0,[z163,z1,z2,z3,z4,z39])],[(0,[z1,z2,z3,z4,z8,z1088]),(0,[z1,z59,z2,z4,z8,z480]),(0,[z1,z2,z3,z4,z736,z169])],[(0,[z1,z2,z3,z1089,z8,z6]),(0,[z14,z177,z20,z4,z8,z6]),(0,[z1,z2,z3,z111,z206,z6])],[(0,[z1,z347,z43,z4,z8,z6]),(0,[z1,z2,z122,z438,z4,z8]),(0,[z1,z2,z3,z4,z8,z1090]),(0,[z1,z22,z3,z4,z8,z321]),(0,[z1,z2,z4,z8,z175,z39])],[(0,[z1,z2,z3,z4,z8,z245]),(0,[z1,z2,z3,z1091,z8,z6]),(0,[z1,z2,z3,z4,z1092,z6]),(0,[z452,z1,z2,z3,z8,z13]),(0,[z61,z2,z62,z4,z8,z87]),(0,[z1,z216,z43,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1093]),(0,[z1,z2,z3,z4,z178,z39]),(0,[z1,z2,z3,z4,z8,z1094]),(0,[z1,z2,z3,z1074,z8,z13])],[(0,[z1,z2,z3,z1095,z8,z6]),(0,[z112,z327,z3,z4,z8,z13]),(0,[z1,z105,z2,z3,z4,z350]),(0,[z1,z2,z3,z24,z781,z6])]],
   [[(0,[z1,z123,z3,z4,z147,z6]),(0,[z1,z884,z3,z4,z8,z6])],[(0,[z1,z3,z4,z222,z147,z39]),(0,[z1,z2,z3,z98,z8,z6]),(0,[z55,z1,z2,z672,z8,z6]),(0,[z1,z2,z3,z4,z8,z1096])],[(0,[z1,z2,z1097,z4,z8,z6]),(0,[z1,z2,z3,z1098,z8,z6]),(0,[z1,z2,z287,z4,z8,z13]),(0,[z1,z292,z3,z79,z8,z6])],[(0,[z1,z2,z352,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1099]),(0,[z1,z1100,z3,z4,z8,z6]),(0,[z41,z2,z3,z113,z222,z6]),(0,[z1,z126,z132,z4,z8,z13]),(0,[z1,z216,z43,z231,z8,z6]),(0,[z1,z76,z3,z79,z8,z77]),(0,[z1,z2,z3,z4,z303,z425]),(0,[z1,z2,z4,z8,z6,z720])],[(0,[z1,z2,z62,z4,z8,z6]),(0,[z61,z2,z3,z4,z8,z87]),(0,[z1,z2,z3,z4,z8,z1101]),(0,[z1,z694,z3,z4,z8,z39])],[(0,[z1,z2,z1102,z4,z8,z6]),(0,[z1,z2,z1103,z4,z8,z6]),(0,[z1,z2,z3,z1104,z8,z6]),(0,[z1,z3,z4,z8,z263,z39]),(0,[z1,z2,z3,z1105,z8,z6]),(0,[z1,z2,z3,z4,z8,z720]),(0,[z1,z2,z3,z151,z6,z118])],[(0,[z112,z327,z3,z4,z8,z370]),(0,[z1,z2,z3,z4,z8,z1106]),(0,[z1,z1107,z3,z4,z8,z6]),(0,[z1,z3,z4,z697,z8,z39]),(0,[z1,z216,z43,z4,z8,z13]),(0,[z1,z2,z3,z8,z1108,z6]),(0,[z1,z1109,z2,z3,z4,z6])],[(0,[z1,z2,z3,z91,z229,z6]),(0,[z452,z1,z347,z3,z8,z6]),(0,[z1,z3,z4,z8,z700,z39]),(0,[z1,z358,z273,z2,z3,z6])]],
   [[(0,[z1,z347,z3,z4,z8,z6]),(0,[z1,z2,z1110,z4,z8,z6]),(0,[z1,z2,z3,z50,z184,z6]),(0,[z1,z2,z3,z4,z8,z1111]),(0,[z1112,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1113]),(1,[z1,z884,z3,z4,z8]),(0,[z1,z105,z276,z3,z4,z169])],[(0,[z1,z2,z1114,z4,z8,z6]),(0,[z1,z2,z3,z1115,z8,z6]),(0,[z1,z2,z3,z1116,z8,z6]),(0,[z1,z3,z280,z4,z8,z39]),(0,[z1,z703,z3,z4,z8,z39]),(0,[z1,z2,z3,z98,z8,z13])],[(0,[z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z229,z39]),(0,[z1,z2,z3,z1117,z4,z6]),(0,[z1,z2,z3,z4,z1118,z6]),(0,[z1,z2,z3,z4,z8,z1119]),(0,[z1,z2,z3,z4,z8,z718]),(0,[z1,z105,z2,z3,z4,z736])],[(0,[z1,z2,z352,z4,z8,z13]),(0,[z112,z327,z3,z4,z8,z266]),(0,[z1,z2,z1120,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1121]),(0,[z1,z2,z3,z136,z8,z210]),(0,[z1,z76,z3,z79,z8,z115]),(0,[z1,z2,z21,z4,z8,z410]),(0,[z89,z1,z2,z4,z828,z6])],[(0,[z1,z126,z325,z4,z8,z6]),(0,[z1,z2,z62,z4,z8,z13]),(0,[z55,z1,z2,z699,z8,z6])],[(0,[z1,z2,z3,z4,z1122,z6]),(0,[z1123,z2,z3,z4,z8,z6]),(0,[z1,z67,z2,z3,z8,z640]),(0,[z1,z276,z3,z4,z8,z425])],[(0,[z1,z2,z3,z4,z8,z1124]),(0,[z2,z96,z761,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1125]),(0,[z55,z1,z2,z278,z8,z6]),(0,[z1,z2,z3,z4,z8,z1126])],[(0,[z1,z3,z4,z229,z6,z39]),(0,[z1,z2,z3,z4,z8,z1127]),(0,[z1,z2,z3,z231,z8,z6]),(0,[z1,z211,z3,z4,z23,z6]),(0,[z769,z2,z3,z4,z8,z39]),(0,[z1,z292,z2,z3,z8,z412])]],
   [[(0,[z2,z3,z4,z958,z222,z6]),(0,[z1,z2,z3,z4,z1128,z6]),(0,[z1,z78,z3,z79,z8,z39]),(0,[z1,z2,z3,z4,z6,z1046])],[(0,[z1,z2,z3,z4,z8,z1129]),(0,[z1,z216,z759,z4,z8,z6]),(0,[z1,z2,z3,z4,z38,z77]),(0,[z1,z78,z3,z111,z8,z405]),(0,[z1,z2,z3,z104,z24,z39]),(0,[z1,z2,z1114,z4,z8,z13]),(0,[z1,z374,z3,z4,z8,z13]),(0,[z1,z59,z2,z4,z423,z30]),(0,[z1,z2,z3,z8,z6,z801])],[(0,[z1,z97,z3,z4,z147,z6]),(0,[z1,z3,z4,z8,z39,z47]),(0,[z1130,z2,z3,z4,z8,z6])],[(0,[z588,z1,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z1131]),(0,[z1,z177,z3,z267,z4,z6]),(0,[z247,z2,z3,z4,z222,z6]),(0,[z1132,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z1133,z8,z6]),(0,[z1,z2,z3,z4,z100,z6])],[(0,[z1,z2,z3,z4,z1134,z6]),(0,[z1135,z1,z2,z3,z8,z6]),(0,[z112,z3,z4,z8,z403,z6]),(0,[z1,z3,z4,z1136,z8,z6]),(0,[z1,z2,z3,z4,z8,z1137]),(0,[z1,z22,z3,z4,z8,z13])],[(0,[z258,z112,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z6,z1004]),(0,[z1,z2,z3,z4,z8,z1138]),(0,[z1123,z2,z3,z4,z8,z13]),(0,[z1,z2,z107,z4,z108,z6]),(0,[z1,z2,z4,z8,z720,z30]),(0,[z1139,z1,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1140]),(0,[z1,z1141,z3,z4,z8,z6]),(0,[z1,z105,z2,z3,z90,z169])],[(0,[z1,z2,z3,z265,z8,z39]),(0,[z1,z2,z3,z267,z4,z39]),(0,[z1,z2,z3,z240,z58,z6]),(0,[z1,z1142,z3,z4,z8,z6])],[(0,[z1,z167,z177,z3,z4,z8]),(0,[z1,z1143,z3,z4,z8,z6]),(0,[z1,z3,z4,z8,z13,z383]),(0,[z1,z2,z3,z4,z1144,z6]),(0,[z1,z276,z3,z4,z8,z39])]],
   [[(0,[z876,z1,z177,z3,z4,z8]),(0,[z1145,z2,z3,z4,z8,z6]),(0,[z1,z3,z79,z8,z58,z39]),(0,[z1,z3,z4,z23,z962,z6]),(0,[z1,z3,z4,z8,z39,z73]),(0,[z1,z105,z2,z3,z4,z649])],[(0,[z14,z2,z761,z4,z8,z6]),(0,[z1,z2,z72,z3,z184,z6]),(0,[z1,z2,z3,z4,z38,z115]),(0,[z1,z2,z3,z1146,z8,z6]),(0,[z1,z2,z4,z816,z8,z6]),(0,[z1,z358,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z262,z6]),(0,[z1,z97,z3,z4,z147,z13]),(0,[z1,z3,z4,z324,z8,z39]),(0,[z1,z3,z4,z8,z39,z85]),(0,[z1,z524,z3,z4,z274,z6])],[(0,[z1,z347,z132,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1147]),(0,[z1,z211,z3,z4,z8,z39]),(1,[z1,z3,z4,z962,z6]),(0,[z1,z107,z3,z4,z147,z39]),(0,[z1,z2,z72,z816,z8,z6]),(0,[z1,z2,z3,z285,z24,z6])],[(0,[z1,z3,z265,z8,z6,z39]),(0,[z1,z2,z3,z4,z1148,z6]),(0,[z1,z2,z3,z4,z1149,z6]),(0,[z1,z3,z4,z79,z8,z77]),(0,[z1,z78,z3,z647,z8,z6]),(0,[z1,z521,z3,z111,z8,z6]),(0,[z1,z2,z760,z4,z8,z13])],[(0,[z1,z2,z3,z91,z8,z117]),(0,[z1,z2,z3,z4,z8,z1150]),(0,[z1,z2,z3,z4,z1151,z6]),(0,[z1,z76,z3,z765,z8,z6]),(0,[z1,z290,z3,z4,z8,z39]),(0,[z89,z1,z2,z4,z175,z6]),(0,[z1,z105,z2,z3,z4,z151])],[(0,[z1,z3,z4,z8,z137,z39]),(0,[z762,z1,z2,z3,z8,z13])],[(0,[z1,z2,z3,z231,z262,z6]),(0,[z656,z1,z3,z4,z8,z39]),(0,[z1,z2,z107,z108,z17,z6])]],
   [[(0,[z12,z1,z3,z265,z8,z6]),(0,[z60,z1,z3,z4,z8,z39]),(0,[z0,z1,z3,z4,z5,z39]),(0,[z1,z2,z3,z4,z8,z1152]),(0,[z1,z2,z3,z1153,z8,z6]),(0,[z1145,z2,z3,z4,z8,z13])],[(0,[z1,z2,z3,z1154,z8,z6]),(0,[z1,z2,z3,z4,z8,z103]),(0,[z1,z2,z3,z4,z1030,z6]),(0,[z1,z358,z2,z3,z4,z13])],[(0,[z1,z2,z3,z4,z1155,z6]),(0,[z1,z2,z3,z4,z262,z13]),(0,[z2,z3,z4,z8,z1156,z6]),(0,[z1,z1157,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z184,z6]),(0,[z1,z2,z3,z4,z1158,z6]),(0,[z1,z2,z122,z4,z8,z149]),(0,[z1,z2,z3,z8,z801,z118])],[(0,[z1,z2,z3,z4,z1159,z6]),(0,[z171,z2,z3,z4,z69,z6]),(0,[z1,z1160,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1161])],[(0,[z1,z2,z3,z4,z1162,z6]),(0,[z1,z2,z3,z8,z17,z6]),(0,[z1,z57,z309,z2,z3,z58]),(0,[z1,z22,z105,z3,z4,z169])],[(0,[z1,z2,z3,z4,z1163,z6]),(0,[z1,z2,z3,z4,z8,z1164]),(0,[z80,z2,z3,z128,z8,z6]),(0,[z1,z2,z3,z8,z1165,z6]),(0,[z55,z1,z3,z79,z8,z39]),(0,[z1,z2,z3,z349,z23,z6]),(0,[z1,z1166,z2,z4,z8,z6]),(0,[z1,z105,z2,z3,z411,z169])],[(0,[z1,z1167,z3,z4,z8,z6]),(0,[z1,z2,z3,z1168,z8,z6]),(0,[z1,z368,z3,z4,z8,z39]),(0,[z1,z815,z2,z3,z8,z39]),(0,[z1,z2,z884,z3,z4,z8])]],
   [[(0,[z1,z2,z3,z8,z1169,z6]),(0,[z1,z2,z1170,z4,z8,z6]),(0,[z1,z2,z3,z68,z151,z6]),(0,[z1,z2,z3,z68,z8,z65])],[(0,[z14,z2,z49,z20,z8,z6]),(0,[z1,z2,z3,z49,z8,z39]),(0,[z1,z2,z1104,z287,z8,z6]),(0,[z1,z2,z3,z1171,z8,z6]),(0,[z1,z2,z223,z4,z8,z149]),(0,[z89,z1,z2,z4,z255,z6]),(0,[z1,z2,z3,z1172,z8,z6]),(0,[z1,z2,z3,z8,z1173,z6])],[(0,[z1,z1174,z2,z3,z8,z6]),(0,[z163,z1,z2,z513,z3,z4]),(0,[z1,z2,z3,z1175,z8,z6]),(0,[z1,z2,z3,z4,z8,z1176]),(0,[z1,z309,z2,z3,z68,z8])],[(0,[z1,z2,z3,z4,z8,z1177]),(0,[z1,z2,z3,z4,z1178,z6]),(0,[z1,z2,z3,z4,z8,z1179]),(0,[z1,z3,z4,z8,z321,z39])],[(0,[z1,z2,z3,z91,z8,z39]),(0,[z1,z177,z3,z4,z8,z39]),(0,[z1,z2,z3,z1180,z8,z6]),(0,[z1,z2,z3,z4,z8,z1181])],[(0,[z1,z3,z128,z79,z8,z39]),(0,[z1,z542,z3,z4,z8,z39]),(0,[z1,z2,z3,z8,z17,z13]),(0,[z1,z57,z2,z3,z58,z6]),(0,[z1,z276,z3,z4,z8,z169])],[(0,[z1,z2,z3,z114,z24,z6]),(0,[z256,z2,z3,z4,z8,z191]),(0,[z1,z3,z4,z8,z384,z39]),(0,[z1,z276,z3,z411,z8,z6])],[(0,[z1,z1182,z3,z4,z8,z6]),(0,[z1,z2,z3,z1042,z8,z6]),(0,[z1,z105,z524,z3,z4,z8]),(0,[z1,z67,z2,z3,z151,z118])]],
   [[(0,[z0,z1,z325,z4,z8,z39]),(0,[z1,z2,z3,z110,z8,z39]),(0,[z1,z3,z4,z8,z711,z6]),(0,[z1,z2,z3,z920,z8,z6])],[(0,[z235,z2,z3,z4,z8,z403]),(0,[z1,z2,z4,z175,z467,z6])],[(0,[z508,z1,z3,z4,z8,z39]),(1,[z2,z3,z814,z8,z6]),(0,[z1,z2,z3,z349,z8,z39]),(0,[z89,z1,z2,z4,z662,z6])],[(0,[z1,z2,z3,z265,z5,z6]),(0,[z1,z2,z3,z4,z1183,z6]),(0,[z1,z2,z3,z4,z1184,z6]),(0,[z1,z3,z4,z8,z196,z39]),(0,[z1,z276,z107,z3,z4,z6]),(0,[z1,z766,z309,z3,z4,z8])],[(0,[z1,z2,z3,z4,z8,z204]),(0,[z15,z2,z3,z50,z8,z13]),(0,[z1,z3,z4,z404,z8,z39]),(0,[z1,z2,z3,z90,z8,z6])],[(0,[z0,z145,z3,z4,z229,z6]),(0,[z1,z1185,z2,z3,z8,z6]),(0,[z1,z2,z3,z4,z1186,z6]),(0,[z1,z2,z3,z814,z8,z6]),(0,[z1,z2,z3,z113,z222,z6]),(0,[z1,z2,z3,z4,z8,z436]),(0,[z1,z3,z4,z8,z147,z157]),(0,[z1,z2,z3,z4,z846,z39]),(0,[z1,z57,z2,z3,z58,z13]),(0,[z1,z67,z2,z3,z8,z47]),(0,[z1,z1187,z3,z4,z8,z6])],[(0,[z1,z2,z3,z8,z6,z1188]),(0,[z1,z205,z3,z4,z8,z39]),(1,[z1,z759,z4,z8,z6]),(0,[z1,z2,z3,z136,z8,z39]),(0,[z1,z524,z3,z4,z8,z244])],[(0,[z1,z2,z3,z4,z8,z1189]),(0,[z1,z2,z3,z4,z1190,z6]),(0,[z1,z353,z3,z79,z8,z6]),(0,[z61,z2,z287,z4,z8,z87]),(0,[z2,z3,z4,z8,z191,z789]),(0,[z520,z1,z3,z4,z8,z39]),(0,[z1,z521,z3,z4,z8,z39]),(0,[z1,z2,z3,z4,z8,z1191]),(0,[z1,z524,z3,z4,z8,z118])]],
   [[(0,[z1,z2,z3,z4,z1192,z6]),(0,[z1,z2,z1054,z4,z8,z6]),(0,[z1,z2,z72,z3,z151,z6])],[(0,[z452,z1,z2,z3,z8,z6]),(0,[z1,z164,z43,z4,z8,z6]),(0,[z1,z541,z3,z4,z23,z6]),(0,[z1,z2,z3,z1193,z8,z6]),(0,[z89,z1,z2,z4,z675,z6]),(0,[z1,z2,z3,z4,z151,z39])],[(0,[z1,z2,z3,z4,z1194,z6]),(0,[z1,z2,z513,z3,z267,z4]),(0,[z1,z72,z3,z79,z8,z39]),(0,[z1,z2,z3,z4,z962,z6]),(0,[z1,z300,z2,z3,z58,z6])],[(0,[z1132,z1,z2,z287,z8,z6]),(0,[z1,z304,z3,z4,z8,z39]),(0,[z1,z524,z72,z3,z8,z6]),(0,[z1,z2,z3,z781,z58,z6])],[(0,[z1,z2,z3,z1195,z8,z6]),(0,[z1,z1196,z3,z4,z8,z6]),(0,[z1,z2,z287,z4,z8,z87]),(0,[z1,z3,z4,z8,z425,z39]),(0,[z1,z2,z3,z90,z8,z13]),(0,[z1,z290,z67,z3,z8,z118])],[(0,[z1,z2,z1197,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1198]),(0,[z1,z2,z287,z4,z8,z6]),(0,[z55,z1,z2,z212,z8,z39]),(0,[z55,z1,z2,z3,z467,z6]),(0,[z1,z2,z3,z4,z781,z6])],[(0,[z1,z2,z3,z4,z229,z117]),(0,[z1,z513,z177,z3,z4,z8]),(0,[z452,z1,z2,z3,z267,z6]),(0,[z1,z126,z132,z4,z8,z6]),(0,[z1,z290,z3,z4,z274,z6])],[(0,[z1,z2,z3,z4,z8,z1199]),(0,[z1,z2,z3,z4,z8,z405]),(0,[z233,z1,z2,z111,z8,z6]),(0,[z1,z2,z3,z816,z8,z6]),(0,[z1,z2,z3,z4,z8,z1200]),(0,[z233,z1,z309,z2,z4,z8])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 521) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 521).take 513) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1034).take 224) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1258)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [521, 513, 224] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 90).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 90).take 94).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 184).take 72).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [90, 94, 72] = true :=
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

end PEqualNP.Outside.L_meta_39849

theorem PEqualNP.Outside.L_meta_39849 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373984 * 2 ^ 32 + 4008364160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373984 * 2 ^ 32 + 4008364160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39849.solve