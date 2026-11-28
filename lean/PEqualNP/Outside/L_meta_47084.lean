import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47084

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
  Nat.testBit (4008241384 * 2 ^ 32 + 3907578016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00071450b142c2d4#64 ++ 0x0001c5142c50b0b5#64 ++ 0xf50f3cf1f3c7c7fe#64 ++ 0xfd43cf3c7cf1f1ff#64 : BitVec 256),
   (0x1470492654995970#64 ++ 0x051c12499526565c#64 ++ 0xfef0cf3e7cf9f9f3#64 ++ 0xffbc33cf9f3e7e7c#64 : BitVec 256),
   (0x2300a28b0a2c2c28#64 ++ 0x08c028a2c28b0b0a#64 ++ 0xf700f3cf8f3e3e3f#64 ++ 0x7dc03cf3e3cf8f8f#64 : BitVec 256),
   (0x4bbb03f00fc03780#64 ++ 0x52eec0fc03f00de0#64 ++ 0x5bff03f00fc03fc3#64 ++ 0xd6ffc0fc03f00ff0#64 : BitVec 256),
   (0x8bddfc000ff78000#64 ++ 0xa2f77f0003fde000#64 ++ 0xabfffc000fffc003#64 ++ 0xeaffff0003fff000#64 : BitVec 256),
   (0xc7eefffde0000001#64 ++ 0x31fbbfff78000000#64 ++ 0xcffffffff0000003#64 ++ 0xb3fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [3, 4]⟩, ⟨.and, [6, 5]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [9, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0xf50f3cf1f3c7c7fe 0xfd43cf3c7cf1f1ff

def z1 : W := mkw 0x1470492654995970 0x051c12499526565c 0xfef0cf3e7cf9f9f3 0xffbc33cf9f3e7e7c

def z2 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0xf700f3cf8f3e3e3f 0x7dc03cf3e3cf8f8f

def z3 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z4 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0xabfffc000fffc003 0xeaffff0003fff000

def z5 : W := mkw 0x8bdffc50aff78000 0xa2f7ff142bfde000 0xeffffcf1ffffc003 0xfbffff3c7ffff000

def z6 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0xcffffffff0000003 0xb3fffffffc000000

def z7 : W := mkw 0xe7eefffdea242409 0x39fbbfff7a890902 0xcffffffff306060f 0xb3fffffffcc18183

def z8 : W := mkw 0x3740ea8f5a3d6c78 0x0dd03aa3d68f5b1e 0xf700ffcfff3ffe3f 0x7dc03ff3ffcfff8f

def z9 : W := mkw 0xd7feffffe4991921 0x35ffbffff9264648 0xcffffffffc383803 0xb3ffffffff0e0e00

def z10 : W := mkw 0xabddfe890ff7a408 0xaaf77fa243fde902 0xabfffcc18fffc60f 0xeaffff3063fff183

def z11 : W := mkw 0x0300a0000a240000 0x00c0280002890000 0xa300f0000f3e0003 0x68c03c0003cf8000

def z12 : W := mkw 0xc7eefffdea240001 0x31fbbfff7a890000 0xefffffffff3e0003 0xfbffffffffcf8000

def z13 : W := mkw 0x8fddfc0deff78001 0xa3f77f037bfde000 0xaffffc0fffffc003 0xebffff03fffff000

def z14 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0x000f0c3070c1c1c0 0x8003c30c1c307070

def z15 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0x0200c30e0c383801 0x008030c3830e0e00

def z16 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0x010f3cf1f3c7c7cc 0x8043cf3c7cf1f1f3

def z17 : W := mkw 0x0350e8000eb50000 0x00d43a0003ad4000 0xabf0fc000fffc003 0xeafc3f0003fff000

def z18 : W := mkw 0x8444fc0de0000001 0x21113f0378000000 0x8400fc0ff0000000 0x21003f03fc000000

def z19 : W := mkw 0xcbfffff00ff7b780 0xf2fffffc03fdede0 0xfbfffff00fffffc3 0xfefffffc03fffff0

def z20 : W := mkw 0xa744fe8fea2c2c29 0x29d13fa3fa8b0b0a 0xf700ffcfff3e3e3f 0x7dc03ff3ffcf8f8f

def z21 : W := mkw 0x2307b6dbab6eaeac 0x08c1edb6eadbabab 0xf70ff3cf8f3e3e3f 0x7dc3fcf3e3cf8f8f

def z22 : W := mkw 0x4bbb03f01fc2f7d4 0x52eec0fc07f0bdf5 0x7bff03f00fc7ffff 0xdeffc0fc03f1ffff

def z23 : W := mkw 0x1420012650085970 0x050800499402165c 0x5400033e700039f0 0x150000cf9c000e7c

def z24 : W := mkw 0x8b8db4000b668000 0xa2e36d0002d9a000 0x010f300003060000 0x0043cc0000c18000

def z25 : W := mkw 0x081100000fc03780 0x4204400003f00de0 0x100000000fc03fc0 0x4400000003f00ff0

def z26 : W := mkw 0x83ccfc0000378000 0xa0f33f00000de000 0xabfffc00003fc003 0xaaffff00000ff000

def z27 : W := mkw 0x442203fde0000001 0x110880ff78000000 0x440003fff0000000 0x110000fffc000000

def z28 : W := mkw 0x83ccfc0000000000 0x20f33f0000000000 0x8bfffc0000000003 0xa2ffff0000000000

def z29 : W := mkw 0xc7effffde1428285 0x31fbffff7850a0a1 0xcffffffff306060f 0xb3fffffffcc18183

def z30 : W := mkw 0x00061450a0000000 0x0001851428000000 0xf50f3cf1f306063e 0xfd43cf3c7cc1818f

def z31 : W := mkw 0x00071450a1428284 0x0001c5142850a0a1 0xf50f30c18306063e 0x7d43cc3060c1818f

def z32 : W := mkw 0xdffffff65ffffff0 0xf7fffffd97fffffc 0xfffffffe7ffffff3 0xffffffff9ffffffc

def z33 : W := mkw 0x0440480440000000 0x0110120110000000 0x8400cc0e70000000 0x210033039c000000

def z34 : W := mkw 0x48bb017005c01380 0x522ec05c017004e0 0x08ff003000c001c0 0x823fc00c00300070

def z35 : W := mkw 0x2300a2890a242408 0x08c028a242890902 0x010030c18306060c 0x00400c3060c18183

def z36 : W := mkw 0x48bb017005c01380 0x522ec05c017004e0 0x5aff03300cc039c3 0xd6bfc0cc03300e70

def z37 : W := mkw 0x6bbba3fb0fec3fa8 0x5aeee8fec3fb0fea 0x5bffc3fe0ff83fc3 0xd6fff0ff83fe0ff0

def z38 : W := mkw 0x14271576f14adbf4 0x0509c55dbc52b6fd 0xf50f3ffff3c7fffe 0xfd43cffffcf1ffff

def z39 : W := mkw 0x8bddfc0005d38000 0xa2f77f000174e000 0x8bfffc0000c1c003 0xa2ffff0000307000

def z40 : W := mkw 0x1011000215dbdbf4 0x040440008576f6fd 0x300000000ffffffc 0x4c00000003ffffff

def z41 : W := mkw 0x14775d76f5dbdbf4 0x051dd75dbd76f6fd 0xffffffffffffffff 0xffffffffffffffff

def z42 : W := mkw 0x0000000000000000 0x0000000000000000 0xf50030c18306063e 0x7d400c3060c1818f

def z43 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0x0affcf3e70000001 0x82bff3cf9c000000

def z44 : W := mkw 0x0000000200080820 0x0000000080020208 0xf600c30e0c383833 0x7d8030c3830e0e0c

def z45 : W := mkw 0x3770ebaf5ebd7d78 0x0ddc3aebd7af5f5e 0xfff0ffffffffffff 0xfffc3fffffffffff

def z46 : W := mkw 0x00020050b00042d4 0x000080142c0010b5 0xf4000cf1f0c1c7fe 0xfd00033c7c3071ff

def z47 : W := mkw 0x4bbba3f00fe43780 0x52eee8fc03f90de0 0xfbfff3f00ffe3fc3 0xfefffcfc03ff8ff0

def z48 : W := mkw 0x2000028b00082c28 0x080000a2c0020b0a 0x540003cf80003e3c 0x150000f3e0000f8f

def z49 : W := mkw 0xabddfe8b0fffac28 0xaaf77fa2c3ffeb0a 0xffffffcf8ffffe3f 0xfffffff3e3ffff8f

def z50 : W := mkw 0x081100000ff78000 0x8204400003fde000 0x200000000fffc000 0x4800000003fff000

def z51 : W := mkw 0x200716dbb14aeefc 0x0801c5b6ec52bbbf 0xf50f3ffff3c7fffe 0xfd43cffffcf1ffff

def z52 : W := mkw 0x1470492454915150 0x051c124915245454 0xcef0cf3e70c1c1c3 0xb3bc33cf9c307070

def z53 : W := mkw 0x2302a2dbba2c6efc 0x08c0a8b6ee8b1bbf 0xf700f3ffff3e3fff 0x7dc03cffffcf8fff

def z54 : W := mkw 0x402203f000003780 0x500880fc00000de0 0x500003f000003fc0 0x140000fc00000ff0

def z55 : W := mkw 0x8044fc0000378000 0xa0113f00000de000 0xa000fc00003fc000 0x28003f00000ff000

def z56 : W := mkw 0x47aa03fde0000001 0x11ea80ff78000000 0x4fff03fff0000003 0x93ffc0fffc000000

def z57 : W := mkw 0xab8db68b0b6eac28 0xaae36da2c2dbab0a 0xf70ff3cf8f3e3e3f 0x7dc3fcf3e3cf8f8f

def z58 : W := mkw 0x2007b45bb16ecafc 0x0801ed16ec5bb2bf 0xf50ffcfff3ffc7fe 0xfd43ff3ffcfff1ff

def z59 : W := mkw 0x0300a28900000000 0x00c028a240000000 0xc700f3cf80000003 0x31c03cf3e0000000

def z60 : W := mkw 0xe7eeffffea2c2c29 0x39fbbffffa8b0b0a 0xffffffffff3e3e3f 0xffffffffffcf8f8f

def z61 : W := mkw 0x1470492444911100 0x051c124911244440 0x08f0000000000000 0x023c000000000000

def z62 : W := mkw 0x5ff84ba65e997d70 0x57fe12e997a65f5c 0xfef0cf3e7cf9f9f3 0xffbc33cf9f3e7e7c

def z63 : W := mkw 0xc38eb6d9a0000001 0x30e3adb668000000 0xc50f3cf1f0000002 0xb143cf3c7c000000

def z64 : W := mkw 0x6bb8a3ab0eac3d28 0x5aee28eac3ab0f4a 0xfff0f3cf8f3e3e3f 0x7ffc3cf3e3cf8f8f

def z65 : W := mkw 0x442617fde0000001 0x110985ff78000000 0xc50f3ffff0000002 0xb143cffffc000000

def z66 : W := mkw 0x2000028b00082c28 0x080000a2c0020b0a 0xf600c3cf8c383e3f 0x7d8030f3e30e0f8f

def z67 : W := mkw 0x8bddfe800ff7a400 0xa2f77fa003fde900 0xfbffffc00ffffe03 0xfefffff003ffff80

def z68 : W := mkw 0x0307b6d9b142c2d4 0x00c1edb66c50b0b5 0xf70ffffff3c7c7ff 0xfdc3fffffcf1f1ff

def z69 : W := mkw 0x0000000200080820 0x0000000080020208 0xf700f3cf8f3e3e3f 0x7dc03cf3e3cf8f8f

def z70 : W := mkw 0x04665d74e0000000 0x0119975d38000000 0xcffffffff0000003 0xb3fffffffc000000

def z71 : W := mkw 0x00041400a0028004 0x000105002800a001 0x000030018006000c 0x00000c0060018003

def z72 : W := mkw 0x2307b6dbbb6eeefc 0x08c1edb6eedbbbbf 0xf70fffffffffffff 0xfdc3ffffffffffff

def z73 : W := mkw 0x4b8f16d0ab42a684 0x52e3c5b42ad0a9a1 0x010f30c18306060c 0x0043cc3060c18183

def z74 : W := mkw 0x2301a28b1b6eeefc 0x08c068a2c6dbbbbf 0xf700f3cf8fffffff 0x7dc03cf3e3ffffff

def z75 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0x550033cf83063e3c 0x15400cf3e0c18f8f

def z76 : W := mkw 0x0b9900000fc00000 0x02e6400003f00000 0x0bff00000fc00003 0xc2ffc00003f00000

def z77 : W := mkw 0xc38eb6d9a0000001 0x30e3adb668000000 0x010f30c180000000 0x0043cc3060000000

def z78 : W := mkw 0xd7f8ebaf44991921 0x35fe3aebd1264648 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z79 : W := mkw 0xa044fc0b003f8828 0xa8113f02c00fe20a 0xa400fc0f803fc03c 0x29003f03e00ff00f

def z80 : W := mkw 0x2303a2db0b6c2ea8 0x08c0e8b6c2db0baa 0xf70ff3ff8ffe3fff 0xfdc3fcffe3ff8fff

def z81 : W := mkw 0xcffefffdee803501 0x73ffbfff7ba00d40 0xcffffffffc003803 0xb3ffffffff000e00

def z82 : W := mkw 0xc38eb6d9a0000001 0x30e3adb668000000 0xc70ff3cf80000003 0x31c3fcf3e0000000

def z83 : W := mkw 0x48bf1570b5c2d3d4 0x522fc55c2d70b4f5 0xfdff3cf1f3c7c7fe 0xff7fcf3c7cf1f1ff

def z84 : W := mkw 0x88dd5c000ff78000 0xa237570003fde000 0x28ff0c000fffc000 0xca3fc30003fff000

def z85 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0xfffffffff306063f 0xfffffffffcc1818f

def z86 : W := mkw 0x0002005000000000 0x0000801400000000 0x410f00f000000002 0x9043c03c00000000

def z87 : W := mkw 0x5ffb4bf65fd97ff0 0x57fed2fd97f65ffc 0xffffcffe7ff9fff3 0xfffff3ff9ffe7ffc

def z88 : W := mkw 0x5cfb497455d153d0 0x573ed25d157454f4 0x08ff0c3070c1c1c0 0x823fc30c1c307070

def z89 : W := mkw 0x9ffdfd264fff9920 0xa7ff7f4993ffe648 0xabffff0e0ffff803 0xeaffffc383fffe00

def z90 : W := mkw 0x83c8e80000000000 0x20f23a0000000000 0x0af0c00000000001 0x02bc300000000000

def z91 : W := mkw 0x0300a0020a2c0820 0x00c02800828b0208 0xf700f30e0f3e3833 0x7dc03cc383cf8e0c

def z92 : W := mkw 0x04675d74f142c2d4 0x0119d75d3c50b0b5 0xfffffffff3c7c7ff 0xfffffffffcf1f1ff

def z93 : W := mkw 0xc7eefffde0003781 0x71fbbfff78000de0 0xdffffffff0003fc3 0xb7fffffffc000ff0

def z94 : W := mkw 0x43aa03f000003780 0x50ea80fc00000de0 0x5bff03f000003fc3 0x96ffc0fc00000ff0

def z95 : W := mkw 0x0030012014805150 0x000c004805201454 0xfef00f307cc1f9f3 0xffbc03cc1f307e7c

def z96 : W := mkw 0x4bbb03f20fc83fa0 0x52eec0fc83f20fe8 0xffffc3fe0ff83ff3 0xfffff0ff83fe0ffc

def z97 : W := mkw 0x0460492440000000 0x0118124910000000 0xcef0cf3e70000003 0xb3bc33cf9c000000

def z98 : W := mkw 0xd7fefffff4995971 0x35ffbffffd26565c 0xfffffffffcf9f9f3 0xffffffffff3e7e7c

def z99 : W := mkw 0xc4ee5d74e0000001 0x313b975d38000000 0xceffcf3e70000003 0xb3bff3cf9c000000

def z100 : W := mkw 0x1440480650194870 0x051012019406521c 0xa400cc0e7039c030 0x290033039c0e700c

def z101 : W := mkw 0x10171452b5dbdbf4 0x0405c514ad76f6fd 0xf50f3cf1fffffffe 0xfd43cf3c7fffffff

def z102 : W := mkw 0x1470492654995970 0x051c12499526565c 0xacf0cc3e70f9c1f0 0xab3c330f9c3e707c

def z103 : W := mkw 0x9474fd2654bfd970 0xa51d3f49952ff65c 0xfef0ff3e7cfff9f3 0xffbc3fcf9f3ffe7c

def z104 : W := mkw 0x4bbb03f00fc00000 0x12eec0fc03f00000 0x4bff03f00fc00003 0xd2ffc0fc03f00000

def z105 : W := mkw 0x88dd5c0005d38000 0xa23757000174e000 0xaaffcc000cf9c003 0xeabff300033e7000

def z106 : W := mkw 0x6bbba3fb0fec3fa8 0x5aeee8fec3fb0fea 0xfffff3ff8ffe3fff 0xfffffcffe3ff8fff

def z107 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z108 : W := mkw 0x4bbb03f005c01380 0x52eec0fc017004e0 0x4bff03f000c001c3 0x92ffc0fc00300070

def z109 : W := mkw 0x00555c0005d38000 0x001557000174e000 0xabfffc000fffc003 0xeaffff0003fff000

def z110 : W := mkw 0x14775d76f5dbdbf4 0x051dd75dbd76f6fd 0xfeffcf3e7cf9f9f3 0xffbff3cf9f3e7e7c

def z111 : W := mkw 0xc7ecffade0000001 0x31fb3feb78000000 0x8ef0ff0ff0000001 0x23bc3fc3fc000000

def z112 : W := mkw 0x1470492644991920 0x051c124991264648 0xaaf0cf0e0cf9f803 0xeabc33c3833e7e00

def z113 : W := mkw 0x1010000214995970 0x040400008526565c 0x300000000cf9f9f0 0x4c000000033e7e7c

def z114 : W := mkw 0xcffffffdefc03781 0x73ffffff7bf00de0 0xdfffffffffc03fc3 0xf7fffffffff00ff0

def z115 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0x540f0cf1f0c1c7fc 0x9503c33c7c3071ff

def z116 : W := mkw 0x1460492650085970 0x051812499402165c 0xdef0cf3e700039f3 0xb7bc33cf9c000e7c

def z117 : W := mkw 0x0000a00000240000 0x0000280000090000 0xa000f000003e0000 0x28003c00000f8000

def z118 : W := mkw 0x4bbf17f0afc2b784 0x52efc5fc2bf0ade1 0x5bff33f18fc63fcf 0xd6ffccfc63f18ff3

def z119 : W := mkw 0x0070492004911100 0x001c124801244440 0xfaf0cf300cf9f9c3 0xfebc33cc033e7e70

def z120 : W := mkw 0x0000000210084870 0x000000008402121c 0xf600cf3e7cf9f9f3 0xfd8033cf9f3e7e7c

def z121 : W := mkw 0x00041400b002c054 0x000105002c00b015 0xa4003c01f007c03c 0x29000f007c01f00f

def z122 : W := mkw 0x4bb803a00e803500 0x52ee00e803a00d40 0x0af003000c003801 0x02bc00c003000e00

def z123 : W := mkw 0x4bba03f00e803780 0x52ee80fc03a00de0 0x5af003f00c003fc1 0x16bc00fc03000ff0

def z124 : W := mkw 0x00071450a1428284 0x0001c5142850a0a1 0xc50f3cf1f306060e 0xb143cf3c7cc18183

def z125 : W := mkw 0x8444fc0df002c055 0x21113f037c00b015 0xa400fc0ff007c03c 0x29003f03fc01f00f

def z126 : W := mkw 0x48bb01700fc03780 0x522ec05c03f00de0 0x18ff00300fc03fc0 0xc63fc00c03f00ff0

def z127 : W := mkw 0xcff8ebad4e803501 0x73fe3aeb53a00d40 0x0af0c30e0c003801 0x02bc30c383000e00

def z128 : W := mkw 0x8bdffc50aff78284 0xa2f7ff142bfde0a1 0xabfffcc18fffc60f 0xeaffff3063fff183

def z129 : W := mkw 0x4bbf17f0bfc2f7d4 0x52efc5fc2ff0bdf5 0x5bff0ff07fc1ffc3 0xd6ffc3fc1ff07ff0

def z130 : W := mkw 0x88dd5c0005d38000 0xa23757000174e000 0x08ff0c0000c1c000 0x823fc30000307000

def z131 : W := mkw 0x8bd8e8000eb50000 0xa2f63a0003ad4000 0x0af0c0000c380001 0x02bc3000030e0000

def z132 : W := mkw 0x4bbb03f00ff7b780 0xd2eec0fc03fdede0 0x7bff03f00fffffc3 0xdeffc0fc03fffff0

def z133 : W := mkw 0x1470492654995970 0x051c12499526565c 0xfff0ffffffffffff 0xfffc3fffffffffff

def z134 : W := mkw 0xc4e8492440000001 0x313a124910000000 0x08f0000000000000 0x023c000000000000

def z135 : W := mkw 0x9ff8e9264ebd1920 0xa7fe3a4993af4648 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z136 : W := mkw 0x14445c06f01bc874 0x05111701bc06f21d 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z137 : W := mkw 0x030002800a002400 0x00c000a002800900 0x530003c00f003e03 0x54c000f003c00f80

def z138 : W := mkw 0x2000a00b002c0828 0x08002802c00b020a 0xa400f00f803e003c 0x29003c03e00f800f

def z139 : W := mkw 0xcbff5ff00fd3b780 0xf2ffd7fc03f4ede0 0x5bff0ff00fc1ffc3 0xd6ffc3fc03f07ff0

def z140 : W := mkw 0xcffffd74eff78001 0xb3ffff5d3bfde000 0xabfffc307fffc003 0xeaffff0c1ffff000

def z141 : W := mkw 0xc7eaebfde0000001 0x31fabaff78000000 0x4ef0c3fff0000001 0x13bc30fffc000000

def z142 : W := mkw 0x00041400b002c054 0x000105002c00b015 0x00000c007001c000 0x000003001c007000

def z143 : W := mkw 0x7ffbebff5ffd7ff8 0x5ffefaffd7ff5ffe 0xffffffffffffffff 0xffffffffffffffff

def z144 : W := mkw 0x400202d9a0000001 0x100080b668000000 0x000000c180000000 0x0000003060000000

def z145 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0xa50f3cc1f307c63c 0x2943cf307cc1f18f

def z146 : W := mkw 0x0050480004910000 0x0014120001244000 0xaaf0cc000cf9c003 0xeabc3300033e7000

def z147 : W := mkw 0x43aaa3f900000000 0x10eaa8fe40000000 0xcffff3ff80000003 0xb3fffcffe0000000

def z148 : W := mkw 0x8b8db4000b668000 0xa2e36d0002d9a000 0xa10f3c0003c7c002 0xe843cf0000f1f000

def z149 : W := mkw 0xcffbebfd4fc03781 0x73fefaff53f00de0 0x5bffc3fe0fc03fc3 0xd6fff0ff83f00ff0

def z150 : W := mkw 0x542203f650087ff0 0x550880fd94021ffc 0x540003fe70003ff0 0x150000ff9c000ffc

def z151 : W := mkw 0x400202d000002680 0x500080b4000009a0 0x000000c000000600 0x0000003000000180

def z152 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0x550f30f1f30607fc 0x1543cc3c7cc181ff

def z153 : W := mkw 0x9ffdfd265fffd970 0xa7ff7f4997fff65c 0xffffff3e7ffff9f3 0xffffffcf9ffffe7c

def z154 : W := mkw 0x87ecfd2440000000 0x21fb3f4910000000 0xcfffff3e70000003 0xb3ffffcf9c000000

def z155 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0x310030c18f3e3e3c 0x4c400c3063cf8f8f

def z156 : W := mkw 0x00020050b00042d4 0x000080142c0010b5 0x540000f1f00007fc 0x1500003c7c0001ff

def z157 : W := mkw 0x1420012650085970 0x050800499402165c 0xf4000f3e70c1f9f2 0xfd0003cf9c307e7c

def z158 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0x09ff3cf1f0000000 0x827fcf3c7c000000

def z159 : W := mkw 0x43aa03f000000000 0x10ea80fc00000000 0x4bff03f000000003 0x92ffc0fc00000000

def z160 : W := mkw 0xc7eefffdf0004051 0x31fbbfff7c001014 0xfffffffff0c1c1f3 0xfffffffffc30707c

def z161 : W := mkw 0xc7e8ebad40000001 0x31fa3aeb50000000 0xcef0cf3e70000003 0xb3bc33cf9c000000

def z162 : W := mkw 0x0300a0000a240000 0x00c0280002890000 0x0100300003060000 0x00400c0000c18000

def z163 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0x0bfff3cf80000001 0x02fffcf3e0000000

def z164 : W := mkw 0xc7e8ebad40000001 0x31fa3aeb50000000 0x0af0c30e00000001 0x02bc30c380000000

def z165 : W := mkw 0x9cfd5d2455d3d150 0xa73f57491574f454 0x08ff0c3070c1c1c0 0x823fc30c1c307070

def z166 : W := mkw 0x0000000000000000 0x0000000000000000 0x520003000c003803 0x548000c003000e00

def z167 : W := mkw 0x5ff84ba64e993d20 0x57fe12e993a64f48 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z168 : W := mkw 0x8b9db4000fe68000 0xa2e76d0003f9a000 0x0bff30000fc60003 0xc2ffcc0003f18000

def z169 : W := mkw 0x281100020fec3fa8 0x4a04400083fb0fea 0x300000000ffe3ffc 0x4c00000003ff8fff

def z170 : W := mkw 0x081100000ff7b780 0xc204400003fdede0 0x300000000fffffc0 0x4c00000003fffff0

def z171 : W := mkw 0x0000000010004050 0x0000000004001014 0xf4000c3070c1c1f2 0xfd00030c1c30707c

def z172 : W := mkw 0x1470492644991920 0x051c124991264648 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z173 : W := mkw 0x0030012004801100 0x000c004801200440 0x0af003000c003801 0x02bc00c003000e00

def z174 : W := mkw 0x4bb903a00fc03780 0x52ee40e803f00de0 0x1af003000fc03fc1 0x46bc00c003f00ff0

def z175 : W := mkw 0x0470492444801100 0x011c124911200440 0xdef0cf3e7cc039c3 0xf7bc33cf9f300e70

def z176 : W := mkw 0x8447fc5df142c2d5 0x2111ff177c50b0b5 0xf50ffcfff3c7c7fe 0xfd43ff3ffcf1f1ff

def z177 : W := mkw 0x2304b68bba2eec7c 0x08c12da2ee8bbb1f 0xf700ffcfff3ffe3f 0x7dc03ff3ffcfff8f

def z178 : W := mkw 0xcffffffdeff78001 0xb3ffffff7bfde000 0xefffffffffffc003 0xfbfffffffffff000

def z179 : W := mkw 0x0001000001400000 0x0000400000500000 0x010f000003c00002 0xc043c00000f00000

def z180 : W := mkw 0x0005140001428000 0x000145000050a000 0xa10f3c0003c7c002 0xe843cf0000f1f000

def z181 : W := mkw 0x8bdffc50bff7c2d4 0xa2f7ff142ffdf0b5 0xfffffcf1ffffc7ff 0xffffff3c7ffff1ff

def z182 : W := mkw 0x000100001142c2d4 0x000040000450b0b5 0x3000000003c7c7fc 0x4c00000000f1f1ff

def z183 : W := mkw 0x00071450a1428284 0x0001c5142850a0a1 0x510f30f183c607ce 0xd443cc3c60f181f3

def z184 : W := mkw 0x9444fc06503fc870 0xa5113f01940ff21c 0xa400fc0e703fc030 0x29003f039c0ff00c

def z185 : W := mkw 0x83ccfc000a240000 0x20f33f0002890000 0xabfffc000f3e0003 0xeaffff0003cf8000

def z186 : W := mkw 0xc3eefff000000000 0x30fbbffc00000000 0xcbfffff000000003 0xb2fffffc00000000

def z187 : W := mkw 0xc7ecffad40000001 0x31fb3feb50000000 0x8bffff0e00000003 0xa2ffffc380000000

def z188 : W := mkw 0x4b8b02d00b402680 0x52e2c0b402d009a0 0x010f00c003000600 0x0043c03000c00180

def z189 : W := mkw 0x2300028b0a082c28 0x08c000a2c2820b0a 0x570003cf8f003e3f 0x55c000f3e3c00f8f

def z190 : W := mkw 0x8bdffc50bff7c2d4 0xa2f7ff142ffdf0b5 0xabfffc307fffc1c3 0xeaffff0c1ffff070

def z191 : W := mkw 0x34704baf54997d78 0x0d1c12ebd5265f5e 0xfef0cffffcf9ffff 0xffbc33ffff3e7fff

def z192 : W := mkw 0x1770ebaf54995970 0x05dc3aebd526565c 0xfff0fffffcf9f9f3 0xfffc3fffff3e7e7c

def z193 : W := mkw 0x0460492450004050 0x0118124914001014 0xfef0cf3e70c1c1f3 0xffbc33cf9c30707c

def z194 : W := mkw 0x8004b40000268000 0xa0012d000009a000 0x0000300000060000 0x00000c0000018000

def z195 : W := mkw 0x4bbba3f90fc03780 0x52eee8fe43f00de0 0xdffff3ff8fc03fc3 0xf7fffcffe3f00ff0

def z196 : W := mkw 0x00061450a0000000 0x0001851428000000 0x000f0c3070000000 0x8003c30c1c000000

def z197 : W := mkw 0x47ea4bf440000000 0x11fa92fd10000000 0xcfffcffe70000003 0xb3fff3ff9c000000

def z198 : W := mkw 0x14475c56f15bcaf4 0x0511d715bc56f2bd 0xf50ffcfff3ffc7fe 0xfd43ff3ffcfff1ff

def z199 : W := mkw 0x00071450a1428284 0x0001c5142850a0a1 0x000f000000000000 0x0003c00000000000

def z200 : W := mkw 0x000514001142c050 0x000145000450b014 0xf50f3c3073c7c1f2 0xfd43cf0c1cf1f07c

def z201 : W := mkw 0x43ba03f004801100 0x10ee80fc01200440 0x5bff03f00cc039c3 0xd6ffc0fc03300e70

def z202 : W := mkw 0x9444fc0ff0194871 0x25113f03fc06521c 0xa400fc0ff039c030 0x29003f03fc0e700c

def z203 : W := mkw 0x4bbf17f0bfc2f7d4 0x52efc5fc2ff0bdf5 0xffff3ff1ffc7ffff 0xffffcffc7ff1ffff

def z204 : W := mkw 0x48bf1570b5c2d3d4 0x522fc55c2d70b4f5 0x08ff0c3070c1c1c0 0x823fc30c1c307070

def z205 : W := mkw 0x0004140000000000 0x0001050000000000 0x810f3c0000000002 0xa043cf0000000000

def z206 : W := mkw 0x1010000214995970 0x040400008526565c 0xf4000c307cf9f9f2 0xfd00030c1f3e7e7c

def z207 : W := mkw 0x5fbb03f65fc87ff0 0x57eec0fd97f21ffc 0x5fff03fe7fc03ff3 0xd7ffc0ff9ff00ffc

def z208 : W := mkw 0xc4ee5d74e0000001 0x313b975d38000000 0x08ff0c3070000000 0x823fc30c1c000000

def z209 : W := mkw 0x57fa4bf654995970 0x15fe92fd9526565c 0xffffcffe7cf9f9f3 0xfffff3ff9f3e7e7c

def z210 : W := mkw 0x0030012004801100 0x000c004801200440 0x5af003300cc039c3 0xd6bc00cc03300e70

def z211 : W := mkw 0xab8db6890b66a408 0xaae36da242d9a902 0x010f30c18306060c 0x0043cc3060c18183

def z212 : W := mkw 0x0003005001400280 0x0000c014005000a0 0x510f00f003c007c2 0xd443c03c00f001f0

def z213 : W := mkw 0x8bddfc001ff7c050 0xa2f77f0007fdf014 0xfffffc307fffc1f3 0xffffff0c1ffff07c

def z214 : W := mkw 0x1470492454915150 0x051c124915245454 0x08f00c3070c1c1c0 0x823c030c1c307070

def z215 : W := mkw 0x2004b40bb02ec87c 0x08012d02ec0bb21f 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z216 : W := mkw 0x2300a28b1a2c6c78 0x08c028a2c68b1b1e 0xf700ffffffffffff 0xfdc03fffffffffff

def z217 : W := mkw 0x5ffb4bf64fd93fa0 0x57fed2fd93f64fe8 0x5bffc3fe0ff83fc3 0xd6fff0ff83fe0ff0

def z218 : W := mkw 0xc7eaebfd40000001 0x31fabaff50000000 0x4bffc3fe00000003 0x92fff0ff80000000

def z219 : W := mkw 0x00041400b002c054 0x000105002c00b015 0xf4003c31f0c7c1fe 0xfd000f0c7c31f07f

def z220 : W := mkw 0xc4ee5ffde0000001 0x313b97ff78000000 0x4cff0ffff0000000 0x933fc3fffc000000

def z221 : W := mkw 0xc466fffde0000001 0x3119bfff78000000 0xc400fffff0000000 0x31003ffffc000000

def z222 : W := mkw 0x8444fc0de0378001 0xa1113f03780de000 0xa400fc0ff03fc000 0x29003f03fc0ff000

def z223 : W := mkw 0x9474fd2ff4995971 0x251d3f4bfd26565c 0xfef0ff3ffcf9f9f3 0xffbc3fcfff3e7e7c

def z224 : W := mkw 0x0000000200080820 0x0000000080020208 0x5400030e00003830 0x150000c380000e0c

def z225 : W := mkw 0xcbbfb7f00fe6b780 0xf2efedfc03f9ade0 0x5bff33f00fc63fc3 0xd6ffccfc03f18ff0

def z226 : W := mkw 0xcb8fb6d9ab402681 0x72e3edb66ad009a0 0x010f30c183000600 0x0043cc3060c00180

def z227 : W := mkw 0x4bb803a00e803500 0x52ee00e803a00d40 0x5bf003c00f003e03 0x56fc00f003c00f80

def z228 : W := mkw 0xdfffffffffffd971 0xb7fffffffffff65c 0xfffffffffffff9f3 0xfffffffffffffe7c

def z229 : W := mkw 0x0001000001400280 0x00004000005000a0 0x1000000003c007c0 0x4400000000f001f0

def z230 : W := mkw 0x8bddfc000ff7b780 0xe2f77f0003fdede0 0xbbfffc000fffffc3 0xeeffff0003fffff0

def z231 : W := mkw 0x1420012640081920 0x0508004990020648 0x0000030e00003800 0x000000c380000e00

def z232 : W := mkw 0x0050480014914050 0x0014120005245014 0xfef0cc307cf9c1f3 0xffbc330c1f3e707c

def z233 : W := mkw 0xc7eefffdea002401 0x31fbbfff7a800900 0xdfffffffff003e03 0xf7ffffffffc00f80

def z234 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0x0aff03300cc039c1 0x82bfc0cc03300e70

def z235 : W := mkw 0x48b8012004801100 0x522e004801200440 0x08f0000000000000 0x023c000000000000

def z236 : W := mkw 0xcffffffde5c01381 0x73ffffff797004e0 0xcffffffff0c001c3 0xb3fffffffc300070

def z237 : W := mkw 0x8bd9e8000ff50000 0xa2f67a0003fd4000 0x0bffc0000ff80003 0xc2fff00003fe0000

def z238 : W := mkw 0x00071450a1428284 0x0001c5142850a0a1 0x010f30c18306060c 0x0043cc3060c18183

def z239 : W := mkw 0xc4eefd7de0000001 0x313bbf5f78000000 0x8cfffc3ff0000000 0xa33fff0ffc000000

def z240 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0x510f0cf073c1c7c2 0xd443c33c1cf071f0

def z241 : W := mkw 0x00020050b00042d4 0x000080142c0010b5 0x00000030700001c0 0x0000000c1c000070

def z242 : W := mkw 0x0300a28900000000 0x00c028a240000000 0x0200c30e00000001 0x008030c380000000

def z243 : W := mkw 0x8b8db4000b668000 0xa2e36d0002d9a000 0xa30ff0000f3e0003 0x68c3fc0003cf8000

def z244 : W := mkw 0x0033017005c01380 0x000cc05c017004e0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z245 : W := mkw 0x4b8b02d00b402680 0x52e2c0b402d009a0 0x510f00f003c007c2 0xd443c03c00f001f0

def z246 : W := mkw 0x8040e80000350000 0xa0103a00000d4000 0x0000c00000380000 0x00003000000e0000

def z247 : W := mkw 0x0030012204881920 0x000c004881220648 0xfef0c33e0cf839f3 0xffbc30cf833e0e7c

def z248 : W := mkw 0x0460492440000000 0x0118124910000000 0x0af0c30e00000001 0x02bc30c380000000

def z249 : W := mkw 0x0b9d14000fc28000 0x02e7450003f0a000 0xabff3c000fc7c003 0xeaffcf0003f1f000

def z250 : W := mkw 0x00061450a0000000 0x0001851428000000 0xc50f3cf1f0000002 0xb143cf3c7c000000

def z251 : W := mkw 0x301000021ebd7d78 0x0c04000087af5f5e 0x300000000ffffffc 0x4c00000003ffffff

def z252 : W := mkw 0xc38fb6d9b142c2d5 0x30e3edb66c50b0b5 0xf50f3cf1f3c7c7fe 0xfd43cf3c7cf1f1ff

def z253 : W := mkw 0x8446fc5de0000001 0x2111bf1778000000 0xc50ffcfff0000002 0xb143ff3ffc000000

def z254 : W := mkw 0x6bbba3f90fe43788 0x5aeee8fe43f90de2 0x5bff33f18fc63fcf 0xd6ffccfc63f18ff3

def z255 : W := mkw 0x542203fff0085971 0x150880fffc02165c 0x540003fff00039f0 0x150000fffc000e7c

def z256 : W := mkw 0xabd8ea8b0ebd2c28 0xaaf63aa2c3af4b0a 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z257 : W := mkw 0x1010000204991920 0x0404000081264648 0x000000000c383800 0x00000000030e0e00

def z258 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0x0affcc000cf9c001 0x82bff300033e7000

def z259 : W := mkw 0x181100021fffd970 0x8604400087fff65c 0x300000000ffff9f0 0x4c00000003fffe7c

def z260 : W := mkw 0x0b9900000ff78000 0x82e6400003fde000 0x2bff00000fffc003 0xcaffc00003fff000

def z261 : W := mkw 0x2000028b0a2c2c28 0x080000a2c28b0b0a 0x740003cf8f3e3e3c 0x5d0000f3e3cf8f8f

def z262 : W := mkw 0x00041400a0000000 0x0001050028000000 0x84003c01f0000000 0x21000f007c000000

def z263 : W := mkw 0x181100021fd97ff0 0x4604400087f65ffc 0x300000000ff9fff0 0x4c00000003fe7ffc

def z264 : W := mkw 0x3777fffffffffffc 0x0dddffffffffffff 0xffffffffffffffff 0xffffffffffffffff

def z265 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0x5300c3ce0f383e03 0x54c030f383ce0f80

def z266 : W := mkw 0x1440480650194870 0x051012019406521c 0xf400cc3e70f9c1f2 0xfd00330f9c3e707c

def z267 : W := mkw 0x00071452b14acaf4 0x0001c514ac52b2bd 0xf70fffffffffffff 0xfdc3ffffffffffff

def z268 : W := mkw 0x1000000210194870 0x040000008406521c 0x200000000039c030 0x08000000000e700c

def z269 : W := mkw 0x44624bfde0000001 0x111892ff78000000 0xcef0cffff0000003 0xb3bc33fffc000000

def z270 : W := mkw 0x0b9900000fc03780 0x42e6400003f00de0 0x1bff00000fc03fc3 0xc6ffc00003f00ff0

def z271 : W := mkw 0x0306b6d9a0000000 0x00c1adb668000000 0xc70ffffff0000003 0xb1c3fffffc000000

def z272 : W := mkw 0xc7effffdf142c2d5 0x31fbffff7c50b0b5 0xfffffffff3c7c7ff 0xfffffffffcf1f1ff

def z273 : W := mkw 0x0000a00900000000 0x0000280240000000 0x8400f00f80000000 0x21003c03e0000000

def z274 : W := mkw 0x44220174e0000001 0x1108805d38000000 0x0000003070000000 0x0000000c1c000000

def z275 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0xffff33f18fc63fff 0xffffccfc63f18fff

def z276 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0xfffffcc18fffc63f 0xffffff3063fff18f

def z277 : W := mkw 0xabd8ea8b0ebd2c28 0xaaf63aa2c3af4b0a 0xfff0f3cf8f3e3e3f 0x7ffc3cf3e3cf8f8f

def z278 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0xf600c30e0c383833 0x7d8030c3830e0e0c

def z279 : W := mkw 0x8bddfc001ff7c2d4 0xa2f77f0007fdf0b5 0xbbfffc000fffc7ff 0xeeffff0003fff1ff

def z280 : W := mkw 0xd7eefffff0085971 0x35fbbffffc02165c 0xdffffffff00039f3 0xb7fffffffc000e7c

def z281 : W := mkw 0x200100021b6eeefc 0x0800400086dbbbbf 0x300000000ffffffc 0x4c00000003ffffff

def z282 : W := mkw 0xbffdffaf5ffffd78 0xafff7febd7ffff5e 0xffffffffffffffff 0xffffffffffffffff

def z283 : W := mkw 0xc8ff5d7005d39380 0xf23fd75c0174e4e0 0x08ff0c3000c1c1c0 0x823fc30c00307070

def z284 : W := mkw 0x1470492654995970 0x051c12499526565c 0x5ef0c33e7c3839f1 0x17bc30cf9f0e0e7c

def z285 : W := mkw 0x0300a00000000000 0x00c0280000000000 0x8300f00000000003 0x20c03c0000000000

def z286 : W := mkw 0x8054fc0004b78000 0xa0153f00012de000 0xaaf0fc000cffc003 0xeabc3f00033ff000

def z287 : W := mkw 0xd4fe5d74f4915151 0x353f975d3d245454 0x08ff0c3070c1c1c0 0x823fc30c1c307070

def z288 : W := mkw 0x083101200fc03780 0x420c404803f00de0 0x5af003300fc03fc3 0xd6bc00cc03f00ff0

def z289 : W := mkw 0x1470492454915150 0x051c124915245454 0x5af00f307cc1f9c3 0xd6bc03cc1f307e70

def z290 : W := mkw 0x2b11a28b0fec3fa8 0x4ac468a2c3fb0fea 0xf700f3cf8ffe3fff 0x7dc03cf3e3ff8fff

def z291 : W := mkw 0x4bb803a00e803500 0x52ee00e803a00d40 0x5af003300cc039c3 0xd6bc00cc03300e70

def z292 : W := mkw 0x3770ebaf4ebd3d28 0x0ddc3aebd3af4f4a 0xfff0f3cf8f3e3e3f 0x7ffc3cf3e3cf8f8f

def z293 : W := mkw 0xc38fb6d9a1428285 0x30e3edb66850a0a1 0x010f30c18306060c 0x0043cc3060c18183

def z294 : W := mkw 0x88ddfc0005f78000 0xa2377f00017de000 0xa8fffc0000ffc000 0xaa3fff00003ff000

def z295 : W := mkw 0x402203f000000000 0x100880fc00000000 0x400003f000000000 0x100000fc00000000

def z296 : W := mkw 0x0030012004801100 0x000c004801200440 0x08f0003000c001c0 0x823c000c00300070

def z297 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0xf40f0c3070c1c1f2 0xfd03c30c1c30707c

def z298 : W := mkw 0xefffffffefec3fa9 0x7bfffffffbfb0fea 0xfffffffffffe3fff 0xffffffffffff8fff

def z299 : W := mkw 0x442717fdf142c2d5 0x1109c5ff7c50b0b5 0xf50f3ffff3c7c7fe 0xfd43cffffcf1f1ff

def z300 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0x5600c3cf8c383e3d 0x158030f3e30e0f8f

def z301 : W := mkw 0x43ab03f001400280 0x10eac0fc005000a0 0x5bff03f003c007c3 0xd6ffc0fc00f001f0

def z302 : W := mkw 0x0b1102800fc03780 0x42c440a003f00de0 0x530003c00fc03fc3 0x54c000f003f00ff0

def z303 : W := mkw 0x0040480000000000 0x0010120000000000 0x8af0cc0000000003 0xa2bc330000000000

def z304 : W := mkw 0x000100001142c2d4 0x000040000450b0b5 0xf4000c3073c7c7fe 0xfd00030c1cf1f1ff

def z305 : W := mkw 0x14745d26f49bd974 0x051d1749bd26f65d 0xfef0ff3ffcfff9ff 0xffbc3fcfff3ffe7f

def z306 : W := mkw 0x00020050b00042d4 0x000080142c0010b5 0xf50030f1f30607fe 0x7d400c3c7cc181ff

def z307 : W := mkw 0x0b9902800fc02400 0x02e640a003f00900 0x5bff03c00fc03e03 0xd6ffc0f003f00f80

def z308 : W := mkw 0x4fbb03fdefc03781 0x53eec0ff7bf00de0 0x5fff03ffffc03fc3 0xd7ffc0fffff00ff0

def z309 : W := mkw 0xa3ccfe8b0a2c2c28 0x28f33fa2c28b0b0a 0xffffffcf8f3e3e3f 0xfffffff3e3cf8f8f

def z310 : W := mkw 0xcffefffdeeb50001 0xb3ffbfff7bad4000 0xcffffffffc380003 0xb3ffffffff0e0000

def z311 : W := mkw 0x0010000004910000 0x0004000001244000 0x200000000cf9c000 0x48000000033e7000

def z312 : W := mkw 0x442203fde0003781 0x510880ff78000de0 0x540003fff0003fc0 0x150000fffc000ff0

def z313 : W := mkw 0xd7fffffff5dbdbf5 0x35fffffffd76f6fd 0xffffffffffffffff 0xffffffffffffffff

def z314 : W := mkw 0x2000a00900240008 0x0800280240090002 0x000030018006000c 0x00000c0060018003

def z315 : W := mkw 0xc7effffde1428001 0x31fbffff7850a000 0xeffffffff3c7c003 0xfbfffffffcf1f000

def z316 : W := mkw 0x8344fc000a378000 0xa0d13f00028de000 0xa300fc000f3fc003 0x68c03f0003cff000

def z317 : W := mkw 0x87ccfc0de0000001 0x21f33f0378000000 0x8ffffc0ff0000003 0xa3ffff03fc000000

def z318 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0xa40f3c31f0c7c1fc 0xa903cf0c7c31f07f

def z319 : W := mkw 0x1470492654995970 0x051c12499526565c 0x38f00c307cf9f9f0 0xce3c030c1f3e7e7c

def z320 : W := mkw 0x1430012654995970 0x050c00499526565c 0x7400033e7cf9f9f0 0x5d0000cf9f3e7e7c

def z321 : W := mkw 0x1440480640190820 0x0510120190064208 0x0000c00e00380000 0x00003003800e0000

def z322 : W := mkw 0x1770e9265ebd5970 0x05dc3a4997af565c 0xfff0ff3e7ffff9f3 0xfffc3fcf9ffffe7c

def z323 : W := mkw 0x200000020a2c2c28 0x08000000828b0b0a 0x300000000f3e3e3c 0x4c00000003cf8f8f

def z324 : W := mkw 0x0000000000003780 0x4000000000000de0 0x1000000000003fc0 0x0400000000000ff0

def z325 : W := mkw 0xe7eeffffea2c2c29 0x39fbbffffa8b0b0a 0xcffffffffc383803 0xb3ffffffff0e0e00

def z326 : W := mkw 0xc4ee5d74e0000001 0x313b975d38000000 0xcdff3cf1f0000002 0xb37fcf3c7c000000

def z327 : W := mkw 0x00575c50b5d3c2d4 0x0015d7142d74f0b5 0xfffffcf1ffffc7ff 0xffffff3c7ffff1ff

def z328 : W := mkw 0x1440480650194870 0x051012019406521c 0xf600cf0e7c39f833 0x7d8033c39f0e7e0c

def z329 : W := mkw 0xa444fc0fe02c0829 0x29113f03f80b020a 0xa400fc0ff03e003c 0x29003f03fc0f800f

def z330 : W := mkw 0x0002005000000280 0x00008014000000a0 0x500000f0000007c0 0x1400003c000001f0

def z331 : W := mkw 0x00000000100042d4 0x00000000040010b5 0x10000000000007fc 0x04000000000001ff

def z332 : W := mkw 0xcbf8eba00eb53500 0xf2fe3ae803ad4d40 0x0af0c3000c383801 0x02bc30c0030e0e00

def z333 : W := mkw 0xd7eefffff0194871 0x35fbbffffc06521c 0xeffffffff039c033 0xbbfffffffc0e700c

def z334 : W := mkw 0x4b8f16d0bb42e6d4 0x52e3c5b42ed0b9b5 0xf50f3cf1f3c7c7fe 0xfd43cf3c7cf1f1ff

def z335 : W := mkw 0x838cb40000000000 0x20e32d0000000000 0x010f300000000000 0x0043cc0000000000

def z336 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0x300f0c3073c7c7fc 0xcc03c30c1cf1f1ff

def z337 : W := mkw 0x4bbb01700fc01380 0x52eec05c03f004e0 0x0bff00300fc001c3 0xc2ffc00c03f00070

def z338 : W := mkw 0x00071450a1400280 0x0001c514285000a0 0xd50f3cf1f3c007c2 0xf543cf3c7cf001f0

def z339 : W := mkw 0x0b9b00500fc00280 0x02e6c01403f000a0 0x5bff00f00fc007c3 0xd6ffc03c03f001f0

def z340 : W := mkw 0x081514000ff78000 0x8205450003fde000 0xa10f3c000fffc002 0xe843cf0003fff000

def z341 : W := mkw 0xc7cefedde0000001 0x31f3bfb778000000 0x850ffccff0000000 0x2143ff33fc000000

def z342 : W := mkw 0xe7eeffffe02c0829 0x39fbbffff80b020a 0xeffffffff03e003f 0xbbfffffffc0f800f

def z343 : W := mkw 0x030302d00b402680 0x00c0c0b402d009a0 0x530f03f00fc03fc3 0xd4c3c0fc03f00ff0

def z344 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0x09ff3c0003c7c000 0x827fcf0000f1f000

def z345 : W := mkw 0x0000028000002400 0x000000a000000900 0x500003c000003e00 0x140000f000000f80

def z346 : W := mkw 0xcff8ebad4eb50001 0xb3fe3aeb53ad4000 0x0af0c30e0c380001 0x02bc30c3830e0000

def z347 : W := mkw 0x438a02d000000000 0x10e280b400000000 0x010f00c000000000 0x0043c03000000000

def z348 : W := mkw 0x6722a3ffea2c2c29 0x19c8a8fffa8b0b0a 0xf700f3ffff3e3e3f 0x7dc03cffffcf8f8f

def z349 : W := mkw 0xcbfbebf00ff53780 0xf2fefafc03fd4de0 0x5bffc3f00ff83fc3 0xd6fff0fc03fe0ff0

def z350 : W := mkw 0x0305b4000b668000 0x00c16d0002d9a000 0xa30ffc000fffc003 0xe8c3ff0003fff000

def z351 : W := mkw 0x0bd948000fd10000 0x02f6520003f44000 0xabffcc000ff9c003 0xeafff30003fe7000

def z352 : W := mkw 0x00000000b0004054 0x000000002c001015 0x04000001f000003c 0x010000007c00000f

def z353 : W := mkw 0x000000001002c054 0x000000000400b015 0x200000000007c03c 0x080000000001f00f

def z354 : W := mkw 0x00020050a0000000 0x0000801428000000 0x440000f1f0000000 0x1100003c7c000000

def z355 : W := mkw 0x347049265ebd7d78 0x0d1c124997af5f5e 0xfef0cf3e7fffffff 0xffbc33cf9fffffff

def z356 : W := mkw 0x2b11a28b0fffac28 0x8ac468a2c3ffeb0a 0xf700f3cf8ffffe3f 0x7dc03cf3e3ffff8f

def z357 : W := mkw 0x4bbb03f0bfc077d4 0x52eec0fc2ff01df5 0x5fff03f1ffc03fff 0xd7ffc0fc7ff00fff

def z358 : W := mkw 0xe7e8ebaf4a2c2c29 0x39fa3aebd28b0b0a 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z359 : W := mkw 0x1030012214995970 0x040c00488526565c 0x7af003300cf9f9f3 0xdebc00cc033e7e7c

def z360 : W := mkw 0x0000000000000000 0x0000000000000000 0xc50030c180000002 0x31400c3060000000

def z361 : W := mkw 0xc7effffde1400281 0x31fbffff785000a0 0xdffffffff3c007c3 0xf7fffffffcf001f0

def z362 : W := mkw 0x8bfdfd200ff79100 0xa2ff7f4803fde440 0xfbffff300ffff9c3 0xfeffffcc03fffe70

def z363 : W := mkw 0x00051400b142c054 0x000145002c50b015 0xa50f3c01f3c7c03e 0xe943cf007cf1f00f

def z364 : W := mkw 0x83cffc50b142c2d4 0x20f3ff142c50b0b5 0xfffffcf1f3c7c7ff 0xffffff3c7cf1f1ff

def z365 : W := mkw 0x14755d2655dbd970 0x051d57499576f65c 0xffffff3e7ffff9f3 0xffffffcf9ffffe7c

def z366 : W := mkw 0x0300a28900000000 0x00c028a240000000 0xf700f3cf8306063f 0x7dc03cf3e0c1818f

def z367 : W := mkw 0x8464fd2de0000001 0x21193f4b78000000 0xcef0ff3ff0000003 0xb3bc3fcffc000000

def z368 : W := mkw 0x230002820a2c2c28 0x08c000a0828b0b0a 0x730003c00f3e3e3f 0x5cc000f003cf8f8f

def z369 : W := mkw 0x1470492654995970 0x051c12499526565c 0x0af0cf3e7cf9f9c1 0x82bc33cf9f3e7e70

def z370 : W := mkw 0x402303f001403780 0x5008c0fc00500de0 0x510f03f003c03fc2 0xd443c0fc00f00ff0

def z371 : W := mkw 0xcbdffed00ff7a680 0xf2f7ffb403fde9a0 0xabfffcc00fffc603 0xeaffff3003fff180

def z372 : W := mkw 0x2000000b00080828 0x08000002c002020a 0x0400000f8000003c 0x01000003e000000f

def z373 : W := mkw 0x4bbf17f00fc2b780 0x52efc5fc03f0ade0 0xfbff3ff00fc7ffc3 0xfeffcffc03f1fff0

def z374 : W := mkw 0xc7eeffffe0080821 0x31fbbffff8020208 0xfffffffffc383833 0xffffffffff0e0e0c

def z375 : W := mkw 0x3720a3af5a2c7d78 0x0dc828ebd68b1f5e 0xf700f3ffff3e3fff 0x7dc03cffffcf8fff

def z376 : W := mkw 0xe7e8ebaf4a2c2c29 0x39fa3aebd28b0b0a 0xfff0f3cf8f3e3e3f 0x7ffc3cf3e3cf8f8f

def z377 : W := mkw 0xe38eb6d9aa242409 0x38e3adb66a890902 0x010f30c18306060c 0x0043cc3060c18183

def z378 : W := mkw 0x43ae17f0a0000000 0x10eb85fc28000000 0xcfff3ff1f0000003 0xb3ffcffc7c000000

def z379 : W := mkw 0x1440480450114050 0x0510120114045014 0x00000c007001c000 0x000003001c007000

def z380 : W := mkw 0x080100000b402680 0x4200400002d009a0 0x0000000003000600 0x0000000000c00180

def z381 : W := mkw 0x3770ebaf4ebd3d28 0x0ddc3aebd3af4f4a 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z382 : W := mkw 0xc7eefffde0378001 0xb1fbbfff780de000 0xeffffffff03fc003 0xbbfffffffc0ff000

def z383 : W := mkw 0x80cc5c0000000000 0x2033170000000000 0x08ff0c0000000000 0x823fc30000000000

def z384 : W := mkw 0xccff5d74e5d38001 0xb33fd75d3974e000 0x08ff0c3070c1c000 0x823fc30c1c307000

def z385 : W := mkw 0x43af17f0b142c2d4 0x10ebc5fc2c50b0b5 0xffff3ff1f3c7c7ff 0xffffcffc7cf1f1ff

def z386 : W := mkw 0x0000000000000000 0x0000000000000000 0x010030c18306060c 0x00400c3060c18183

def z387 : W := mkw 0xabddfe8b0fffac28 0xaaf77fa2c3ffeb0a 0xabffff0e0ffff803 0xeaffffc383fffe00

def z388 : W := mkw 0x1470492644991920 0x051c124991264648 0xcef0cf3e7c383803 0xb3bc33cf9f0e0e00

def z389 : W := mkw 0x1450480654994870 0x051412019526521c 0xaef0cc0e7cf9c033 0xebbc33039f3e700c

def z390 : W := mkw 0x6322a3fb0a2c3fa8 0x58c8a8fec28b0fea 0xf700f3ff8f3e3fff 0x7dc03cffe3cf8fff

def z391 : W := mkw 0x8bdffc500ff78280 0xa2f7ff1403fde0a0 0xfbfffcf00fffc7c3 0xfeffff3c03fff1f0

def z392 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0x3200c30e0f3e3e3d 0x4c8030c383cf8f8f

def z393 : W := mkw 0x2000028900002408 0x080000a240000902 0x000000c18000060c 0x0000003060000183

def z394 : W := mkw 0x8ffdfd244ff78000 0xa3ff7f4913fde000 0xefffff3e7fffc003 0xfbffffcf9ffff000

def z395 : W := mkw 0x1430012654885970 0x050c00499522165c 0x5ef0033e7cc039f3 0xd7bc00cf9f300e7c

def z396 : W := mkw 0x1ff949265fd95970 0x07fe524997f6565c 0xffffcf3e7ff9f9f3 0xfffff3cf9ffe7e7c

def z397 : W := mkw 0x4bb903a00fc03500 0x52ee40e803f00d40 0x0bff03000fc03803 0xc2ffc0c003f00e00

def z398 : W := mkw 0x9ffdfd245ff7d150 0xa7ff7f4917fdf454 0xabfffc307fffc1c3 0xeaffff0c1ffff070

def z399 : W := mkw 0x8bcdfc000b778000 0xa2f37f0002dde000 0xa10ffc00033fc000 0x2843ff0000cff000

def z400 : W := mkw 0x17704ba65e997d70 0x05dc12e997a65f5c 0xfff0cffe7ff9fff3 0xfffc33ff9ffe7ffc

def z401 : W := mkw 0x84445c04e0000001 0x2111170138000000 0x00000c0070000000 0x000003001c000000

def z402 : W := mkw 0x1460492650194870 0x051812499406521c 0xeef0cf3e7039c033 0xbbbc33cf9c0e700c

def z403 : W := mkw 0x442003ad40000001 0x110800eb50000000 0x0000030e00000000 0x000000c380000000

def z404 : W := mkw 0x0300028000000000 0x00c000a000000000 0x430003c000000003 0x10c000f000000000

def z405 : W := mkw 0x4bbb03f01fc077d0 0x52eec0fc07f01df4 0xffff0ff07fc1fff3 0xffffc3fc1ff07ffc

def z406 : W := mkw 0x1470492644991920 0x051c124991264648 0x5af0c33e0cf839c3 0xd6bc30cf833e0e70

def z407 : W := mkw 0xcbbfb7f9afc03781 0x72efedfe6bf00de0 0x5bff33f18fc03fc3 0xd6ffccfc63f00ff0

def z408 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0x0bfff0000f3e0001 0x02fffc0003cf8000

def z409 : W := mkw 0x14220176f0085bf4 0x0508805dbc0216fd 0x540003fff0003ffc 0x150000fffc000fff

def z410 : W := mkw 0xc7fefffde4801101 0x31ffbfff79200440 0xdffffffffcc039c3 0xf7ffffffff300e70

def z411 : W := mkw 0xc7aeb7fde0000001 0x31ebadff78000000 0x450f33fff0000000 0x1143ccfffc000000

def z412 : W := mkw 0x8bddfc020fff8820 0xa2f77f0083ffe208 0xffffff0e0ffff833 0xffffffc383fffe0c

def z413 : W := mkw 0x83dcfc0004910000 0x20f73f0001244000 0xabfffc000cf9c003 0xeaffff00033e7000

def z414 : W := mkw 0x0811000005d38000 0x820440000174e000 0x0000000000c1c000 0x0000000000307000

def z415 : W := mkw 0x5fff5ff6ffdbfff4 0x57ffd7fdbff6fffd 0xffffffffffffffff 0xffffffffffffffff

def z416 : W := mkw 0x88df5c50b5d3c2d4 0xa237d7142d74f0b5 0x08ff0c3070c1c1c0 0x823fc30c1c307070

def z417 : W := mkw 0x8bdcfc000eb50000 0xa2f73f0003ad4000 0x8bfffc000c380003 0xa2ffff00030e0000

def z418 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0xa10f3c3073c7c1c2 0xe843cf0c1cf1f070

def z419 : W := mkw 0x0001000001428000 0x000040000050a000 0x2000000003c7c000 0x4800000000f1f000

def z420 : W := mkw 0x14765d76f4995970 0x051d975dbd26565c 0xfffffffffcf9f9f3 0xffffffffff3e7e7c

def z421 : W := mkw 0xc08e1450a0000001 0x3023851428000000 0x000f000000000000 0x0003c00000000000

def z422 : W := mkw 0x4bfb4bf00fd13780 0x52fed2fc03f44de0 0xfbffcff00ff9ffc3 0xfefff3fc03fe7ff0

def z423 : W := mkw 0x8b88a0000a240000 0xa2e2280002890000 0x0000000000000000 0x0000000000000000

def z424 : W := mkw 0x0bb901200fc01100 0x02ee404803f00440 0x5bff03300fc039c3 0xd6ffc0cc03f00e70

def z425 : W := mkw 0xe7eeffffe0082c29 0x39fbbffff8020b0a 0xdffffffff0003e3f 0xb7fffffffc000f8f

def z426 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0x0bff03c00f003e01 0x02ffc0f003c00f80

def z427 : W := mkw 0x033003a00e803500 0x00cc00e803a00d40 0x5bf003f00fc03fc3 0xd6fc00fc03f00ff0

def z428 : W := mkw 0x2330a3ab0eac3d28 0x08cc28eac3ab0f4a 0xfff0f3ff8ffe3fff 0xfffc3cffe3ff8fff

def z429 : W := mkw 0x00030050b14042d4 0x0000c0142c5010b5 0x550f00f1f3c007fe 0xd543c03c7cf001ff

def z430 : W := mkw 0x000300501142c2d4 0x0000c0140450b0b5 0x710f00f003c7c7fe 0xdc43c03c00f1f1ff

def z431 : W := mkw 0x081300500fc03780 0x4204c01403f00de0 0x510f00f00fc03fc2 0xd443c03c03f00ff0

def z432 : W := mkw 0x3470e92f54bd5978 0x0d1c3a4bd52f565e 0xfef0ff3ffcfff9ff 0xffbc3fcfff3ffe7f

def z433 : W := mkw 0x0000000000378000 0x80000000000de000 0x20000000003fc000 0x08000000000ff000

def z434 : W := mkw 0x14775d74f5d3d3d4 0x051dd75d3d74f4f5 0x08ff0c3070c1c1c0 0x823fc30c1c307070

def z435 : W := mkw 0x442203fdf00042d5 0x110880ff7c0010b5 0x540003fff00007fc 0x150000fffc0001ff

def z436 : W := mkw 0x8bddfe890ff78000 0xa2f77fa243fde000 0xefffffcf8fffc003 0xfbfffff3e3fff000

def z437 : W := mkw 0x888d140001428000 0xa22345000050a000 0x000f000000000000 0x0003c00000000000

def z438 : W := mkw 0x0004140000028000 0x000105000000a000 0xa0003c000007c000 0x28000f000001f000

def z439 : W := mkw 0xebfffffb0fffbfa8 0xfafffffec3ffefea 0xffffffff8fffffff 0xffffffffe3ffffff

def z440 : W := mkw 0x0b9f1450bfc2c2d4 0x02e7c5142ff0b0b5 0xffff3cf1ffc7c7ff 0xffffcf3c7ff1f1ff

def z441 : W := mkw 0x000000000a002400 0x0000000002800900 0x100000000f003e00 0x4400000003c00f80

def z442 : W := mkw 0xc7eefd74e0000001 0x31fbbf5d38000000 0x8bfffc3070000003 0xa2ffff0c1c000000

def z443 : W := mkw 0x0300a2890a002400 0x00c028a242800900 0xd700f3cf8f003e03 0x75c03cf3e3c00f80

def z444 : W := mkw 0x4b8802800a002400 0x52e200a002800900 0x0000000000000000 0x0000000000000000

def z445 : W := mkw 0x2300a2890a242408 0x08c028a242890902 0xc700f3cf8306060f 0x31c03cf3e0c18183

def z446 : W := mkw 0x030716d0bb42e6d4 0x00c1c5b42ed0b9b5 0xf70f3ff1ffc7ffff 0xfdc3cffc7ff1ffff

def z447 : W := mkw 0x00061450b00042d4 0x000185142c0010b5 0xd50f3cf1f00007fe 0xb543cf3c7c0001ff

def z448 : W := mkw 0x0000000000000000 0x0000000000000000 0x540000c18000063c 0x150000306000018f

def z449 : W := mkw 0x8bddfc000fc00000 0x22f77f0003f00000 0x8bfffc000fc00003 0xe2ffff0003f00000

def z450 : W := mkw 0x1c7149265fd97ff0 0x471c524997f65ffc 0xfef0cf3e7ff9fff3 0xffbc33cf9ffe7ffc

def z451 : W := mkw 0x0470492444910000 0x011c124911244000 0xeef0cf3e7cf9c003 0xfbbc33cf9f3e7000

def z452 : W := mkw 0x0050480004910000 0x0014120001244000 0x0af0c0000c380001 0x02bc3000030e0000

def z453 : W := mkw 0x8bddfc00bff7c054 0xa2f77f002ffdf015 0xaffffc01ffffc03f 0xebffff007ffff00f

def z454 : W := mkw 0x0005140001428000 0x000145000050a000 0xf50f3cc183c7c63e 0xfd43cf3060f1f18f

def z455 : W := mkw 0x0050480204990820 0x0014120081264208 0xfef0cf0e0cf9f833 0xffbc33c3833e7e0c

def z456 : W := mkw 0x2300a28b00082c28 0x08c028a2c0020b0a 0xd700f3cf80003e3f 0x35c03cf3e0000f8f

def z457 : W := mkw 0x88dd5c0005d38000 0xa23757000174e000 0xa9ff3c0003c7c002 0xea7fcf0000f1f000

def z458 : W := mkw 0x402717f0b142f7d4 0x5009c5fc2c50bdf5 0xf50f3ff1f3c7fffe 0xfd43cffc7cf1ffff

def z459 : W := mkw 0x030002820a082c20 0x00c000a082820b08 0xf700c3ce0f383e33 0x7dc030f383ce0f8c

def z460 : W := mkw 0xdfffffffffd97ff1 0x77fffffffff65ffc 0xfffffffffff9fff3 0xfffffffffffe7ffc

def z461 : W := mkw 0x2760ebaf4a2c2c28 0x09d83aebd28b0b0a 0xfff0ffffff3e3e3f 0xfffc3fffffcf8f8f

def z462 : W := mkw 0xcbfffff00ff78000 0xb2fffffc03fde000 0xebfffff00fffc003 0xfafffffc03fff000

def z463 : W := mkw 0x9ffffd76ffffdbf4 0xa7ffff5dbffff6fd 0xffffffffffffffff 0xffffffffffffffff

def z464 : W := mkw 0xc4ef5d74f142c2d5 0x313bd75d3c50b0b5 0xfdff3cf1f3c7c7fe 0xff7fcf3c7cf1f1ff

def z465 : W := mkw 0x8044fc0000000000 0x20113f0000000000 0x8000fc0000000000 0x20003f0000000000

def z466 : W := mkw 0x4bbf17f0afc03780 0x52efc5fc2bf00de0 0xdfff3ff1ffc03fc3 0xf7ffcffc7ff00ff0

def z467 : W := mkw 0x88df5c50b5d3c2d4 0xa237d7142d74f0b5 0xfdff3cf1f3c7c7fe 0xff7fcf3c7cf1f1ff

def z468 : W := mkw 0xcffffffde5d38001 0xb3ffffff7974e000 0xcffffffff0c1c003 0xb3fffffffc307000

def z469 : W := mkw 0x2300a0020a2c2c28 0x08c02800828b0b0a 0xb300f0000f3e3e3f 0x6cc03c0003cf8f8f

def z470 : W := mkw 0x4bab03f00b402680 0x52eac0fc02d009a0 0x4bff03f003000603 0x92ffc0fc00c00180

def z471 : W := mkw 0x2300a00b0a2c0828 0x08c02802c28b020a 0xa700f00f8f3e003f 0x69c03c03e3cf800f

def z472 : W := mkw 0x00061450b002c054 0x000185142c00b015 0xe50f3cf1f007c03e 0xb943cf3c7c01f00f

def z473 : W := mkw 0x000000000a240000 0x0000000002890000 0x200000000f3e0000 0x4800000003cf8000

def z474 : W := mkw 0x0400000de0000001 0x0100000378000000 0x0400000ff0000000 0x01000003fc000000

def z475 : W := mkw 0x0000000200080820 0x0000000080020208 0xa400c00e00380030 0x29003003800e000c

def z476 : W := mkw 0x0003005001400280 0x0000c014005000a0 0x010f00c003000600 0x0043c03000c00180

def z477 : W := mkw 0x6bbfb7fbbfeefffc 0x5aefedfeeffbbfff 0xffffffffffffffff 0xffffffffffffffff

def z478 : W := mkw 0x6b8ba2db0b6c2ea8 0x5ae2e8b6c2db0baa 0xf70ff3cf8f3e3e3f 0x7dc3fcf3e3cf8f8f

def z479 : W := mkw 0xcbfffff00fc03780 0x72fffffc03f00de0 0xdbfffff00fc03fc3 0xf6fffffc03f00ff0

def z480 : W := mkw 0x1400000650084870 0x050000019402121c 0x0400000e70000030 0x010000039c00000c

def z481 : W := mkw 0x0460492640080820 0x0118124990020208 0xfef0cf3e7c383833 0xffbc33cf9f0e0e0c

def z482 : W := mkw 0x8047fc50b177c2d4 0xa011ff142c5df0b5 0xf50ffcf1f3ffc7fe 0xfd43ff3c7cfff1ff

def z483 : W := mkw 0xc7effffdf142c2d5 0x31fbffff7c50b0b5 0xcffffffff0c1c1c3 0xb3fffffffc307070

def z484 : W := mkw 0x54724bf654997ff0 0x551c92fd95265ffc 0xfef0cffe7cf9fff3 0xffbc33ff9f3e7ffc

def z485 : W := mkw 0x4bab03f00b403780 0x52eac0fc02d00de0 0x510f03f003003fc0 0x1443c0fc00c00ff0

def z486 : W := mkw 0x8004b409a0000001 0x20012d0268000000 0x0000300180000000 0x00000c0060000000

def z487 : W := mkw 0xcbdffed9aff78001 0xb2f7ffb66bfde000 0xabfffcc18fffc003 0xeaffff3063fff000

def z488 : W := mkw 0x432203f00a003780 0x50c880fc02800de0 0x530003f00f003fc3 0x54c000fc03c00ff0

def z489 : W := mkw 0x5ffb4bf45fd177d0 0x57fed2fd17f45df4 0x5bff0ff07fc1ffc3 0xd6ffc3fc1ff07ff0

def z490 : W := mkw 0x2300a2890a242408 0x08c028a242890902 0xa300f0c18f3e060f 0x68c03c3063cf8183

def z491 : W := mkw 0x63aaa3fb0a2c2c28 0x18eaa8fec28b0b0a 0xfffff3ff8f3e3e3f 0xfffffcffe3cf8f8f

def z492 : W := mkw 0x030000000a000000 0x00c0000002800000 0x030000000f000003 0x40c0000003c00000

def z493 : W := mkw 0x6b8ba2d90b642688 0x5ae2e8b642d909a2 0x010f30c18306060c 0x0043cc3060c18183

def z494 : W := mkw 0x8bdd5c000fd38000 0xa2f7570003f4e000 0x0bff0c000fc1c003 0xc2ffc30003f07000

def z495 : W := mkw 0x43a803a000000000 0x10ea00e800000000 0x0af0030000000001 0x02bc00c000000000

def z496 : W := mkw 0x4022017000001380 0x5008805c000004e0 0x00000030000001c0 0x0000000c00000070

def z497 : W := mkw 0x0000000010004050 0x0000000004001014 0xa4000c007001c030 0x290003001c00700c

def z498 : W := mkw 0x200000020a2c2c28 0x08000000828b0b0a 0xf50030c18f3e3e3e 0x7d400c3063cf8f8f

def z499 : W := mkw 0x0050480004910000 0x0014120001244000 0x08f00c0000c1c000 0x823c030000307000

def z500 : W := mkw 0x2b99a28b0fec2c28 0x0ae668a2c3fb0b0a 0xfffff3cf8ffe3e3f 0xfffffcf3e3ff8f8f

def z501 : W := mkw 0x2307b6d9ab66a68c 0x08c1edb66ad9a9a3 0x010f30c18306060c 0x0043cc3060c18183

def z502 : W := mkw 0x0000028900000000 0x000000a240000000 0x440003cf80000000 0x110000f3e0000000

def z503 : W := mkw 0xd7f8ebaf54995971 0x35fe3aebd526565c 0xfef0cf3e7cf9f9f3 0xffbc33cf9f3e7e7c

def z504 : W := mkw 0x0007145001428280 0x0001c5140050a0a0 0xf10f3cf003c7c7c2 0xfc43cf3c00f1f1f0

def z505 : W := mkw 0x000514001142c2d4 0x000145000450b0b5 0xb10f3c0003c7c7fe 0xec43cf0000f1f1ff

def z506 : W := mkw 0x030002800a002400 0x00c000a002800900 0x010000c003000600 0x0040003000c00180

def z507 : W := mkw 0x1470492654995970 0x051c12499526565c 0x5cf00f3e70c1f9f0 0x973c03cf9c307e7c

def z508 : W := mkw 0xcb8fb6d00b66a680 0xf2e3edb402d9a9a0 0x010f30c003060600 0x0043cc3000c18180

def z509 : W := mkw 0x80445c0000138000 0xa01117000004e000 0x00000c000001c000 0x0000030000007000

def z510 : W := mkw 0x8bd8e8000eb50000 0xa2f63a0003ad4000 0xabf0f0000f3e0003 0x6afc3c0003cf8000

def z511 : W := mkw 0x8bd9e8000ff78000 0xa2f67a0003fde000 0x2af0c0000fffc001 0x4abc300003fff000

def z512 : W := mkw 0x8bcdfc000b668000 0xa2f37f0002d9a000 0x8bfffc0003060003 0xa2ffff0000c18000

def z513 : W := mkw 0x2000a00b002c0828 0x08002802c00b020a 0xf600f30f8c3e383f 0x7d803cc3e30f8e0f

def z514 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0000c0000c1c002 0xe800030000307000

def z515 : W := mkw 0x8bd8e8000eb50000 0xa2f63a0003ad4000 0xaaf0cc000cf9c003 0xeabc3300033e7000

def z516 : W := mkw 0xcffffffdffc2f7d5 0x73ffffff7ff0bdf5 0xffffffffffc7ffff 0xfffffffffff1ffff

def z517 : W := mkw 0x83cdfc0001428000 0x20f37f000050a000 0xabfffc0003c7c003 0xeaffff0000f1f000

def z518 : W := mkw 0x200000000a242408 0x0800000002890902 0x000000000306060c 0x0000000000c18183

def z519 : W := mkw 0x08171450bfc2f7d4 0x4205c5142ff0bdf5 0xf50f3cf1ffc7fffe 0xfd43cf3c7ff1ffff

def z520 : W := mkw 0xcbfffff0bff7f7d4 0xf2fffffc2ffdfdf5 0xfffffff1ffffffff 0xfffffffc7fffffff

def z521 : W := mkw 0x08171450bff7c2d4 0x8205c5142ffdf0b5 0xf50f3cf1ffffc7fe 0xfd43cf3c7ffff1ff

def z522 : W := mkw 0x200000020a2c2c28 0x08000000828b0b0a 0x000000000c383800 0x00000000030e0e00

def z523 : W := mkw 0x1471492655dbdbf4 0x051c52499576f6fd 0xfef0cf3e7fffffff 0xffbc33cf9fffffff

def z524 : W := mkw 0x43aa03f00a002400 0x10ea80fc02800900 0x5bff03f00f003e03 0xd6ffc0fc03c00f80

def z525 : W := mkw 0x2300a2890a242408 0x08c028a242890902 0xf50030c18306063e 0x7d400c3060c1818f

def z526 : W := mkw 0xc3cefed9a0000001 0x30f3bfb668000000 0x8bfffcc180000003 0xa2ffff3060000000

def z527 : W := mkw 0x3310a28b1ebd7d78 0x0cc428a2c7af5f5e 0xf700f3cf8fffffff 0x7dc03cf3e3ffffff

def z528 : W := mkw 0xefffffffefffac29 0xbbfffffffbffeb0a 0xfffffffffffffe3f 0xffffffffffffff8f

def z529 : W := mkw 0x2000a00b0a2c2c28 0x08002802c28b0b0a 0xb400f00f8f3e3e3c 0x6d003c03e3cf8f8f

def z530 : W := mkw 0x00071450a1428000 0x0001c5142850a000 0xe50f3cf1f3c7c002 0xf943cf3c7cf1f000

def z531 : W := mkw 0x0460492440000000 0x0118124910000000 0x08f00c3070000000 0x823c030c1c000000

def z532 : W := mkw 0x0420012440000000 0x0108004910000000 0x4400033e70000000 0x110000cf9c000000

def z533 : W := mkw 0x0300a28b00080820 0x00c028a2c0020208 0xf700f3cf8c383833 0x7dc03cf3e30e0e0c

def z534 : W := mkw 0x2000000200082c28 0x0800000080020b0a 0x1000000000003e3c 0x0400000000000f8f

def z535 : W := mkw 0x1450480654995970 0x051412019526565c 0xb400cc0e7cf9f9f0 0x6d0033039f3e7e7c

def z536 : W := mkw 0x54724bfff4995971 0x151c92fffd26565c 0xfef0cffffcf9f9f3 0xffbc33ffff3e7e7c

def z537 : W := mkw 0x4bba03f00e803500 0x52ee80fc03a00d40 0x4bff03f00c003803 0x92ffc0fc03000e00

def z538 : W := mkw 0x40aa017000000000 0x102a805c00000000 0x08ff003000000000 0x823fc00c00000000

def z539 : W := mkw 0x0307b450bb66c2d4 0x00c1ed142ed9b0b5 0xf70ffcf1ffffc7ff 0xfdc3ff3c7ffff1ff

def z540 : W := mkw 0x0000000000000000 0x0000000000000000 0x510000c003000602 0x5440003000c00180

def z541 : W := mkw 0x0000000010004050 0x0000000004001014 0x3000000000c1c1f0 0x4c0000000030707c

def z542 : W := mkw 0xcffffffdfff7c2d5 0xb3ffffff7ffdf0b5 0xffffffffffffc7ff 0xfffffffffffff1ff

def z543 : W := mkw 0x48bb03f005c03780 0x522ec0fc01700de0 0x58ff03f000c03fc0 0x963fc0fc00300ff0

def z544 : W := mkw 0xd7fefffdf4915151 0x35ffbfff7d245454 0xcffffffff0c1c1c3 0xb3fffffffc307070

def z545 : W := mkw 0x1c7149265fffd970 0x871c524997fff65c 0xfef0cf3e7ffff9f3 0xffbc33cf9ffffe7c

def z546 : W := mkw 0x2307b6d9bb66e6dc 0x08c1edb66ed9b9b7 0xf50f3cf1f3c7c7fe 0xfd43cf3c7cf1f1ff

def z547 : W := mkw 0x1460492650195970 0x051812499406565c 0xf400cf3e7039f9f0 0x3d0033cf9c0e7e7c

def z548 : W := mkw 0x0388000000000000 0x00e2000000000000 0x0bff000000000003 0x82ffc00000000000

def z549 : W := mkw 0x0760ebad40000000 0x01d83aeb50000000 0xcff0fffff0000003 0xb3fc3ffffc000000

def z550 : W := mkw 0x8b9db4000ff78000 0xa2e76d0003fde000 0x210f30000fffc000 0x4843cc0003fff000

def z551 : W := mkw 0x0005140001428000 0x000145000050a000 0x000f0c0000c1c000 0x8003c30000307000

def z552 : W := mkw 0x4722a3fde0000001 0x11c8a8ff78000000 0xc700f3fff0000003 0x31c03cfffc000000

def z553 : W := mkw 0xabddfc020fffac28 0xaaf77f0083ffeb0a 0xbbfffc000ffffe3f 0xeeffff0003ffff8f

def z554 : W := mkw 0x00061450a0000000 0x0001851428000000 0x010f30c180000000 0x0043cc3060000000

def z555 : W := mkw 0xabdffedbbfffeefc 0xaaf7ffb6effffbbf 0xffffffffffffffff 0xffffffffffffffff

def z556 : W := mkw 0x0010000004800000 0x0004000001200000 0x0af000000cc00003 0xc2bc000003300000

def z557 : W := mkw 0xabddfc0b0fff8828 0xaaf77f02c3ffe20a 0xaffffc0f8fffc03f 0xebffff03e3fff00f

def z558 : W := mkw 0x2300a2890a242408 0x08c028a242890902 0x0000000000000000 0x0000000000000000

def z559 : W := mkw 0x0b9800000e800000 0x02e6000003a00000 0x0af000000c000001 0x02bc000003000000

def z560 : W := mkw 0xc7eefffdf002c055 0x31fbbfff7c00b015 0xeffffffff007c03f 0xbbfffffffc01f00f

def z561 : W := mkw 0x342003af50087d78 0x0d0800ebd4021f5e 0x540003fff0003ffc 0x150000fffc000fff

def z562 : W := mkw 0x14775d74f5d3d3d4 0x051dd75d3d74f4f5 0xfdff3cf1f3c7c7fe 0xff7fcf3c7cf1f1ff

def z563 : W := mkw 0x030002800a002400 0x00c000a002800900 0x020003000c003801 0x008000c003000e00

def z564 : W := mkw 0x402003a000003500 0x500800e800000d40 0x0000030000003800 0x000000c000000e00

def z565 : W := mkw 0x4b8b02d00b402680 0x52e2c0b402d009a0 0x530f03c00f003e03 0x54c3c0f003c00f80

def z566 : W := mkw 0x1470492454915150 0x051c124915245454 0xaaf0cc307cf9c1c3 0xeabc330c1f3e7070

def z567 : W := mkw 0xcffffffdeff7b781 0xf3ffffff7bfdede0 0xffffffffffffffc3 0xfffffffffffffff0

def z568 : W := mkw 0x00051400b142c2d4 0x000145002c50b0b5 0xb4003c01f3c7c7fc 0x6d000f007cf1f1ff

def z569 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0xa600f30f8c3e383d 0x29803cc3e30f8e0f

def z570 : W := mkw 0x0020012000000000 0x0008004800000000 0x4af0033000000003 0x92bc00cc00000000

def z571 : W := mkw 0x4ffb4bf44fc03780 0x53fed2fd13f00de0 0xdfffcffe7fc03fc3 0xf7fff3ff9ff00ff0

def z572 : W := mkw 0x6bbb03fb0fc83fa8 0x5aeec0fec3f20fea 0x5fff03ff8fc03fff 0xd7ffc0ffe3f00fff

def z573 : W := mkw 0x1010000214995970 0x040400008526565c 0xf600c30e0cf9f9f3 0x7d8030c3833e7e7c

def z574 : W := mkw 0x1050480214995970 0x041412008526565c 0xbaf0cc000cf9f9f3 0xeebc3300033e7e7c

def z575 : W := mkw 0x3440e80f503d4878 0x0d103a03d40f521e 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z576 : W := mkw 0x00030050114042d0 0x0000c014045010b4 0xf50f0cf073c1c7f2 0xfd43c33c1cf071fc

def z577 : W := mkw 0x0300a2800a242400 0x00c028a002890900 0xf300f3c00f3e3e03 0x7cc03cf003cf8f80

def z578 : W := mkw 0x488b005001400280 0x5222c014005000a0 0x000f000000000000 0x0003c00000000000

def z579 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0x09ff00f003c007c0 0x827fc03c00f001f0

def z580 : W := mkw 0xd4fe5d76f4995971 0x353f975dbd26565c 0xfeffcf3e7cf9f9f3 0xffbff3cf9f3e7e7c

def z581 : W := mkw 0x2000028b00082c28 0x080000a2c0020b0a 0xf50033cf83063e3e 0x7d400cf3e0c18f8f

def z582 : W := mkw 0x5cfb497655d95bf0 0x573ed25d957656fc 0xfeffcf3e7cf9f9f3 0xffbff3cf9f3e7e7c

def z583 : W := mkw 0x0005140001428000 0x000145000050a000 0x010f300003060000 0x0043cc0000c18000

def z584 : W := mkw 0x14724976f4995bf4 0x051c925dbd2656fd 0xfef0cffffcf9ffff 0xffbc33ffff3e7fff

def z585 : W := mkw 0x0300a28900000000 0x00c028a240000000 0x010030c180000000 0x00400c3060000000

def z586 : W := mkw 0x080100000b668000 0x8200400002d9a000 0x0000000003060000 0x0000000000c18000

def z587 : W := mkw 0x602203fb00083fa8 0x580880fec0020fea 0x540003ff80003ffc 0x150000ffe0000fff

def z588 : W := mkw 0x402203f0b00077d4 0x500880fc2c001df5 0x540003f1f0003ffc 0x150000fc7c000fff

def z589 : W := mkw 0x2000a00b002c0828 0x08002802c00b020a 0xf500f0cf833e063e 0x7d403c33e0cf818f

def z590 : W := mkw 0x0000000010004050 0x0000000004001014 0x00000c3070c1c1c0 0x8000030c1c307070

def z591 : W := mkw 0x3770ebaf5ebd7d78 0x0ddc3aebd7af5f5e 0xfef0cf3e7cf9f9f3 0xffbc33cf9f3e7e7c

def z592 : W := mkw 0x9ff8e9265ebd5970 0xa7fe3a4997af565c 0xfef0cf3e7cf9f9f3 0xffbc33cf9f3e7e7c

def z593 : W := mkw 0x9bddfc021fffd970 0xa6f77f0087fff65c 0xbbfffc000ffff9f3 0xeeffff0003fffe7c

def z594 : W := mkw 0x000100001142c2d4 0x000040000450b0b5 0x0000000000c1c1c0 0x0000000000307070

def z595 : W := mkw 0xcbfdffa00ff7b500 0xf2ff7fe803fded40 0xabffff000ffff803 0xeaffffc003fffe00

def z596 : W := mkw 0x83ccfe8900000000 0x20f33fa240000000 0xcfffffcf80000003 0xb3fffff3e0000000

def z597 : W := mkw 0xc388a28900000001 0x30e228a240000000 0x0000000000000000 0x0000000000000000

def z598 : W := mkw 0x8440e80d40000001 0x21103a0350000000 0x0000c00e00000000 0x0000300380000000

def z599 : W := mkw 0x0000000000000000 0x0000000000000000 0xf400000000000032 0x7d0000000000000c

def z600 : W := mkw 0x83cefc50a0000000 0x20f3bf1428000000 0xcffffcf1f0000003 0xb3ffff3c7c000000

def z601 : W := mkw 0x0b8900000b400000 0x02e2400002d00000 0x010f000003000000 0x0043c00000c00000

def z602 : W := mkw 0xc7eefffdf00042d5 0x31fbbfff7c0010b5 0xdffffffff00007ff 0xb7fffffffc0001ff

def z603 : W := mkw 0x0000000000000000 0x0000000000000000 0xa200c0000c380003 0x68803000030e0000

def z604 : W := mkw 0xc3aeb7f9a0000001 0x30ebadfe68000000 0x4bff33f180000003 0x92ffccfc60000000

def z605 : W := mkw 0x1420012650085970 0x050800499402165c 0xf600c33e7c3839f3 0x7d8030cf9f0e0e7c

def z606 : W := mkw 0xc4ef5d74f142c2d5 0x313bd75d3c50b0b5 0x08ff0c3070c1c1c0 0x823fc30c1c307070

def z607 : W := mkw 0x2000028b00082c28 0x080000a2c0020b0a 0x0000030e00003800 0x000000c380000e00

def z608 : W := mkw 0xcffdffad4ff78001 0xb3ff7feb53fde000 0xabffff0e0fffc003 0xeaffffc383fff000

def z609 : W := mkw 0x081100000fc00000 0x0204400003f00000 0x000000000fc00000 0x4000000003f00000

def z610 : W := mkw 0xf7fefffffebd7d79 0x3dffbfffffaf5f5e 0xffffffffffffffff 0xffffffffffffffff

def z611 : W := mkw 0x2000a00b002c0828 0x08002802c00b020a 0x0000c00e00380000 0x00003003800e0000

def z612 : W := mkw 0x0300a0000a240000 0x00c0280002890000 0xf700f0c18f3e063f 0x7dc03c3063cf818f

def z613 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0xc700f3cf8c383803 0x31c03cf3e30e0e00

def z614 : W := mkw 0xc7ee5ff4e0000001 0x31fb97fd38000000 0x4bff0ff070000003 0x92ffc3fc1c000000

def z615 : W := mkw 0x8744fe8de0000001 0x21d13fa378000000 0xc700ffcff0000003 0x31c03ff3fc000000

def z616 : W := mkw 0x8044fc00b037c054 0xa0113f002c0df015 0xa400fc01f03fc03c 0x29003f007c0ff00f

def z617 : W := mkw 0x1010000014915150 0x0404000005245454 0x0000000000c1c1c0 0x0000000000307070

def z618 : W := mkw 0x2300a2890a242408 0x08c028a242890902 0x530033c18f063e0f 0x54c00cf063c18f83

def z619 : W := mkw 0x2350ea8b0ebd2c28 0x08d43aa2c3af4b0a 0xfff0ffcf8ffffe3f 0xfffc3ff3e3ffff8f

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0xa40030018006003c 0x29000c006001800f

def z621 : W := mkw 0x2300a28b002c0828 0x08c028a2c00b020a 0xe700f3cf803e003f 0x39c03cf3e00f800f

def z622 : W := mkw 0x0003005001400280 0x0000c014005000a0 0x000f003000c001c0 0x8003c00c00300070

def z623 : W := mkw 0x9fddfc065fffc870 0xa7f77f0197fff21c 0xaffffc0e7fffc033 0xebffff039ffff00c

def z624 : W := mkw 0xccff5d74e5c01381 0x733fd75d397004e0 0x08ff0c3070c001c0 0x823fc30c1c300070

def z625 : W := mkw 0xc7fefffde4910001 0x31ffbfff79244000 0xeffffffffcf9c003 0xfbffffffff3e7000

def z626 : W := mkw 0x483303f00fc03780 0x520cc0fc03f00de0 0x500003f00fc03fc0 0x540000fc03f00ff0

def z627 : W := mkw 0x0000000000000000 0x0000000000000000 0x300000000306063c 0x4c00000000c1818f

def z628 : W := mkw 0xcb8fb6d9ab668001 0xb2e3edb66ad9a000 0x010f30c183060000 0x0043cc3060c18000

def z629 : W := mkw 0x200202dbb0086efc 0x080080b6ec021bbf 0x540003fff0003ffc 0x150000fffc000fff

def z630 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0xa500f0cf833e063c 0x29403c33e0cf818f

def z631 : W := mkw 0x1473497655d95bf0 0x051cd25d957656fc 0xffffcffe7ff9fff3 0xfffff3ff9ffe7ffc

def z632 : W := mkw 0x8045fc0001778000 0xa0117f00005de000 0xa10ffc0003ffc002 0xe843ff0000fff000

def z633 : W := mkw 0x0000000200080820 0x0000000080020208 0x300000000c383830 0x4c000000030e0e0c

def z634 : W := mkw 0x081000000e803500 0x4204000003a00d40 0x000000000c003800 0x0000000003000e00

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0xc4000c3070000002 0xb100030c1c000000

def z636 : W := mkw 0x081000000eb50000 0x8204000003ad4000 0x000000000c380000 0x00000000030e0000

def z637 : W := mkw 0xcfeffffdeb668001 0xb3fbffff7ad9a000 0xcffffffff3060003 0xb3fffffffcc18000

def z638 : W := mkw 0x97fcfd2654995970 0x25ff3f499526565c 0xffffff3e7cf9f9f3 0xffffffcf9f3e7e7c

def z639 : W := mkw 0x1420012450005150 0x0508004914001454 0x00000030700001c0 0x0000000c1c000070

def z640 : W := mkw 0x00061450b0004050 0x000185142c001014 0xf50f3cf1f0c1c1f2 0xfd43cf3c7c30707c

def z641 : W := mkw 0x0811000005c01380 0x42044000017004e0 0x0000000000c001c0 0x0000000000300070

def z642 : W := mkw 0x0b11a0000ff78000 0x82c4680003fde000 0xa300f0000fffc003 0x68c03c0003fff000

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0xc600c30e00000003 0x318030c380000000

def z644 : W := mkw 0x1000000210085970 0x040000008402165c 0x10000000000039f0 0x0400000000000e7c

def z645 : W := mkw 0x00030050b142c2d4 0x0000c0142c50b0b5 0x740000f1f3c7c7fc 0x5d00003c7cf1f1ff

def z646 : W := mkw 0x00020050a0000284 0x00008014280000a1 0x000000c18000060c 0x0000003060000183

def z647 : W := mkw 0x0000000010004050 0x0000000004001014 0xf5003cf1f3c7c7fe 0xfd400f3c7cf1f1ff

def z648 : W := mkw 0x4b9b02d00fc02680 0x52e6c0b403f009a0 0x0bff00c00fc00603 0xc2ffc03003f00180

def z649 : W := mkw 0x8b8fb450bb66c2d4 0xa2e3ed142ed9b0b5 0xf50f3cf1f3c7c7fe 0xfd43cf3c7cf1f1ff

def z650 : W := mkw 0x0300a0000a240000 0x00c0280002890000 0x0200c0000c380001 0x00803000030e0000

def z651 : W := mkw 0x081100001fc2f7d4 0x4204400007f0bdf5 0x300000000fc7fffc 0x4c00000003f1ffff

def z652 : W := mkw 0xe38eb6dbaa2c2c29 0x38e3adb6ea8b0b0a 0xf70ff3cf8f3e3e3f 0x7dc3fcf3e3cf8f8f

def z653 : W := mkw 0x0899000005c00000 0x0226400001700000 0x08ff000000c00000 0x823fc00000300000

def z654 : W := mkw 0x000100001142c2d4 0x000040000450b0b5 0xf50030c183c7c7fe 0x7d400c3060f1f1ff

def z655 : W := mkw 0x081100001ff7c2d4 0x8204400007fdf0b5 0x300000000fffc7fc 0x4c00000003fff1ff

def z656 : W := mkw 0x00071450a1428284 0x0001c5142850a0a1 0xa10f3cc183c7c60e 0xe843cf3060f1f183

def z657 : W := mkw 0x1470492654995970 0x051c12499526565c 0xaef0cf0e7c39f831 0x2bbc33c39f0e7e0c

def z658 : W := mkw 0x2306b6dbaa2c2c28 0x08c1adb6ea8b0b0a 0xf70fffffff3e3e3f 0xfdc3ffffffcf8f8f

def z659 : W := mkw 0x085148000ff78000 0x8214520003fde000 0xaaf0cc000fffc003 0xeabc330003fff000

def z660 : W := mkw 0x6bbb03f20fec3fa8 0x5aeec0fc83fb0fea 0x7bff03f00ffe3fff 0xdeffc0fc03ff8fff

def z661 : W := mkw 0x0300a2890a240000 0x00c028a242890000 0xe700f3cf8f3e0003 0x79c03cf3e3cf8000

def z662 : W := mkw 0x00061450b002c2d4 0x000185142c00b0b5 0xf4003cf1f007c7fc 0x3d000f3c7c01f1ff

def z663 : W := mkw 0xcffffffdefc00001 0x33ffffff7bf00000 0xcfffffffffc00003 0xf3fffffffff00000

def z664 : W := mkw 0x0000000010004050 0x0000000004001014 0x54000030700001f0 0x1500000c1c00007c

def z665 : W := mkw 0x20071452bb6eeefc 0x0801c514aedbbbbf 0xf50f3cf1fffffffe 0xfd43cf3c7fffffff

def z666 : W := mkw 0xcfff5ff4efc03781 0x73ffd7fd3bf00de0 0x5bff0ff07fc03fc3 0xd6ffc3fc1ff00ff0

def z667 : W := mkw 0x403203f004803780 0x500c80fc01200de0 0x5af003f00cc03fc3 0xd6bc00fc03300ff0

def z668 : W := mkw 0xc7e8ebad40000001 0x31fa3aeb50000000 0xcff0f3cf80000003 0x33fc3cf3e0000000

def z669 : W := mkw 0x2305b68b0b6eac28 0x08c16da2c2dbab0a 0xf70fffcf8ffffe3f 0xfdc3fff3e3ffff8f

def z670 : W := mkw 0x8855fc000ff78000 0xa2157f0003fde000 0xa000fc000fffc000 0x68003f0003fff000

def z671 : W := mkw 0x48bb017005c01380 0x522ec05c017004e0 0x59ff00f003c007c2 0xd67fc03c00f001f0

def z672 : W := mkw 0x4b9b02d00fc03780 0x52e6c0b403f00de0 0x110f00c00fc03fc0 0x4443c03003f00ff0

def z673 : W := mkw 0x0001000001428284 0x000040000050a0a1 0x000000000306060c 0x0000000000c18183

def z674 : W := mkw 0x1470492654995970 0x051c12499526565c 0x3af0c30e0cf9f9f1 0x4ebc30c3833e7e7c

def z675 : W := mkw 0x030002800a002400 0x00c000a002800900 0xf70033c18f063e3f 0x7dc00cf063c18f8f

def z676 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0x310f30c183c7c7fc 0x4c43cc3060f1f1ff

def z677 : W := mkw 0x0000000000000000 0x0000000000000000 0x5000003000c001c2 0xd400000c00300070

def z678 : W := mkw 0x2000a28b002c2c28 0x080028a2c00b0b0a 0xf400f3cf803e3e3c 0x3d003cf3e00f8f8f

def z679 : W := mkw 0x0003005001400280 0x0000c014005000a0 0xf50f30f183c607fe 0xfd43cc3c60f181ff

def z680 : W := mkw 0x8bdcfc000eb78000 0xa2f73f0003ade000 0xaaf0fc000c3fc001 0x2abc3f00030ff000

def z681 : W := mkw 0x0010000004801100 0x0004000001200440 0x100000000cc039c0 0x4400000003300e70

def z682 : W := mkw 0x0000000200080820 0x0000000080020208 0x0200c30e0c383801 0x008030c3830e0e00

def z683 : W := mkw 0xa344fe8b0a3fac28 0xa8d13fa2c28feb0a 0xf700ffcf8f3ffe3f 0x7dc03ff3e3cfff8f

def z684 : W := mkw 0x5bbb03f21fd97ff0 0x56eec0fc87f65ffc 0x7bff03f00ff9fff3 0xdeffc0fc03fe7ffc

def z685 : W := mkw 0x88d8480004910000 0xa236120001244000 0x08f0000000000000 0x023c000000000000

def z686 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0xc50f3cf1f0c1c1c2 0xb143cf3c7c307070

def z687 : W := mkw 0x1470492454915150 0x051c124915245454 0xfcf00c3070c1c1f2 0xff3c030c1c30707c

def z688 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0xa300f30e0f3e3803 0x68c03cc383cf8e00

def z689 : W := mkw 0x00371570b5c2d3d4 0x000dc55c2d70b4f5 0xffff3ff1ffc7ffff 0xffffcffc7ff1ffff

def z690 : W := mkw 0x0040480000110000 0x0010120000044000 0xa000cc000039c000 0x28003300000e7000

def z691 : W := mkw 0x20000002002c0828 0x08000000800b020a 0x20000000003e003c 0x08000000000f800f

def z692 : W := mkw 0x642203ffe0082c29 0x190880fff8020b0a 0x540003fff0003e3c 0x150000fffc000f8f

def z693 : W := mkw 0x1470492644991920 0x051c124991264648 0xfef0c30e0c383833 0x7fbc30c3830e0e0c

def z694 : W := mkw 0x0020012000001100 0x0008004800000440 0x50000330000039c0 0x140000cc00000e70

def z695 : W := mkw 0x00041400b002c054 0x000105002c00b015 0xf5003cc1f307c63e 0x7d400f307cc1f18f

def z696 : W := mkw 0xcbfffd700ff79380 0xf2ffff5c03fde4e0 0xabfffc300fffc1c3 0xeaffff0c03fff070

def z697 : W := mkw 0xcfeffffdeb402681 0x73fbffff7ad009a0 0xcffffffff3000603 0xb3fffffffcc00180

def z698 : W := mkw 0x0000000000000000 0x0000000000000000 0xa100300003060002 0x68400c0000c18000

def z699 : W := mkw 0x6bb8a3ab0eac3d28 0x5aee28eac3ab0f4a 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z700 : W := mkw 0x281100020fffac28 0x8a04400083ffeb0a 0x300000000ffffe3c 0x4c00000003ffff8f

def z701 : W := mkw 0xe7effffffb6eeefd 0x39fbfffffedbbbbf 0xffffffffffffffff 0xffffffffffffffff

def z702 : W := mkw 0x200000020a2c2c28 0x08000000828b0b0a 0xf600c30e0f3e3e3f 0x7d8030c383cf8f8f

def z703 : W := mkw 0x8b8fb450ab668284 0xa2e3ed142ad9a0a1 0x010f30c18306060c 0x0043cc3060c18183

def z704 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0x0300f3cf8f3e3e0d 0x00c03cf3e3cf8f83

def z705 : W := mkw 0x0b99a0000fe40000 0x02e6680003f90000 0xabfff0000ffe0003 0xeafffc0003ff8000

def z706 : W := mkw 0x9cfd5d2655dbd970 0xa73f57499576f65c 0xfeffcf3e7cf9f9f3 0xffbff3cf9f3e7e7c

def z707 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0xceffcf3e70000003 0xb3bff3cf9c000000

def z708 : W := mkw 0x8fddfc0d4ff78001 0xa3f77f0353fde000 0xabfffc0e0fffc003 0xeaffff0383fff000

def z709 : W := mkw 0x8c55fc0defc03781 0x63157f037bf00de0 0x9400fc0fffc03fc0 0x65003f03fff00ff0

def z710 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0x0bfffffff0000001 0x82fffffffc000000

def z711 : W := mkw 0x14775d76e5db9ba4 0x051dd75db976e6e9 0x0bfff3cf8f3e3e0d 0x02fffcf3e3cf8f83

def z712 : W := mkw 0x68bba17b05ec1ba8 0x5a2ee85ec17b06ea 0xacfff03f80fe01fc 0xab3ffc0fe03f807f

def z713 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0xeffffffff3060003 0xfbfffffffcc18000

def z714 : W := mkw 0xc7ecffade0000001 0x31fb3feb78000000 0x8fffff0ff0000003 0xa3ffffc3fc000000

def z715 : W := mkw 0x88dd5c0005d38000 0xa23757000174e000 0x28ff0c000cf9c000 0xca3fc300033e7000

def z716 : W := mkw 0x4bbb03f90fc03780 0x52eec0fe43f00de0 0x5fff03ff8fc03fc3 0xd7ffc0ffe3f00ff0

def z717 : W := mkw 0x1470492654995970 0x051c12499526565c 0xfef0cf3e7fffffff 0xffbc33cf9fffffff

def z718 : W := mkw 0x8bddfc000ff7b500 0xe2f77f0003fded40 0xabfffc000ffff803 0xeaffff0003fffe00

def z719 : W := mkw 0xc7eefffdea240001 0x31fbbfff7a890000 0xffffffffff3e063f 0xffffffffffcf818f

def z720 : W := mkw 0x1422017650085bf0 0x0508805d940216fc 0x540003fe70003ff0 0x150000ff9c000ffc

def z721 : W := mkw 0x4bbba3f90fc03780 0x52eee8fe43f00de0 0xfffff3ff8fc63fff 0xfffffcffe3f18fff

def z722 : W := mkw 0x4bbb03f00fd13780 0x52eec0fc03f44de0 0x7bff03f00ff9ffc3 0xdeffc0fc03fe7ff0

def z723 : W := mkw 0xc4ee5d74e0000001 0x313b975d38000000 0x0affcf3e70000001 0x82bff3cf9c000000

def z724 : W := mkw 0x542203fff0087ff1 0x550880fffc021ffc 0x540003fff0003ff0 0x150000fffc000ffc

def z725 : W := mkw 0x87ecfd2de0000001 0x21fb3f4b78000000 0xcfffff3ff0000003 0xb3ffffcffc000000

def z726 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0x5700f3cf8f3e3e3d 0x15c03cf3e3cf8f8f

def z727 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0xa50f3cf1f3c7c7fc 0xa943cf3c7cf1f1ff

def z728 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0x4bffcffe70000003 0x92fff3ff9c000000

def z729 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0x5fff03f18fc03fff 0xd7ffc0fc63f00fff

def z730 : W := mkw 0x181100021fffdbf4 0x8604400087fff6fd 0x300000000ffffffc 0x4c00000003ffffff

def z731 : W := mkw 0x4bba03f00e803780 0x52ee80fc03a00de0 0x5bff03f00c003fc3 0x96ffc0fc03000ff0

def z732 : W := mkw 0x5fcb4ad65b596ef0 0x57f2d2b596d65bbc 0xa50fccce7339c630 0x2943f3339cce718c

def z733 : W := mkw 0x43aa03f000001100 0x10ea80fc00000440 0x5bff03f0000039c3 0x96ffc0fc00000e70

def z734 : W := mkw 0x07e8492440000000 0x01fa124910000000 0xcfffcf3e70000003 0xb3fff3cf9c000000

def z735 : W := mkw 0xc066fff00037b780 0xf019bffc000dede0 0xf000fff0003fffc0 0x3c003ffc000ffff0

def z736 : W := mkw 0x9cff5d74f5d3d3d4 0xa73fd75d3d74f4f5 0x08ff0c3070c1c1c0 0x823fc30c1c307070

def z737 : W := mkw 0x04645d2440000000 0x0119174910000000 0xcfffff3e70000003 0xb3ffffcf9c000000

def z738 : W := mkw 0x54220176f0085971 0x1508805dbc02165c 0x5400033e700039f0 0x150000cf9c000e7c

def z739 : W := mkw 0x2388a28b0a2c2c28 0x08e228a2c28b0b0a 0xfffff3cf8f3e3e3f 0xfffffcf3e3cf8f8f

def z740 : W := mkw 0x0b9b00500fc03780 0x42e6c01403f00de0 0x5bff00f00fc03fc3 0xd6ffc03c03f00ff0

def z741 : W := mkw 0x8bddfe890ff78000 0xa2f77fa243fde000 0xabffff0e0fffc003 0xeaffffc383fff000

def z742 : W := mkw 0xc7eefffdea002401 0x31fbbfff7a800900 0xcffffffff3000603 0xb3fffffffcc00180

def z743 : W := mkw 0xe4ee5d76ea2c2c29 0x393b975dba8b0b0a 0x38ff0c307f3e3e3c 0xce3fc30c1fcf8f8f

def z744 : W := mkw 0x281100021fffeefc 0x8a04400087fffbbf 0x300000000ffffffc 0x4c00000003ffffff

def z745 : W := mkw 0xc7e9ebad5142c2d5 0x31fa7aeb5450b0b5 0x3af0c30e03c7c7fd 0x4ebc30c380f1f1ff

def z746 : W := mkw 0x0b9902800fc03780 0x42e640a003f00de0 0x5bff03c00fc03fc3 0xd6ffc0f003f00ff0

def z747 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0x550f3cf1f3c7c7fc 0x9543cf3c7cf1f1ff

def z748 : W := mkw 0xc7ecffad40000001 0x31fb3feb50000000 0xcfffff3e70000003 0xb3ffffcf9c000000

def z749 : W := mkw 0x2307b6dbbb6eeefc 0x08c1edb6eedbbbbf 0x020fcf3e7cf9f9c1 0x8083f3cf9f3e7e70

def z750 : W := mkw 0x8bdae850beb542d4 0xa2f6ba142fad50b5 0x5ef0c0f1fc3807fd 0x17bc303c7f0e01ff

def z751 : W := mkw 0x1470492654995970 0x051c12499526565c 0x5af0cf3e7cf9f9c3 0xd6bc33cf9f3e7e70

def z752 : W := mkw 0xc4eefd7de0000001 0x313bbf5f78000000 0x08ffcc3e70000000 0x823ff30f9c000000

def z753 : W := mkw 0x8bddfc09aff78001 0xa2f77f026bfde000 0xabfffc018fffc003 0xeaffff0063fff000

def z754 : W := mkw 0x4bbc17a0be82f554 0x52ef05e82fa0bd55 0xaef03f01fc07f83d 0x2bbc0fc07f01fe0f

def z755 : W := mkw 0xb444fc0f503fc878 0xad113f03d40ff21e 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z756 : W := mkw 0x94445c06f0194871 0x25111701bc06521c 0xa400cc0e7039c030 0x290033039c0e700c

def z757 : W := mkw 0x0300a0020a2c0820 0x00c02800828b0208 0xf700f3cf8f3e3e3f 0x7dc03cf3e3cf8f8f

def z758 : W := mkw 0xe38fb6d9ab66a68d 0x38e3edb66ad9a9a3 0x010f30c18306060c 0x0043cc3060c18183

def z759 : W := mkw 0x4bbba3f90fc03780 0x52eee8fe43f00de0 0x5bff33f18fc03fc3 0xd6ffccfc63f00ff0

def z760 : W := mkw 0x030002820a082c20 0x00c000a082820b08 0xf700f3cf8f3e3e3f 0x7dc03cf3e3cf8f8f

def z761 : W := mkw 0x403303f005c03780 0x500cc0fc01700de0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z762 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0x5bff33f18fc63fcf 0xd6ffccfc63f18ff3

def z763 : W := mkw 0x0470492444911100 0x011c124911244440 0xfef0cf3e7cf9f9c3 0xffbc33cf9f3e7e70

def z764 : W := mkw 0x281100021feefffc 0x4a04400087fbbfff 0x300000000ffffffc 0x4c00000003ffffff

def z765 : W := mkw 0x4bbba3f00ff7b780 0xd2eee8fc03fdede0 0xfbfff3f00fffffc3 0xfefffcfc03fffff0

def z766 : W := mkw 0x83ddfc0005d38000 0x20f77f000174e000 0xabfffc000fffc003 0xeaffff0003fff000

def z767 : W := mkw 0x14445c06f01bc874 0x05111701bc06f21d 0xa400cc0e7039c030 0x290033039c0e700c

def z768 : W := mkw 0x0b9900000fd10000 0x02e6400003f44000 0x2bff00000ff9c003 0xcaffc00003fe7000

def z769 : W := mkw 0xa8dd5e8b05dbac28 0xaa3757a2c176eb0a 0x5cff0fcf80c1fe3c 0x973fc3f3e0307f8f

def z770 : W := mkw 0x43aa03f00a003780 0x50ea80fc02800de0 0x5bff03f00f003fc3 0xd6ffc0fc03c00ff0

def z771 : W := mkw 0x089900000fc03780 0x4226400003f00de0 0x18ff00000fc03fc0 0xc63fc00003f00ff0

def z772 : W := mkw 0x48bb03f005c03780 0x522ec0fc01700de0 0x59ff03f003c03fc2 0xd67fc0fc00f00ff0

def z773 : W := mkw 0x43bb03f005c01380 0x10eec0fc017004e0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z774 : W := mkw 0xc7ee5ff4e0000001 0x31fb97fd38000000 0xcfffcffe70000003 0xb3fff3ff9c000000

def z775 : W := mkw 0x6b88a28b0a2c2c28 0x5ae228a2c28b0b0a 0xf700f3cf8f3e3e3f 0x7dc03cf3e3cf8f8f

def z776 : W := mkw 0xd4ff5d74f5d3d3d5 0x353fd75d3d74f4f5 0x08ff0c3070c1c1c0 0x823fc30c1c307070

def z777 : W := mkw 0xc7eefffdea240001 0x31fbbfff7a890000 0xcffffffffc380003 0xb3ffffffff0e0000

def z778 : W := mkw 0x9fadb5265b6ed970 0xa7eb6d4996dbb65c 0x550f333e730639f0 0x1543cccf9cc18e7c

def z779 : W := mkw 0x48bb017005c01380 0x522ec05c017004e0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z780 : W := mkw 0x1811000215d95bf0 0x46044000857656fc 0x300000000cf9f9f0 0x4c000000033e7e7c

def z781 : W := mkw 0x3770ebad5eb57558 0x0ddc3aeb57ad5d56 0x09f03cf1f3c7c7cc 0x827c0f3c7cf1f1f3

def z782 : W := mkw 0x48bb017005c01380 0x522ec05c017004e0 0x58ff033000c039c0 0x963fc0cc00300e70

def z783 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0x8dfffcfff0000000 0xa37fff3ffc000000

def z784 : W := mkw 0xabddfe890ff7a408 0xaaf77fa243fde902 0xfbffffc18ffffe0f 0xfefffff063ffff83

def z785 : W := mkw 0x4bbb03f005c03780 0x52eec0fc01700de0 0x5bff03f000c03fc3 0x96ffc0fc00300ff0

def z786 : W := mkw 0xc7eefffde0028001 0x31fbbfff7800a000 0xeffffffff007c003 0xbbfffffffc01f000

def z787 : W := mkw 0x48bb03f005c03780 0x522ec0fc01700de0 0x08ff033000c039c0 0x823fc0cc00300e70

def z788 : W := mkw 0x8bddfe890ff78000 0xa2f77fa243fde000 0xffffffcf8fffc63f 0xfffffff3e3fff18f

def z789 : W := mkw 0xe7eefffde0240009 0x39fbbfff78090002 0xcffffffff006000f 0xb3fffffffc018003

def z790 : W := mkw 0x8bddfe800ff7b780 0xe2f77fa003fdede0 0xfbffffc00fffffc3 0xfefffff003fffff0

def z791 : W := mkw 0x4bbb03f00fc01100 0x12eec0fc03f00440 0x5bff03f00fc039c3 0xd6ffc0fc03f00e70

def z792 : W := mkw 0x0b9900000fc01100 0x02e6400003f00440 0x1bff00000fc039c3 0xc6ffc00003f00e70

def z793 : W := mkw 0x84ec5d2440000000 0x213b174910000000 0xceffcf3e70000003 0xb3bff3cf9c000000

def z794 : W := mkw 0xc4ee5d74e0000001 0x313b975d38000000 0xcffffffff0000003 0xb3fffffffc000000

def z795 : W := mkw 0xc4ee5d74e0000001 0x313b975d38000000 0x8cffcc3e70000000 0xa33ff30f9c000000

def z796 : W := mkw 0x48bb017005c01380 0x522ec05c017004e0 0x0aff03300cc039c1 0x82bfc0cc03300e70

def z797 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0x59ff03f003c03fc0 0x967fc0fc00f00ff0

def z798 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0x2affcc000fffc001 0xcabff30003fff000

def z799 : W := mkw 0xc7eefffde0001101 0x31fbbfff78000440 0xdffffffff00039c3 0xb7fffffffc000e70

def z800 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0xf70ffcf1ffffc7ff 0xfdc3ff3c7ffff1ff

def z801 : W := mkw 0x8bddfc000fd10000 0x22f77f0003f44000 0xabfffc000ff9c003 0xeaffff0003fe7000

def z802 : W := mkw 0xc7eefd7de0000001 0x31fbbf5f78000000 0x8ffffc3ff0000003 0xa3ffff0ffc000000

def z803 : W := mkw 0x40ba017004801100 0x102e805c01200440 0x5aff03300cc039c3 0xd6bfc0cc03300e70

def z804 : W := mkw 0x1470492654995970 0x051c12499526565c 0xfff0ff3e7ffff9f3 0xfffc3fcf9ffffe7c

def z805 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0xdffffffffc003803 0xf7ffffffff000e00

def z806 : W := mkw 0x48bb017005c01380 0x522ec05c017004e0 0x18ff00300cc039c0 0xc63fc00c03300e70

def z807 : W := mkw 0x88ddfc000ff78000 0xa2377f0003fde000 0xa8fffc000fffc000 0xea3fff0003fff000

def z808 : W := mkw 0x47aaa3fde0000001 0x11eaa8ff78000000 0xcffff3fff0000003 0xb3fffcfffc000000

def z809 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0xa9fffc0003ffc000 0xaa7fff0000fff000

def z810 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0x8effff3ff0000001 0xa3bfffcffc000000

def z811 : W := mkw 0xc7eefffde0000281 0x31fbbfff780000a0 0xdffffffff00007c3 0xb7fffffffc0001f0

def z812 : W := mkw 0x47ae17fde0000001 0x11eb85ff78000000 0xcfff3ffff0000003 0xb3ffcffffc000000

def z813 : W := mkw 0x88dd5c000ff78000 0xa237570003fde000 0xaaffcc000fffc003 0xeabff30003fff000

def z814 : W := mkw 0x181100021ffffff0 0xc604400087fffffc 0x300000000ffffff0 0x4c00000003fffffc

def z815 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0xdffffffff0c001c3 0xf7fffffffc300070

def z816 : W := mkw 0x87eefd74e0000000 0x21fbbf5d38000000 0xcffffffff0000003 0xb3fffffffc000000

def z817 : W := mkw 0x43ba03f00e803500 0x10ee80fc03a00d40 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z818 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0xaafffc000cffc001 0xaabfff00033ff000

def z819 : W := mkw 0xc7eefffde0002401 0x31fbbfff78000900 0xdffffffff0003e03 0xb7fffffffc000f80

def z820 : W := mkw 0x483303f00ff7b780 0xd20cc0fc03fdede0 0x700003f00fffffc0 0x5c0000fc03fffff0

def z821 : W := mkw 0x43ab03f001403780 0x50eac0fc00500de0 0x5bff03f003c03fc3 0xd6ffc0fc00f00ff0

def z822 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0x29ff3c000fffc000 0xca7fcf0003fff000

def z823 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0xefffff0e0fffc003 0xfbffffc383fff000

def z824 : W := mkw 0x4fbb03f44fc03780 0x53eec0fd13f00de0 0x5fff03fe7fc03fc3 0xd7ffc0ff9ff00ff0

def z825 : W := mkw 0x44aa03fde0000001 0x112a80ff78000000 0x4cff03fff0000000 0x933fc0fffc000000

def z826 : W := mkw 0x2000a28b0a2c2c28 0x080028a2c28b0b0a 0xf400f3cf8f3e3e3c 0x7d003cf3e3cf8f8f

def z827 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0xeffffffff0c1c003 0xfbfffffffc307000

def z828 : W := mkw 0x8bdd5c000ff78000 0xa2f7570003fde000 0x2bff0c000fffc003 0xcaffc30003fff000

def z829 : W := mkw 0xabddfe890ff7a408 0xaaf77fa243fde902 0xabfffc000fffc003 0xeaffff0003fff000

def z830 : W := mkw 0x83cdfc000b668000 0x20f37f0002d9a000 0xabfffc000fffc003 0xeaffff0003fff000

def z831 : W := mkw 0x8bddfc000ff79100 0xa2f77f0003fde440 0xbbfffc000ffff9c3 0xeeffff0003fffe70

def z832 : W := mkw 0x4c3303fdeff78001 0x930cc0ff7bfde000 0x640003ffffffc000 0x590000fffffff000

def z833 : W := mkw 0x43aeb7f9a0000000 0x10ebadfe68000000 0xcffffffff0000003 0xb3fffffffc000000

def z834 : W := mkw 0x00061450b0004050 0x000185142c001014 0xf50f3cf1f3c7c7fe 0xfd43cf3c7cf1f1ff

def z835 : W := mkw 0xc4ee5d7de0000001 0x313b975f78000000 0x0cff0c3ff0000000 0x833fc30ffc000000

def z836 : W := mkw 0x1011000215d95bf0 0x04044000857656fc 0x300000000ff9fff0 0x4c00000003fe7ffc

def z837 : W := mkw 0x0766fffde0000000 0x01d9bfff78000000 0xcffffffff0000003 0xb3fffffffc000000

def z838 : W := mkw 0xe7eefffdea242409 0x39fbbfff7a890902 0xdfffffffff063e0f 0xf7ffffffffc18f83

def z839 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0xdffffffff000063f 0xb7fffffffc00018f

def z840 : W := mkw 0x88dd5c000ff78000 0xa237570003fde000 0xa9ff3c000fffc002 0xea7fcf0003fff000

def z841 : W := mkw 0xc7eefffde0268001 0xb1fbbfff7809a000 0xcffffffff0060003 0xb3fffffffc018000

def z842 : W := mkw 0xc7eefffdea000001 0x31fbbfff7a800000 0xcfffffffff000003 0xf3ffffffffc00000

def z843 : W := mkw 0xab88a28b0a2c2c28 0xaae228a2c28b0b0a 0xf700f3cf8f3e3e3f 0x7dc03cf3e3cf8f8f

def z844 : W := mkw 0x4bbb03f00fc2b780 0x52eec0fc03f0ade0 0x7bff03f00fc7ffc3 0xdeffc0fc03f1fff0

def z845 : W := mkw 0x542203fff0084871 0x150880fffc02121c 0x440003fff0000030 0x110000fffc00000c

def z846 : W := mkw 0x1811000215dbd970 0x860440008576f65c 0x300000000cf9f9f0 0x4c000000033e7e7c

def z847 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0xfbfffc300fffc1c3 0xfeffff0c03fff070

def z848 : W := mkw 0x0bb901200fc03780 0x42ee404803f00de0 0x5bff03300fc03fc3 0xd6ffc0cc03f00ff0

def z849 : W := mkw 0x2000a00b002c0828 0x08002802c00b020a 0xf700f3cf8f3e3e3f 0x7dc03cf3e3cf8f8f

def z850 : W := mkw 0x14220176f0085bf4 0x0508805dbc0216fd 0x5400033e700039f0 0x150000cf9c000e7c

def z851 : W := mkw 0xc4eefd7de0000001 0x313bbf5f78000000 0xceffff3ff0000003 0xb3bfffcffc000000

def z852 : W := mkw 0xabddfc090ff78008 0xaaf77f0243fde002 0xabfffc018fffc00f 0xeaffff0063fff003

def z853 : W := mkw 0xc7eefd74e0000001 0x31fbbf5d38000000 0xcfffff3e70000003 0xb3ffffcf9c000000

def z854 : W := mkw 0x4bbb03f005c01380 0x52eec0fc017004e0 0x5bff03f00cc039c3 0xd6ffc0fc03300e70

def z855 : W := mkw 0x9444fc0ff01bc875 0x25113f03fc06f21d 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z856 : W := mkw 0x0462497440000000 0x0118925d10000000 0xcfffcffe70000003 0xb3fff3ff9c000000

def z857 : W := mkw 0x8bddfc000ff79380 0xe2f77f0003fde4e0 0xabfffc000fffc1c3 0xeaffff0003fff070

def z858 : W := mkw 0x0b99a0000ff78000 0x82e6680003fde000 0xabfff0000fffc003 0xeafffc0003fff000

def z859 : W := mkw 0x1470492654995970 0x051c12499526565c 0x3af0cf3e7cf9f9f1 0xcebc33cf9f3e7e7c

def z860 : W := mkw 0x4bbba3f00fe43780 0x52eee8fc03f90de0 0x5bffc3f00ff83fc3 0xd6fff0fc03fe0ff0

def z861 : W := mkw 0x381100021ffffd78 0x8e04400087ffff5e 0x300000000ffffffc 0x4c00000003ffffff

def z862 : W := mkw 0x4bbb03f9afc03781 0x52eec0fe6bf00de0 0x5bff03f18fc03fc3 0xd6ffc0fc63f00ff0

def z863 : W := mkw 0xe388a28b0a2c2c29 0x38e228a2c28b0b0a 0xf700f3cf8f3e3e3f 0x7dc03cf3e3cf8f8f

def z864 : W := mkw 0x1470492654995970 0x051c12499526565c 0xfff0cffe7ff9fff3 0xfffc33ff9ffe7ffc

def z865 : W := mkw 0xabddfe890ff7a408 0xaaf77fa243fde902 0xefffffcf8fffc60f 0xfbfffff3e3fff183

def z866 : W := mkw 0x0030012214885970 0x000c00488522165c 0xfef0cf3e7cf9f9f3 0xffbc33cf9f3e7e7c

def z867 : W := mkw 0x4bb903a00fc03780 0x52ee40e803f00de0 0x1bff03000fc03fc3 0xc6ffc0c003f00ff0

def z868 : W := mkw 0x4bbb03f00fc2b784 0x52eec0fc03f0ade1 0x5bff03f00fc63fcf 0xd6ffc0fc03f18ff3

def z869 : W := mkw 0x48bb017005c03780 0x522ec05c01700de0 0x18ff003000c03fc0 0x863fc00c00300ff0

def z870 : W := mkw 0x44ea497440000000 0x113a925d10000000 0xceffcf3e70000003 0xb3bff3cf9c000000

def z871 : W := mkw 0x542203fff0085bf5 0x150880fffc0216fd 0x540003fff0003ffc 0x150000fffc000fff

def z872 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0x8bffff3e70000003 0xa2ffffcf9c000000

def z873 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0xfbffff000ffff803 0xfeffffc003fffe00

def z874 : W := mkw 0x88dd5c0005d38000 0xa23757000174e000 0xabfffc000fffc003 0xeaffff0003fff000

def z875 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0xfbfffcc00fffc603 0xfeffff3003fff180

def z876 : W := mkw 0x8bcdfc000b778000 0xa2f37f0002dde000 0xabfffc00033fc003 0xaaffff0000cff000

def z877 : W := mkw 0xc7eefffde0003501 0x71fbbfff78000d40 0xcffffffff0003803 0xb3fffffffc000e00

def z878 : W := mkw 0x47eaebfd40000000 0x11fabaff50000000 0xcffffffff0000003 0xb3fffffffc000000

def z879 : W := mkw 0x0355fc000ff78000 0x00d57f0003fde000 0xabfffc000fffc003 0xeaffff0003fff000

def z880 : W := mkw 0x181100021fc87ff0 0x4604400087f21ffc 0x100000000fc03ff0 0x4400000003f00ffc

def z881 : W := mkw 0xc466fffde0003781 0x7119bfff78000de0 0xd400fffff0003fc0 0x35003ffffc000ff0

def z882 : W := mkw 0xabddfe890ff7a408 0xaaf77fa243fde902 0xfffffcc18fffc63f 0xffffff3063fff18f

def z883 : W := mkw 0x43ba03f004803780 0x50ee80fc01200de0 0x5bff03f00cc03fc3 0xd6ffc0fc03300ff0

def z884 : W := mkw 0xc4ee5d74e0000001 0x313b975d38000000 0x4cff0f3e70000000 0x933fc3cf9c000000

def z885 : W := mkw 0x6bbba3f90fe43788 0x5aeee8fe43f90de2 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z886 : W := mkw 0x6bbb03f00fe43788 0x5aeec0fc03f90de2 0x5bff03f00fc63fcf 0xd6ffc0fc03f18ff3

def z887 : W := mkw 0xc7eefffde0002681 0x71fbbfff780009a0 0xcffffffff0000603 0xb3fffffffc000180

def z888 : W := mkw 0x88ddfc0005f78000 0xa2377f00017de000 0xa9fffc0003ffc002 0xea7fff0000fff000

def z889 : W := mkw 0x8bddfc00aff78000 0xa2f77f002bfde000 0xaffffc01ffffc003 0xebffff007ffff000

def z890 : W := mkw 0x4bbba3f90fe43780 0x52eee8fe43f90de0 0xfffff3ff8ffe3fc3 0xfffffcffe3ff8ff0

def z891 : W := mkw 0x301100021ffffffc 0x0c04400087ffffff 0x300000000ffffffc 0x4c00000003ffffff

def z892 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0xa700f3cf8f3e3e3d 0x29c03cf3e3cf8f8f

def z893 : W := mkw 0x88ddfc0005f78000 0xa2377f00017de000 0xaafffc000cffc003 0xeabfff00033ff000

def z894 : W := mkw 0x1470492654995970 0x051c12499526565c 0xfef0ff3ffcfff9ff 0xffbc3fcfff3ffe7f

def z895 : W := mkw 0xc4ee5ffde0000001 0x313b97ff78000000 0x08ff0f3e70000000 0x823fc3cf9c000000

def z896 : W := mkw 0x8bddfc0005f78000 0xa2f77f00017de000 0xabfffc0000ffc003 0xaaffff00003ff000

def z897 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0xffff03f00fc03ff3 0xffffc0fc03f00ffc

def z898 : W := mkw 0xcbbba3f00fe43780 0xf2eee8fc03f90de0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z899 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0xf700ffcf8ffffe3f 0xfdc03ff3e3ffff8f

def z900 : W := mkw 0x84ccfc0de0000001 0x21333f0378000000 0x8cfffc0ff0000000 0xa33fff03fc000000

def z901 : W := mkw 0x88dd5c0005d38000 0xa23757000174e000 0x0affcc000cf9c001 0x82bff300033e7000

def z902 : W := mkw 0x4bbba3f00fe43780 0x52eee8fc03f90de0 0xfffff3f18ffe3fff 0xfffffcfc63ff8fff

def z903 : W := mkw 0x181100021fd95970 0x0604400087f6565c 0x300000000ff9f9f0 0x4c00000003fe7e7c

def z904 : W := mkw 0x8bddfe890ff7a400 0xa2f77fa243fde900 0xffffffcf8ffffe03 0xfffffff3e3ffff80

def z905 : W := mkw 0xcbbba3f90fc03781 0x72eee8fe43f00de0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z906 : W := mkw 0x8bddfe800ff78000 0xa2f77fa003fde000 0xebffffc00fffc003 0xfafffff003fff000

def z907 : W := mkw 0x5422017650085bf0 0x5508805d940216fc 0x5400033e700039f0 0x150000cf9c000e7c

def z908 : W := mkw 0x9444fc06f03fc874 0xa5113f01bc0ff21d 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z909 : W := mkw 0x87ecffad40000000 0x21fb3feb50000000 0xcffffffff0000003 0xb3fffffffc000000

def z910 : W := mkw 0x14445c06501bc870 0x051117019406f21c 0xa400fc0e703fc030 0x29003f039c0ff00c

def z911 : W := mkw 0x8bd9e8000ff78000 0xa2f67a0003fde000 0x2bffc0000fffc003 0xcafff00003fff000

def z912 : W := mkw 0x5cff5d74f5d3d3d4 0x573fd75d3d74f4f5 0x08ff0c3070c1c1c0 0x823fc30c1c307070

def z913 : W := mkw 0x1470492654995970 0x051c12499526565c 0xcef0cf3e7cf9f9c3 0xb3bc33cf9f3e7e70

def z914 : W := mkw 0x642203fff0086efd 0x190880fffc021bbf 0x540003fff0003ffc 0x150000fffc000fff

def z915 : W := mkw 0x87cefc5de0000001 0x21f3bf1778000000 0xcffffcfff0000003 0xb3ffff3ffc000000

def z916 : W := mkw 0x4bbb01700fc01380 0x52eec05c03f004e0 0x5bff03300fc039c3 0xd6ffc0cc03f00e70

def z917 : W := mkw 0xabddfc000ff7a408 0xaaf77f0003fde902 0xabfffc000fffc60f 0xeaffff0003fff183

def z918 : W := mkw 0x00030050114042d0 0x0000c014045010b4 0xf50f3cf1f3c7c7fe 0xfd43cf3c7cf1f1ff

def z919 : W := mkw 0x8855fc000ff7b780 0xe2157f0003fdede0 0xb000fc000fffffc0 0x6c003f0003fffff0

def z920 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0x0bff03f00fc03fc1 0x82ffc0fc03f00ff0

def z921 : W := mkw 0x88dd5c0005f78000 0xa2375700017de000 0x28ff0c0000ffc000 0x8a3fc300003ff000

def z922 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0x0bff03300fc039c3 0xc2ffc0cc03f00e70

def z923 : W := mkw 0x6bbba3f90fe43788 0x5aeee8fe43f90de2 0xffff33f18fc63fff 0xffffccfc63f18fff

def z924 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0xfbff33f00fc63fc3 0xfeffccfc03f18ff0

def z925 : W := mkw 0xa444fc0ff02ec87d 0x29113f03fc0bb21f 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z926 : W := mkw 0x03d8480004910000 0x00f6120001244000 0xabffcc000cf9c003 0xeafff300033e7000

def z927 : W := mkw 0xc4eefd7de0000001 0x313bbf5f78000000 0xcdfffcfff0000002 0xb37fff3ffc000000

def z928 : W := mkw 0x00545c0004910000 0x0015170001244000 0xabfffc000cf9c003 0xeaffff00033e7000

def z929 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0xeffffffffc380003 0xfbffffffff0e0000

def z930 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0x19ff00f00fc03fc0 0xc67fc03c03f00ff0

def z931 : W := mkw 0x742203ff50087ff8 0x5d0880ffd4021ffe 0x540003fff0003ffc 0x150000fffc000fff

def z932 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0x0bffcc000ff9c003 0xc2fff30003fe7000

def z933 : W := mkw 0x0b9d14000ff78000 0x82e7450003fde000 0xabff3c000fffc003 0xeaffcf0003fff000

def z934 : W := mkw 0x181100021fdbfff4 0x4604400087f6fffd 0x300000000ffffffc 0x4c00000003ffffff

def z935 : W := mkw 0xc4eefffde0000001 0x313bbfff78000000 0xccfffffff0000000 0xb33ffffffc000000

def z936 : W := mkw 0x83cefed9a0000000 0x20f3bfb668000000 0xcffffffff0000003 0xb3fffffffc000000

def z937 : W := mkw 0x4c3303fdefc03781 0x530cc0ff7bf00de0 0x540003ffffc03fc0 0x550000fffff00ff0

def z938 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0xf700f3ff8ffe3fff 0xfdc03cffe3ff8fff

def z939 : W := mkw 0xd39eb6dbb4995971 0x34e7adb6ed26565c 0x310f30c18cf9f9f0 0x4c43cc30633e7e7c

def z940 : W := mkw 0x83ccfc000a378000 0xa0f33f00028de000 0xabfffc000f3fc003 0xeaffff0003cff000

def z941 : W := mkw 0x4bb903a00fc03500 0x52ee40e803f00d40 0x5bff03300fc039c3 0xd6ffc0cc03f00e70

def z942 : W := mkw 0x1470492654995970 0x051c12499526565c 0xfef0cffffcf9ffff 0xffbc33ffff3e7fff

def z943 : W := mkw 0xc7eefffde0110001 0x31fbbfff78044000 0xeffffffff039c003 0xbbfffffffc0e7000

def z944 : W := mkw 0x03b8012004801100 0x00ee004801200440 0x5bff03300cc039c3 0xd6ffc0cc03300e70

def z945 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0xabfffc000f3fc001 0x2affff0003cff000

def z946 : W := mkw 0x0032017004801100 0x000c805c01200440 0x5bff03f00cc039c3 0xd6ffc0fc03300e70

def z947 : W := mkw 0x381100021ffd7ff8 0x4e04400087ff5ffe 0x300000000ffffffc 0x4c00000003ffffff

def z948 : W := mkw 0x0bd9e8000ff50000 0x02f67a0003fd4000 0xabfffc000fffc003 0xeaffff0003fff000

def z949 : W := mkw 0x94445c06501bc870 0xa51117019406f21c 0xa400cc0e7039c030 0x290033039c0e700c

def z950 : W := mkw 0x342203fff0087ffc 0x0d0880fffc021fff 0x540003fff0003ffc 0x150000fffc000fff

def z951 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0xfffffc000fffc033 0xffffff0003fff00c

def z952 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0xdfffc3fe0fc03fc3 0xf7fff0ff83f00ff0

def z953 : W := mkw 0x4fbb03f4efc03781 0x53eec0fd3bf00de0 0x5bff03f07fc03fc3 0xd6ffc0fc1ff00ff0

def z954 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0xeffffffff006003f 0xbbfffffffc01800f

def z955 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0x8bfffc000cf9c003 0xa2ffff00033e7000

def z956 : W := mkw 0xc7eaebfde0000001 0x31fabaff78000000 0x4fffc3fff0000003 0x93fff0fffc000000

def z957 : W := mkw 0x083301700fc03780 0x420cc05c03f00de0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z958 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0xbbfffc000fffc63f 0xeeffff0003fff18f

def z959 : W := mkw 0xc4ee5ffde0000001 0x313b97ff78000000 0xcdff3ffff0000002 0xb37fcffffc000000

def z960 : W := mkw 0xe7eefffdea242409 0x39fbbfff7a890902 0xefffffffff3e060f 0xfbffffffffcf8183

def z961 : W := mkw 0xc7eaebfd40000001 0x31fabaff50000000 0xcfffcffe70000003 0xb3fff3ff9c000000

def z962 : W := mkw 0x8fddfc044ff78000 0xa3f77f0113fde000 0xaffffc0e7fffc003 0xebffff039ffff000

def z963 : W := mkw 0x8bddfc090ff78000 0xa2f77f0243fde000 0xaffffc0f8fffc003 0xebffff03e3fff000

def z964 : W := mkw 0x43ab03f00b402680 0x10eac0fc02d009a0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z965 : W := mkw 0x47ea4bfde0000001 0x11fa92ff78000000 0xcfffcffff0000003 0xb3fff3fffc000000

def z966 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0x310f3cf1f3c7c7fc 0xcc43cf3c7cf1f1ff

def z967 : W := mkw 0xe7eefffde0002409 0x39fbbfff78000902 0xcffffffff000060f 0xb3fffffffc000183

def z968 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0xcffffffff306060f 0xb3fffffffcc18183

def z969 : W := mkw 0x83dcfc0004b78000 0xa0f73f00012de000 0xabfffc000cffc003 0xeaffff00033ff000

def z970 : W := mkw 0x4bbb03f00ff53780 0xd2eec0fc03fd4de0 0x5bff03f00ff83fc3 0xd6ffc0fc03fe0ff0

def z971 : W := mkw 0x9444fc0ff03fc871 0xa5113f03fc0ff21c 0xa400fc0ff03fc030 0x29003f03fc0ff00c

def z972 : W := mkw 0x8bd9e8000ff50000 0xa2f67a0003fd4000 0xabffcc000ff9c003 0xeafff30003fe7000

def z973 : W := mkw 0x4bbb03f00fe6b780 0xd2eec0fc03f9ade0 0x5bff03f00fc63fc3 0xd6ffc0fc03f18ff0

def z974 : W := mkw 0x80dc5c0004910000 0x2037170001244000 0xaaffcc000cf9c003 0xeabff300033e7000

def z975 : W := mkw 0xc7eefffde0001381 0x71fbbfff780004e0 0xcffffffff00001c3 0xb3fffffffc000070

def z976 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0x4dff3ffff0000000 0x937fcffffc000000

def z977 : W := mkw 0x9044fc02103fc870 0xa4113f00840ff21c 0xa000fc00003fc030 0x28003f00000ff00c

def z978 : W := mkw 0x88dd5c000ff78000 0xa237570003fde000 0x08ff0c000cf9c000 0x823fc300033e7000

def z979 : W := mkw 0x8bddfc000ff7a680 0xe2f77f0003fde9a0 0xabfffc000fffc603 0xeaffff0003fff180

def z980 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0x1aff03300fc03fc1 0xc6bfc0cc03f00ff0

def z981 : W := mkw 0x14445c06f0194870 0x05111701bc06521c 0xa400fc0ff039c030 0x29003f03fc0e700c

def z982 : W := mkw 0x0031012005c01100 0x000c404801700440 0x5bff03300fc039c3 0xd6ffc0cc03f00e70

def z983 : W := mkw 0xb444fc0ff03d4879 0x2d113f03fc0f521e 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z984 : W := mkw 0x44665ffde0000001 0x111997ff78000000 0xcffffffff0000003 0xb3fffffffc000000

def z985 : W := mkw 0x0300a28b00080820 0x00c028a2c0020208 0xf700f3cf8f3e3e3f 0x7dc03cf3e3cf8f8f

def z986 : W := mkw 0xc7eefffdea240001 0x31fbbfff7a890000 0xcffffffff3060003 0xb3fffffffcc18000

def z987 : W := mkw 0x0b9db4000fe68000 0x02e76d0003f9a000 0xabfffc000fffc003 0xeaffff0003fff000

def z988 : W := mkw 0x4bbba3f00fc03780 0x52eee8fc03f00de0 0xdbfff3f00fc03fc3 0xf6fffcfc03f00ff0

def z989 : W := mkw 0x4bbb01700fc03780 0x52eec05c03f00de0 0x1bff00300fc03fc3 0xc6ffc00c03f00ff0

def z990 : W := mkw 0x8bddfe800ff7a400 0xa2f77fa003fde900 0xabffff000ffff803 0xeaffffc003fffe00

def z991 : W := mkw 0xc7eefffde0350001 0xb1fbbfff780d4000 0xcffffffff0380003 0xb3fffffffc0e0000

def z992 : W := mkw 0xbff8ebaf4ebd3d28 0xaffe3aebd3af4f4a 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z993 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0x8fffffcff0000001 0x23fffff3fc000000

def z994 : W := mkw 0x48bb03f005c03780 0x522ec0fc01700de0 0x5aff03f00cc03fc3 0xd6bfc0fc03300ff0

def z995 : W := mkw 0x181100021fffc870 0x8604400087fff21c 0x200000000fffc030 0x4800000003fff00c

def z996 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0x0bfffc000fffc001 0x82ffff0003fff000

def z997 : W := mkw 0x0bd948000ff78000 0x82f6520003fde000 0xabffcc000fffc003 0xeafff30003fff000

def z998 : W := mkw 0x47aa03f440000000 0x11ea80fd10000000 0x4fff03fe70000003 0x93ffc0ff9c000000

def z999 : W := mkw 0x4bba03f00e803500 0x52ee80fc03a00d40 0x5bff03f00cc039c3 0xd6ffc0fc03300e70

def z1000 : W := mkw 0x8bdcfc000eb50000 0xa2f73f0003ad4000 0xabfffc000cf9c003 0xeaffff00033e7000

def z1001 : W := mkw 0x08555c000ff78000 0x8215570003fde000 0xabfffc000fffc003 0xeaffff0003fff000

def z1002 : W := mkw 0xc7eefffdea002401 0x31fbbfff7a800900 0xffffffffff063e3f 0xffffffffffc18f8f

def z1003 : W := mkw 0x8fddfe8deff78001 0xa3f77fa37bfde000 0xefffffcfffffc003 0xfbfffff3fffff000

def z1004 : W := mkw 0x48bb03f00fc03780 0x522ec0fc03f00de0 0x58ff03f00fc03fc0 0xd63fc0fc03f00ff0

def z1005 : W := mkw 0xc466fffde0378001 0xb119bfff780de000 0xe400fffff03fc000 0x39003ffffc0ff000

def z1006 : W := mkw 0x200000020a2c2c28 0x08000000828b0b0a 0xf700f3cf8f3e3e3f 0x7dc03cf3e3cf8f8f

def z1007 : W := mkw 0xc7eefffdea378001 0xb1fbbfff7a8de000 0xefffffffff3fc003 0xfbffffffffcff000

def z1008 : W := mkw 0x3444fc0ff03fc87c 0x0d113f03fc0ff21f 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z1009 : W := mkw 0x48bb01700fc03780 0x522ec05c03f00de0 0x59ff00f00fc03fc2 0xd67fc03c03f00ff0

def z1010 : W := mkw 0x4bbb03f0afc03780 0x52eec0fc2bf00de0 0x5fff03f1ffc03fc3 0xd7ffc0fc7ff00ff0

def z1011 : W := mkw 0x9444fc0ff0084871 0x25113f03fc02121c 0x8400fc0ff0000030 0x21003f03fc00000c

def z1012 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0xfffffffff0000033 0xfffffffffc00000c

def z1013 : W := mkw 0x1470492654995970 0x051c12499526565c 0xaef0cf3e7cf9f9f1 0xabbc33cf9f3e7e7c

def z1014 : W := mkw 0xcb8fb6d9ab66a681 0xf2e3edb66ad9a9a0 0x010f30c183060600 0x0043cc3060c18180

def z1015 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0x4ffff3fff0000001 0x13fffcfffc000000

def z1016 : W := mkw 0xa044fc0bb03fc87c 0xa8113f02ec0ff21f 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z1017 : W := mkw 0x0bb903a00fc03500 0x02ee40e803f00d40 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z1018 : W := mkw 0xc7eefffdea003781 0x71fbbfff7a800de0 0xdfffffffff003fc3 0xf7ffffffffc00ff0

def z1019 : W := mkw 0x9444fc0650194870 0x25113f019406521c 0xa400fc0e7039c030 0x29003f039c0e700c

def z1020 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0xdffffffff3000603 0xf7fffffffcc00180

def z1021 : W := mkw 0x4bbb03f00fd3b780 0xd2eec0fc03f4ede0 0x5bff03f00fc1ffc3 0xd6ffc0fc03f07ff0

def z1022 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0x5bff03f00f003fc1 0x16ffc0fc03c00ff0

def z1023 : W := mkw 0x1470492654995970 0x051c12499526565c 0xfff0fffffcf9f9f3 0xfffc3fffff3e7e7c

def z1024 : W := mkw 0x83ccfc0000110000 0x20f33f0000044000 0xabfffc000039c003 0xaaffff00000e7000

def z1025 : W := mkw 0x0460492650084870 0x011812499402121c 0xfef0cf3e7cf9f9f3 0xffbc33cf9f3e7e7c

def z1026 : W := mkw 0x88ddfc0005f78000 0xa2377f00017de000 0x08ffcc0000f9c000 0x823ff300003e7000

def z1027 : W := mkw 0xc7aeb7fde0000001 0x31ebadff78000000 0x4fff33fff0000003 0x93ffccfffc000000

def z1028 : W := mkw 0x542203f650085970 0x150880fd9402165c 0x540003fe700039f0 0x150000ff9c000e7c

def z1029 : W := mkw 0x48bb01700fc03780 0x522ec05c03f00de0 0x08ff00300cc039c0 0x823fc00c03300e70

def z1030 : W := mkw 0x4bbba3f00fe43780 0x52eee8fc03f90de0 0x5bff33f00fc63fc3 0xd6ffccfc03f18ff0

def z1031 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0xdfff33f18fc03fc3 0xf7ffccfc63f00ff0

def z1032 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0xf70f3ff1ffc7ffff 0xfdc3cffc7ff1ffff

def z1033 : W := mkw 0x6bbb03f90fc03788 0x5aeec0fe43f00de2 0x5bff03f18fc03fcf 0xd6ffc0fc63f00ff3

def z1034 : W := mkw 0x80ccfc0000378000 0xa0333f00000de000 0xa8fffc00003fc000 0xaa3fff00000ff000

def z1035 : W := mkw 0x00071450b142c2d4 0x0001c5142c50b0b5 0xf70ffffff3c7c7ff 0xfdc3fffffcf1f1ff

def z1036 : W := mkw 0x4b9b02d00fc03780 0x52e6c0b403f00de0 0x1bff00c00fc03fc3 0xc6ffc03003f00ff0

def z1037 : W := mkw 0x08b9012005c01100 0x022e404801700440 0x5aff03300cc039c3 0xd6bfc0cc03300e70

def z1038 : W := mkw 0x0b9b02d00fc02680 0x02e6c0b403f009a0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z1039 : W := mkw 0x14220176f0085970 0x0508805dbc02165c 0x540003fff00039f0 0x150000fffc000e7c

def z1040 : W := mkw 0xcfeefffdea240001 0xb3fbbfff7a890000 0xcffffffff0000003 0xb3fffffffc000000

def z1041 : W := mkw 0x8bddfe800ff7a400 0xa2f77fa003fde900 0xffffffc18ffffe3f 0xfffffff063ffff8f

def z1042 : W := mkw 0x8bddfe890ff78000 0xa2f77fa243fde000 0xabfffcc18fffc003 0xeaffff3063fff000

def z1043 : W := mkw 0x0bdd5c000fd38000 0x02f7570003f4e000 0xabfffc000fffc003 0xeaffff0003fff000

def z1044 : W := mkw 0x8bdd5c000fd38000 0xa2f7570003f4e000 0xabffcc000ff9c003 0xeafff30003fe7000

def z1045 : W := mkw 0xe7eefffdea242409 0x39fbbfff7a890902 0xfffffffff306063f 0xfffffffffcc1818f

def z1046 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0x7bff03f00fc63fff 0xdeffc0fc03f18fff

def z1047 : W := mkw 0x502203f210087ff0 0x540880fc84021ffc 0x500003f000003ff0 0x140000fc00000ffc

def z1048 : W := mkw 0xcfeefffdea002401 0x73fbbfff7a800900 0xcffffffff0000003 0xb3fffffffc000000

def z1049 : W := mkw 0x00555c0005d38000 0x001557000174e000 0xaaffcc000cf9c003 0xeabff300033e7000

def z1050 : W := mkw 0x47ee5ff4e0000000 0x11fb97fd38000000 0xcffffffff0000003 0xb3fffffffc000000

def z1051 : W := mkw 0x4fbba3fdefc03781 0x53eee8ff7bf00de0 0xdffff3ffffc03fc3 0xf7fffcfffff00ff0

def z1052 : W := mkw 0xc7eefffdea002401 0x31fbbfff7a800900 0xcffffffffc003803 0xb3ffffffff000e00

def z1053 : W := mkw 0x87ccfc0440000000 0x21f33f0110000000 0x8ffffc0e70000003 0xa3ffff039c000000

def z1054 : W := mkw 0x2000028b00082c28 0x080000a2c0020b0a 0xf700f3cf8f3e3e3f 0x7dc03cf3e3cf8f8f

def z1055 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0xfbffc3f00ff83fc3 0xfefff0fc03fe0ff0

def z1056 : W := mkw 0x7ff8ebaf4ebd3d28 0x5ffe3aebd3af4f4a 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z1057 : W := mkw 0x40aa03f000003780 0x502a80fc00000de0 0x58ff03f000003fc0 0x963fc0fc00000ff0

def z1058 : W := mkw 0x48bb01700fc03780 0x522ec05c03f00de0 0x5aff03300fc03fc3 0xd6bfc0cc03f00ff0

def z1059 : W := mkw 0x8fddfc04eff78001 0xa3f77f013bfde000 0xabfffc007fffc003 0xeaffff001ffff000

def z1060 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0xdfff0ff07fc03fc3 0xf7ffc3fc1ff00ff0

def z1061 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0xaaffcc000cf9c003 0xeabff300033e7000

def z1062 : W := mkw 0xc7eefffde0028005 0x31fbbfff7800a001 0xcffffffff006000f 0xb3fffffffc018003

def z1063 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0x4bff03f00cc039c3 0x92ffc0fc03300e70

def z1064 : W := mkw 0xc7eefff440000000 0x31fbbffd10000000 0xcffffffe70000003 0xb3ffffff9c000000

def z1065 : W := mkw 0x8bddfc000ff7a400 0xa2f77f0003fde900 0xbbfffc000ffffe03 0xeeffff0003ffff80

def z1066 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0xeffffc307fffc003 0xfbffff0c1ffff000

def z1067 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0x2bfff0000fffc001 0x4afffc0003fff000

def z1068 : W := mkw 0x033303f00fc03780 0x00ccc0fc03f00de0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z1069 : W := mkw 0x83dcfc000eb50000 0x20f73f0003ad4000 0xabfffc000fffc003 0xeaffff0003fff000

def z1070 : W := mkw 0x0051480005d10000 0x0014520001744000 0xabffcc000ff9c003 0xeafff30003fe7000

def z1071 : W := mkw 0x1011000215dbd970 0x040440008576f65c 0x300000000ffff9f0 0x4c00000003fffe7c

def z1072 : W := mkw 0xc7eefffde0240001 0x31fbbfff78090000 0xeffffffff03e0003 0xbbfffffffc0f8000

def z1073 : W := mkw 0x742203fff0087d79 0x1d0880fffc021f5e 0x540003fff0003ffc 0x150000fffc000fff

def z1074 : W := mkw 0x542203f6f0087ff4 0x550880fdbc021ffd 0x540003fff0003ffc 0x150000fffc000fff

def z1075 : W := mkw 0xc4ee5ffde0000001 0x313b97ff78000000 0xceffcffff0000003 0xb3bff3fffc000000

def z1076 : W := mkw 0x1470492654995970 0x051c12499526565c 0xaaf0cf3e7cf9f9c3 0xeabc33cf9f3e7e70

def z1077 : W := mkw 0x6b8fb6d9ab66a68c 0x5ae3edb66ad9a9a3 0x010f30c18306060c 0x0043cc3060c18183

def z1078 : W := mkw 0x4fbb03fd4fc03781 0x53eec0ff53f00de0 0x5bff03fe0fc03fc3 0xd6ffc0ff83f00ff0

def z1079 : W := mkw 0x8bddfc000ff78280 0xa2f77f0003fde0a0 0xbbfffc000fffc7c3 0xeeffff0003fff1f0

def z1080 : W := mkw 0x6bbba3f90fe43788 0x5aeee8fe43f90de2 0xfbfff3f18ffe3fcf 0xfefffcfc63ff8ff3

def z1081 : W := mkw 0x8466fd7de0000001 0x2119bf5f78000000 0xcffffffff0000003 0xb3fffffffc000000

def z1082 : W := mkw 0x602203fbb0087ffc 0x580880feec021fff 0x540003fff0003ffc 0x150000fffc000fff

def z1083 : W := mkw 0x0033017005c01380 0x000cc05c017004e0 0x5aff03300cc039c3 0xd6bfc0cc03300e70

def z1084 : W := mkw 0xc7cefedde0000001 0x31f3bfb778000000 0x8ffffccff0000003 0xa3ffff33fc000000

def z1085 : W := mkw 0x6bbba3f90fe43788 0x5aeee8fe43f90de2 0xdffff3ff8fc63fcf 0xf7fffcffe3f18ff3

def z1086 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0x3300f3cf8f3e3e3d 0x4cc03cf3e3cf8f8f

def z1087 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0x1bff03c00fc03fc1 0x46ffc0f003f00ff0

def z1088 : W := mkw 0xe7eefffdea242409 0x39fbbfff7a890902 0xcffffffff0000003 0xb3fffffffc000000

def z1089 : W := mkw 0x8055fc0005f78000 0xa0157f00017de000 0xabfffc000fffc003 0xeaffff0003fff000

def z1090 : W := mkw 0x4bbb03f00fe43780 0x52eec0fc03f90de0 0x7bff03f00ffe3fc3 0xdeffc0fc03ff8ff0

def z1091 : W := mkw 0x04665d74e0000000 0x0119975d38000000 0xceffcf3e70000003 0xb3bff3cf9c000000

def z1092 : W := mkw 0x4bbb03f0afc03784 0x52eec0fc2bf00de1 0x5bff03f18fc03fcf 0xd6ffc0fc63f00ff3

def z1093 : W := mkw 0x87ccfe8de0000001 0x21f33fa378000000 0xcfffffcff0000003 0xb3fffff3fc000000

def z1094 : W := mkw 0xc7eefffde0000285 0x31fbbfff780000a1 0xcffffffff000060f 0xb3fffffffc000183

def z1095 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0xaffffc018fffc03f 0xebffff0063fff00f

def z1096 : W := mkw 0x4bbba3f90fc03780 0x52eee8fe43f00de0 0x5bffc3fe0fc03fc3 0xd6fff0ff83f00ff0

def z1097 : W := mkw 0x1470492654995970 0x051c12499526565c 0x5ef0cf3e7cf9f9f1 0x97bc33cf9f3e7e7c

def z1098 : W := mkw 0xc7eefffde0000001 0x31fbbfff78000000 0x4effcffff0000001 0x93bff3fffc000000

def z1099 : W := mkw 0x1011000215dbdbf4 0x040440008576f6fd 0x300000000cf9f9f0 0x4c000000033e7e7c

def z1100 : W := mkw 0x4bab03f00b403780 0x52eac0fc02d00de0 0x5bff03f003003fc3 0x96ffc0fc00c00ff0

def z1101 : W := mkw 0x8bddfe800ff7a400 0xa2f77fa003fde900 0xabfffcc00fffc603 0xeaffff3003fff180

def z1102 : W := mkw 0x8c55fc0deff78001 0xa3157f037bfde000 0xa400fc0fffffc000 0x69003f03fffff000

def z1103 : W := mkw 0x8bddfc00aff78004 0xa2f77f002bfde001 0xabfffc018fffc00f 0xeaffff0063fff003

def z1104 : W := mkw 0xab8fb6d9ab66a68c 0xaae3edb66ad9a9a3 0x010f30c18306060c 0x0043cc3060c18183

def z1105 : W := mkw 0xcbddfe890ff78001 0xb2f77fa243fde000 0xabfffc000fffc003 0xeaffff0003fff000

def z1106 : W := mkw 0xcbddfe800ff7a400 0xf2f77fa003fde900 0xabfffc000fffc003 0xeaffff0003fff000

def z1107 : W := mkw 0x8bddfc000ff78284 0xa2f77f0003fde0a1 0xabfffc000fffc60f 0xeaffff0003fff183

def z1108 : W := mkw 0x8bddfc0005d38000 0xa2f77f000174e000 0xabfffc000cf9c003 0xeaffff00033e7000

def z1109 : W := mkw 0x000514001142c050 0x000145000450b014 0xf50f3cf1f3c7c7fe 0xfd43cf3c7cf1f1ff

def z1110 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0xeffffcc18fffc003 0xfbffff3063fff000

def z1111 : W := mkw 0x0050480214994870 0x001412008526521c 0xfef0cf3e7cf9f9f3 0xffbc33cf9f3e7e7c

def z1112 : W := mkw 0x8bdcfc000eb78000 0xa2f73f0003ade000 0xabfffc000c3fc003 0xaaffff00030ff000

def z1113 : W := mkw 0xc7ee5ffde0000001 0x31fb97ff78000000 0x4fff0ffff0000003 0x93ffc3fffc000000

def z1114 : W := mkw 0x089900000ff78000 0x8226400003fde000 0x28ff00000fffc000 0xca3fc00003fff000

def z1115 : W := mkw 0x8bddfc000ff78000 0xa2f77f0003fde000 0xabfffcc18fffc60f 0xeaffff3063fff183

def z1116 : W := mkw 0xf7f8ebaf4ebd3d29 0x3dfe3aebd3af4f4a 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z1117 : W := mkw 0xc7eefffde0138001 0xb1fbbfff7804e000 0xcffffffff001c003 0xb3fffffffc007000

def z1118 : W := mkw 0xc7eefffdea242401 0x31fbbfff7a890900 0xffffffffff3e3e03 0xffffffffffcf8f80

def z1119 : W := mkw 0x8b9db4000ff78000 0xa2e76d0003fde000 0x2bff30000fffc003 0xcaffcc0003fff000

def z1120 : W := mkw 0x08d9480005d10000 0x0236520001744000 0xaaffcc000cf9c003 0xeabff300033e7000

def z1121 : W := mkw 0x2300a28b0a2c2c28 0x08c028a2c28b0b0a 0xf700ffffff3e3e3f 0xfdc03fffffcf8f8f

def z1122 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0x5aff03f00cc03fc1 0x96bfc0fc03300ff0

def z1123 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0x5aff03300cc039c3 0xd6bfc0cc03300e70

def z1124 : W := mkw 0x0bbb01700fc01380 0x02eec05c03f004e0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z1125 : W := mkw 0x83cdfc0001778000 0xa0f37f00005de000 0xabfffc0003ffc003 0xeaffff0000fff000

def z1126 : W := mkw 0x4bbb03f00fc03780 0x52eec0fc03f00de0 0xfbff0ff00fc1ffc3 0xfeffc3fc03f07ff0

def z1127 : W := mkw 0x88dd5c0005d38000 0xa23757000174e000 0xa8ffcc0000f9c000 0xaa3ff300003e7000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z8,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z9]),(1,[z0,z1,z2,z3,z10,z6]),(0,[z0,z11,z1,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z13,z6])],[(0,[z14,z0,z1,z15,z3,z4,z6]),(0,[z16,z0,z1,z2,z3,z4,z6]),(0,[z0,z17,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z18,z4,z6,z19]),(0,[z0,z1,z2,z3,z4,z6,z19]),(0,[z0,z1,z2,z3,z4,z20,z6])],[(0,[z0,z1,z2,z21,z3,z4,z6]),(0,[z0,z1,z2,z3,z22,z4,z6]),(0,[z0,z23,z1,z2,z3,z24,z6]),(0,[z0,z25,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z27,z3,z28,z4])],[(0,[z0,z1,z2,z3,z4,z6,z29]),(0,[z30,z0,z1,z2,z3,z4,z6])],[(0,[z31,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z32]),(0,[z0,z33,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z34,z4,z6,z19])],[(0,[z0,z1,z35,z2,z36,z4,z6])],[(0,[z0,z1,z2,z3,z37,z4,z6]),(0,[z0,z38,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z39,z4,z6])]],
   [[(0,[z0,z40,z1,z41,z2,z3,z4]),(0,[z42,z0,z1,z2,z3,z4,z43]),(0,[z44,z0,z1,z35,z3,z4,z6]),(0,[z0,z35,z2,z45,z3,z4,z6]),(0,[z46,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z47,z4,z6]),(0,[z0,z1,z48,z2,z3,z49,z6]),(0,[z0,z50,z1,z2,z3,z49,z6]),(0,[z0,z1,z51,z2,z3,z4,z6]),(0,[z0,z52,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z27,z3,z6,z19])],[(0,[z0,z1,z2,z53,z3,z4,z6]),(0,[z0,z1,z2,z54,z55,z4,z6]),(0,[z0,z1,z2,z56,z3,z55,z4])],[(1,[z0,z1,z2,z3,z4,z43]),(0,[z0,z1,z2,z3,z4,z57,z6]),(0,[z0,z1,z58,z2,z3,z4,z6]),(0,[z0,z59,z1,z2,z3,z4,z60]),(0,[z0,z50,z1,z2,z54,z3,z6])],[(0,[z0,z61,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z62,z4,z6])],[(0,[z0,z1,z2,z3,z4,z63,z6]),(0,[z0,z1,z2,z3,z64,z4,z6]),(0,[z0,z1,z2,z65,z3,z4,z6]),(0,[z0,z1,z66,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z67,z6]),(0,[z0,z68,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z55,z4,z6])],[(0,[z69,z0,z1,z2,z3,z4,z6]),(0,[z0,z70,z1,z41,z2,z3,z4]),(0,[z71,z0,z1,z2,z3,z4,z6]),(0,[z42,z1,z2,z72,z3,z4,z6]),(0,[z0,z1,z2,z73,z3,z4,z6]),(0,[z0,z1,z2,z74,z3,z4,z6]),(0,[z0,z1,z75,z2,z3,z4,z6]),(0,[z0,z76,z23,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z77,z6]),(0,[z0,z1,z2,z3,z4,z6,z78]),(0,[z0,z1,z2,z3,z4,z79,z6])],[(0,[z0,z1,z2,z80,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z81]),(0,[z0,z1,z2,z3,z4,z82,z6]),(0,[z0,z1,z2,z83,z3,z4,z6]),(0,[z0,z1,z2,z3,z84,z4,z6])],[(0,[z42,z0,z1,z2,z3,z4,z85]),(0,[z86,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z87,z4,z6]),(0,[z0,z1,z2,z3,z88,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z89,z6]),(0,[z0,z1,z2,z3,z90,z4,z6]),(0,[z0,z91,z1,z2,z3,z4,z6]),(0,[z0,z92,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z54,z3,z4,z93]),(1,[z0,z1,z2,z94,z4,z6])],[(1,[z0,z1,z2,z3,z4,z85])],[(0,[z0,z95,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z96,z4,z6]),(0,[z0,z97,z2,z3,z4,z6,z98]),(0,[z0,z97,z50,z1,z2,z3,z4])],[(0,[z0,z1,z35,z2,z3,z4,z99]),(0,[z0,z100,z1,z2,z87,z4,z6]),(0,[z0,z101,z1,z2,z3,z4,z6]),(0,[z0,z102,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z103,z6]),(0,[z0,z1,z2,z104,z3,z4,z6])],[(0,[z0,z1,z35,z2,z3,z105,z6]),(0,[z0,z1,z2,z106,z4,z6,z19])],[(0,[z107,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z108,z3,z4,z6])],[(0,[z0,z109,z1,z2,z3,z4,z6]),(0,[z0,z1,z110,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z111,z6]),(0,[z0,z112,z1,z2,z3,z4,z6]),(0,[z0,z100,z1,z2,z34,z4,z6]),(0,[z0,z50,z113,z1,z2,z3,z4]),(0,[z0,z1,z2,z34,z4,z6,z114]),(0,[z115,z0,z1,z2,z3,z4,z6]),(0,[z0,z116,z1,z2,z3,z4,z6])],[(0,[z0,z97,z1,z2,z3,z4,z77]),(0,[z117,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z118,z4,z6]),(0,[z0,z119,z1,z2,z3,z4,z6])],[(0,[z120,z0,z1,z2,z3,z4,z6]),(0,[z121,z1,z2,z122,z3,z4,z6]),(0,[z0,z1,z2,z123,z3,z4,z6]),(0,[z124,z0,z1,z2,z3,z4,z6]),(0,[z0,z25,z113,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z125,z4,z6]),(1,[z0,z1,z2,z126,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z127])],[(0,[z0,z1,z2,z3,z4,z128,z6]),(0,[z0,z1,z2,z3,z129,z4,z6]),(0,[z44,z14,z0,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z130,z131,z6]),(0,[z0,z1,z2,z3,z132,z4,z6])],[(0,[z0,z1,z133,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z134,z6]),(0,[z0,z1,z2,z3,z4,z135,z6])],[(0,[z0,z136,z1,z41,z2,z4,z6]),(0,[z0,z97,z1,z2,z3,z4,z6]),(0,[z0,z137,z1,z138,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z139]),(0,[z0,z1,z2,z3,z4,z6,z140])],[(0,[z0,z1,z2,z3,z4,z141,z6])]],
   [[(0,[z142,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z143,z4,z6]),(0,[z0,z1,z35,z2,z3,z4,z7]),(0,[z0,z1,z2,z144,z3,z4,z6])],[(0,[z0,z1,z35,z2,z3,z10,z6]),(0,[z145,z0,z1,z2,z3,z4,z6]),(0,[z0,z146,z1,z2,z3,z24,z6]),(0,[z0,z1,z2,z147,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z12]),(0,[z0,z1,z48,z2,z3,z130,z6]),(0,[z0,z50,z1,z2,z3,z130,z6])],[(0,[z0,z1,z2,z3,z148,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z149]),(1,[z0,z1,z2,z3,z150,z6]),(0,[z0,z1,z2,z151,z3,z4,z6]),(0,[z152,z0,z1,z2,z3,z4,z6]),(0,[z0,z23,z1,z2,z3,z153,z6]),(1,[z0,z1,z2,z3,z154,z4]),(0,[z0,z1,z155,z2,z3,z4,z6])],[(0,[z156,z1,z2,z3,z131,z4,z6]),(0,[z0,z157,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z158,z6]),(0,[z0,z1,z2,z3,z106,z4,z6]),(1,[z0,z1,z2,z159,z4,z114])],[(0,[z0,z1,z2,z3,z4,z6,z160]),(0,[z0,z1,z2,z3,z4,z161,z6]),(0,[z0,z162,z1,z2,z3,z4,z6]),(0,[z0,z146,z1,z2,z3,z28,z6])],[(0,[z0,z1,z2,z3,z4,z163,z6]),(1,[z0,z70,z1,z2,z3,z4]),(0,[z42,z0,z1,z72,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z164,z6]),(0,[z0,z1,z2,z3,z4,z165,z6]),(1,[z0,z1,z48,z3,z130,z6])],[(0,[z0,z1,z2,z3,z131,z4,z6]),(0,[z166,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z167,z4,z6]),(0,[z0,z1,z2,z3,z168,z4,z6]),(0,[z0,z1,z2,z169,z3,z4,z6]),(0,[z0,z170,z1,z2,z3,z4,z6])],[(0,[z171,z0,z172,z2,z3,z4,z6]),(0,[z0,z173,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z174,z3,z4,z6]),(0,[z0,z100,z1,z2,z106,z4,z6]),(0,[z0,z1,z2,z27,z3,z4,z60]),(0,[z0,z175,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z176,z4,z6])]],
   [[(0,[z0,z1,z2,z177,z3,z4,z6]),(0,[z0,z76,z1,z2,z3,z6,z178])],[(0,[z179,z0,z1,z2,z3,z4,z6]),(0,[z156,z180,z1,z2,z3,z4,z6]),(1,[z180,z1,z2,z3,z181,z6]),(0,[z182,z0,z113,z1,z2,z3,z4]),(1,[z0,z1,z2,z36,z4,z6]),(0,[z183,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z184,z6]),(0,[z0,z1,z2,z3,z185,z4,z6]),(0,[z0,z1,z2,z3,z4,z186,z6])],[(0,[z0,z1,z2,z3,z4,z187,z6]),(0,[z0,z2,z188,z3,z87,z4,z6]),(0,[z0,z1,z189,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z190,z6]),(0,[z0,z1,z2,z191,z3,z4,z6]),(0,[z0,z1,z48,z3,z130,z4,z6]),(0,[z0,z1,z192,z2,z3,z4,z6])],[(0,[z0,z193,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z194,z4,z6]),(0,[z0,z59,z1,z2,z195,z4,z6])],[(0,[z196,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z197,z3,z87,z4]),(0,[z0,z198,z1,z2,z3,z4,z6])],[(0,[z199,z0,z1,z2,z3,z4,z6]),(0,[z121,z0,z100,z1,z2,z4,z6]),(0,[z0,z76,z100,z1,z2,z4,z6]),(0,[z200,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z201,z3,z4,z6]),(0,[z0,z1,z2,z4,z202,z6,z98])],[(1,[z171,z41,z2,z3,z4,z6]),(0,[z171,z1,z41,z2,z3,z4,z6]),(0,[z42,z0,z1,z2,z3,z4,z6]),(0,[z121,z0,z1,z2,z203,z4,z6]),(0,[z0,z1,z2,z204,z3,z4,z6]),(0,[z205,z0,z1,z2,z3,z4,z6]),(0,[z0,z206,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z154,z4,z6]),(0,[z0,z1,z2,z3,z207,z4,z6]),(0,[z0,z1,z3,z4,z208,z6,z60]),(0,[z0,z1,z2,z3,z209,z4,z6])]],
   [[(1,[z182,z1,z2,z3,z4,z164]),(0,[z0,z210,z1,z2,z55,z4,z6]),(0,[z0,z1,z2,z3,z4,z211,z6])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z212,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z213,z6]),(0,[z42,z0,z214,z1,z3,z4,z6]),(0,[z0,z1,z215,z2,z3,z4,z6]),(0,[z0,z113,z1,z2,z3,z4,z208]),(0,[z0,z76,z1,z2,z3,z55,z6])],[(0,[z0,z1,z2,z216,z3,z4,z6]),(0,[z0,z1,z2,z3,z217,z4,z6]),(0,[z0,z1,z2,z3,z4,z218,z6]),(0,[z0,z210,z1,z2,z87,z4,z6]),(0,[z219,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z220,z6]),(0,[z0,z1,z2,z3,z4,z221,z6]),(0,[z0,z1,z2,z3,z222,z4,z6])],[(0,[z0,z1,z2,z3,z4,z223,z6])],[(0,[z172,z1,z41,z2,z3,z4,z6]),(0,[z0,z1,z2,z122,z3,z4,z6]),(0,[z224,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z150,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z225]),(0,[z0,z1,z2,z3,z4,z6,z226])],[(0,[z0,z1,z2,z227,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z7]),(1,[z0,z1,z2,z3,z4,z99]),(0,[z0,z210,z1,z2,z34,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z228]),(0,[z0,z1,z2,z126,z3,z4,z6])],[(0,[z229,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z203,z4,z6]),(0,[z1,z2,z3,z131,z4,z181,z6]),(0,[z0,z25,z1,z2,z3,z230,z6])]],
   [[(0,[z0,z231,z1,z2,z3,z4,z6]),(0,[z0,z232,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z150,z87,z6]),(0,[z0,z1,z2,z4,z184,z153,z6]),(0,[z0,z23,z1,z2,z3,z49,z6]),(0,[z0,z137,z1,z2,z3,z4,z233])],[(0,[z42,z0,z1,z2,z234,z4,z6]),(0,[z0,z1,z2,z235,z3,z4,z6]),(0,[z0,z97,z1,z2,z3,z4,z60]),(0,[z0,z137,z1,z2,z3,z67,z6]),(0,[z0,z1,z2,z3,z4,z6,z236])],[(0,[z0,z1,z2,z3,z237,z4,z6]),(0,[z0,z23,z1,z2,z54,z3,z6]),(0,[z0,z97,z113,z2,z3,z4,z6])],[(0,[z238,z0,z172,z2,z3,z4,z6]),(1,[z0,z1,z2,z234,z4,z6]),(1,[z0,z210,z2,z87,z4,z6])],[(0,[z0,z1,z2,z3,z4,z153,z6]),(1,[z0,z1,z2,z3,z4,z239]),(0,[z240,z0,z1,z2,z3,z4,z6])],[(0,[z241,z0,z1,z2,z3,z4,z6]),(0,[z0,z242,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z243,z4,z6]),(0,[z0,z214,z1,z35,z3,z4,z6])],[(1,[z0,z244,z1,z2,z4,z6]),(0,[z0,z1,z2,z245,z3,z4,z6])],[]],
   [[(0,[z0,z1,z2,z3,z246,z4,z6]),(0,[z0,z1,z2,z3,z4,z164,z60]),(0,[z0,z146,z1,z2,z3,z153,z6]),(0,[z0,z247,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z84,z6])],[(0,[z0,z248,z1,z2,z3,z4,z6]),(0,[z0,z249,z1,z2,z3,z4,z6]),(0,[z250,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z251,z3,z4,z6]),(1,[z0,z214,z35,z3,z4,z6]),(0,[z0,z210,z100,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z252,z6]),(0,[z0,z1,z2,z3,z4,z6,z233])],[(0,[z0,z1,z2,z3,z253,z4,z6]),(1,[z0,z1,z2,z254,z4,z6]),(0,[z0,z2,z3,z4,z77,z6,z98]),(1,[z0,z1,z2,z3,z4,z220])],[(0,[z0,z1,z2,z3,z255,z6,z98]),(0,[z0,z1,z2,z3,z4,z256,z6])],[(0,[z0,z257,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z258,z6]),(0,[z0,z1,z259,z2,z3,z4,z153])],[],[(1,[z42,z1,z72,z3,z4,z6]),(0,[z0,z1,z2,z203,z106,z4,z6]),(0,[z0,z97,z1,z2,z159,z3,z4]),(0,[z0,z260,z1,z2,z3,z4,z6]),(0,[z0,z1,z261,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z85]),(0,[z262,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z181,z6]),(0,[z0,z210,z1,z2,z106,z4,z6]),(0,[z0,z1,z263,z2,z3,z87,z4]),(0,[z0,z11,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z201,z4,z6,z98]),(0,[z0,z1,z2,z3,z255,z4,z6])],[(0,[z0,z1,z2,z264,z3,z4,z6]),(0,[z0,z40,z1,z2,z3,z4,z6]),(0,[z0,z1,z265,z2,z3,z4,z6]),(0,[z0,z266,z1,z2,z3,z4,z6]),(0,[z0,z267,z1,z2,z3,z4,z6]),(0,[z0,z268,z1,z2,z3,z4,z6]),(0,[z0,z23,z1,z2,z3,z28,z6]),(0,[z0,z1,z2,z269,z3,z4,z6]),(0,[z0,z270,z1,z2,z3,z4,z6])],[(0,[z0,z271,z1,z2,z3,z4,z6]),(0,[z180,z0,z146,z1,z2,z3,z6]),(0,[z250,z1,z2,z3,z4,z6,z272]),(0,[z1,z2,z3,z4,z164,z6,z272]),(0,[z0,z1,z2,z3,z4,z202,z6]),(0,[z273,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z274,z3,z4,z6])],[(0,[z42,z0,z1,z2,z275,z4,z6]),(0,[z42,z0,z1,z2,z3,z276,z6]),(0,[z0,z1,z2,z159,z3,z4,z178])],[(0,[z0,z1,z2,z3,z4,z277,z6])],[(0,[z0,z1,z278,z2,z3,z4,z6]),(1,[z0,z1,z2,z275,z4,z6]),(1,[z0,z1,z2,z3,z276,z6]),(0,[z250,z0,z1,z2,z3,z4,z164]),(0,[z0,z1,z2,z3,z4,z279,z6])],[(0,[z0,z70,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z280]),(1,[z0,z1,z2,z3,z4,z233]),(0,[z0,z1,z2,z3,z130,z6,z19]),(0,[z0,z76,z1,z2,z4,z6,z114])],[(0,[z0,z1,z281,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z282,z6]),(0,[z0,z1,z2,z3,z4,z6,z283]),(0,[z0,z1,z2,z3,z4,z6,z178])]],
   [[(1,[z0,z136,z1,z2,z4,z6]),(0,[z42,z0,z1,z15,z3,z4,z6]),(0,[z0,z284,z1,z2,z3,z4,z6]),(0,[z0,z210,z2,z3,z87,z4,z6]),(0,[z0,z11,z1,z48,z3,z4,z6]),(0,[z0,z285,z1,z2,z3,z4,z6])],[(0,[z0,z1,z35,z2,z3,z4,z6]),(0,[z0,z23,z1,z2,z3,z130,z6]),(1,[z0,z1,z2,z201,z4,z6]),(1,[z0,z11,z1,z3,z49,z6])],[(0,[z0,z1,z2,z3,z286,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z287]),(0,[z0,z288,z1,z2,z3,z4,z6]),(0,[z0,z289,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z54,z34,z4,z6]),(0,[z0,z1,z2,z3,z130,z4,z6]),(0,[z0,z1,z2,z159,z3,z4,z114]),(0,[z0,z1,z2,z290,z3,z4,z6])],[(0,[z0,z1,z2,z291,z3,z4,z6]),(0,[z0,z1,z2,z292,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z293,z6]),(0,[z0,z137,z1,z2,z3,z294,z6]),(0,[z0,z1,z138,z2,z34,z4,z6]),(0,[z0,z1,z2,z295,z3,z4,z6])],[(0,[z121,z0,z210,z1,z2,z4,z6]),(0,[z0,z296,z1,z2,z3,z4,z6]),(0,[z297,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z298]),(0,[z0,z1,z2,z299,z3,z4,z6])],[(0,[z0,z1,z300,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z181,z49,z6]),(0,[z0,z1,z2,z301,z3,z4,z6]),(0,[z182,z0,z1,z2,z3,z4,z164]),(0,[z0,z302,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z27,z3,z6,z178]),(0,[z0,z50,z1,z2,z27,z3,z6])],[(0,[z0,z303,z1,z2,z3,z4,z6]),(0,[z0,z146,z1,z2,z3,z49,z6]),(0,[z304,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z18,z4,z6,z114]),(0,[z0,z1,z2,z3,z4,z6,z114])],[(0,[z0,z1,z305,z2,z3,z4,z6]),(0,[z306,z0,z1,z2,z3,z4,z6]),(0,[z0,z270,z1,z2,z27,z4,z6])]],
   [[(0,[z0,z146,z1,z2,z54,z3,z6]),(1,[z0,z23,z2,z3,z24,z6]),(0,[z0,z97,z1,z2,z3,z28,z4]),(0,[z0,z11,z1,z2,z3,z4,z220]),(0,[z0,z307,z1,z2,z3,z4,z6]),(0,[z0,z50,z1,z2,z94,z4,z6]),(1,[z0,z1,z2,z308,z4,z6])],[(0,[z0,z1,z2,z3,z4,z309,z6])],[(0,[z0,z1,z2,z3,z4,z6,z310]),(0,[z44,z0,z214,z2,z3,z4,z6]),(0,[z0,z311,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z130,z4,z49,z6]),(0,[z0,z1,z2,z312,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z313]),(1,[z212,z1,z2,z203,z4,z6]),(0,[z180,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z314,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z315]),(0,[z0,z1,z2,z3,z316,z4,z6]),(0,[z0,z1,z2,z54,z3,z317,z4]),(0,[z0,z1,z2,z3,z28,z4,z114])],[(0,[z318,z0,z1,z2,z3,z4,z6]),(0,[z0,z319,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z93]),(0,[z0,z320,z1,z2,z3,z4,z6])],[(0,[z0,z321,z1,z2,z3,z4,z6]),(0,[z0,z137,z1,z2,z3,z4,z6]),(0,[z0,z1,z322,z2,z3,z4,z6]),(0,[z0,z1,z323,z2,z3,z4,z208]),(0,[z324,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z325]),(0,[z0,z1,z2,z3,z4,z326,z6]),(0,[z0,z327,z1,z2,z3,z4,z6]),(0,[z0,z328,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z49,z6,z19]),(0,[z0,z1,z2,z3,z4,z329,z6]),(0,[z0,z1,z2,z27,z3,z55,z6])]],
   [[(0,[z171,z0,z41,z2,z3,z4,z6]),(0,[z0,z1,z2,z234,z3,z4,z6]),(0,[z330,z0,z1,z2,z3,z4,z6]),(0,[z331,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z332])],[(0,[z156,z0,z146,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z333]),(0,[z0,z1,z2,z334,z3,z4,z6]),(0,[z0,z1,z2,z3,z335,z4,z6]),(0,[z336,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z35,z2,z254,z4,z6])],[(0,[z0,z1,z2,z54,z106,z4,z6]),(0,[z0,z1,z2,z337,z3,z4,z6]),(0,[z0,z1,z2,z159,z3,z4,z6]),(0,[z338,z0,z1,z2,z3,z4,z6])],[(0,[z0,z339,z1,z2,z3,z4,z6]),(0,[z0,z1,z138,z2,z106,z4,z6])],[(0,[z0,z340,z1,z2,z3,z4,z6]),(0,[z0,z214,z35,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z341,z6]),(0,[z0,z1,z2,z3,z4,z6,z342])],[(0,[z0,z343,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z344,z4,z6]),(0,[z345,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z346]),(1,[z0,z1,z2,z132,z4,z6])],[(0,[z212,z0,z1,z2,z122,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z0,z1,z2,z347,z3,z4,z6]),(0,[z0,z1,z2,z3,z348,z4,z6])]],
   [[(0,[z180,z0,z1,z2,z3,z131,z6]),(0,[z0,z1,z2,z3,z4,z6,z349]),(0,[z0,z1,z2,z106,z4,z6,z114]),(0,[z0,z11,z1,z2,z47,z4,z6]),(0,[z0,z50,z1,z2,z3,z4,z114])],[(0,[z0,z1,z41,z2,z3,z4,z6]),(0,[z0,z350,z1,z2,z3,z4,z6]),(0,[z0,z351,z1,z2,z3,z87,z6]),(1,[z0,z1,z2,z3,z294,z6]),(0,[z0,z137,z1,z2,z3,z4,z239]),(0,[z0,z1,z2,z3,z28,z6,z19]),(0,[z0,z1,z2,z3,z55,z28,z6])],[(0,[z0,z244,z1,z41,z2,z4,z6]),(0,[z352,z0,z1,z2,z3,z4,z6]),(0,[z353,z0,z1,z2,z3,z4,z6]),(0,[z354,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z355,z3,z4,z6]),(0,[z0,z1,z2,z55,z4,z6,z19]),(0,[z0,z1,z2,z356,z3,z4,z6])],[(0,[z0,z1,z2,z3,z357,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z358]),(0,[z0,z25,z1,z2,z3,z4,z114]),(0,[z0,z359,z1,z2,z3,z4,z6])],[(0,[z360,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z361]),(0,[z0,z1,z2,z3,z4,z362,z6])],[(0,[z363,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z364,z4,z6]),(0,[z0,z1,z2,z3,z28,z4,z6])],[(0,[z0,z1,z365,z2,z3,z4,z6]),(0,[z0,z366,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z367,z4,z6]),(1,[z0,z1,z2,z195,z4,z6]),(0,[z0,z1,z368,z2,z3,z4,z6])],[(0,[z0,z369,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z370,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z371]),(0,[z0,z146,z1,z2,z3,z130,z6]),(0,[z0,z1,z372,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z13,z6])]],
   [[(0,[z0,z1,z2,z3,z373,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z374]),(0,[z0,z1,z2,z375,z3,z4,z6]),(0,[z0,z1,z2,z54,z3,z6,z178])],[(0,[z0,z1,z2,z3,z55,z130,z6])],[(0,[z156,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z376]),(0,[z0,z1,z2,z3,z4,z6,z377])],[(0,[z0,z1,z2,z378,z3,z4,z6]),(0,[z0,z379,z1,z2,z3,z4,z6]),(0,[z0,z380,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z294,z4,z6])],[(0,[z238,z0,z41,z2,z3,z4,z6]),(0,[z0,z1,z2,z381,z3,z4,z6]),(1,[z0,z1,z2,z197,z3,z4]),(0,[z0,z1,z2,z3,z55,z4,z382])],[(1,[z156,z1,z2,z3,z131,z6]),(0,[z0,z97,z1,z2,z3,z4,z98]),(0,[z0,z1,z2,z3,z383,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z384])],[(0,[z238,z172,z1,z2,z3,z4,z6])],[]],
   [[(0,[z0,z1,z323,z3,z4,z208,z6]),(0,[z0,z1,z2,z385,z3,z4,z6])],[(0,[z386,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z387,z6]),(0,[z0,z388,z1,z2,z3,z4,z6]),(0,[z0,z1,z48,z2,z3,z4,z6]),(0,[z0,z389,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z390,z4,z6]),(0,[z0,z50,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z391,z6]),(0,[z0,z1,z392,z2,z3,z4,z6]),(0,[z0,z1,z393,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z394,z6]),(0,[z0,z1,z2,z54,z3,z55,z6]),(0,[z0,z395,z1,z2,z3,z4,z6])],[(0,[z250,z0,z97,z1,z2,z3,z4]),(0,[z0,z1,z396,z2,z3,z4,z6])],[(0,[z0,z146,z2,z3,z4,z153,z6]),(0,[z0,z25,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z397,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z398,z6]),(0,[z0,z1,z2,z3,z399,z4,z6]),(0,[z0,z1,z400,z2,z3,z4,z6])],[(0,[z171,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z401,z4,z6]),(0,[z0,z1,z323,z2,z3,z4,z6]),(0,[z0,z1,z2,z159,z4,z6,z19]),(0,[z0,z402,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z230,z6])],[(0,[z0,z1,z2,z403,z3,z4,z6]),(0,[z156,z0,z1,z2,z3,z131,z6]),(0,[z0,z404,z1,z2,z3,z4,z6]),(0,[z0,z25,z1,z2,z159,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z405,z4,z6]),(0,[z0,z406,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z407]),(0,[z0,z59,z1,z323,z3,z4,z6]),(1,[z0,z1,z2,z56,z3,z4])],[(0,[z0,z1,z2,z3,z408,z4,z6]),(0,[z0,z409,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z410]),(0,[z0,z1,z2,z3,z4,z411,z6]),(0,[z0,z50,z76,z1,z2,z3,z6])],[(0,[z42,z0,z133,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z412,z6]),(0,[z0,z1,z2,z3,z413,z6,z98]),(0,[z0,z414,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z60])],[(0,[z0,z1,z2,z3,z415,z4,z6]),(0,[z0,z1,z2,z3,z258,z4,z6]),(0,[z0,z1,z2,z3,z416,z4,z6]),(0,[z0,z1,z2,z3,z417,z4,z6]),(0,[z418,z0,z1,z2,z3,z4,z6])],[(1,[z0,z133,z2,z3,z4,z6]),(0,[z419,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z420,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z421,z6]),(0,[z0,z1,z2,z3,z422,z4,z6]),(1,[z0,z97,z2,z3,z4,z98]),(1,[z0,z50,z1,z2,z27,z3])],[(0,[z0,z1,z2,z3,z423,z4,z6]),(0,[z42,z0,z1,z2,z3,z258,z6]),(0,[z0,z424,z1,z2,z4,z153,z6]),(0,[z0,z23,z1,z2,z27,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z425])],[(0,[z0,z1,z2,z426,z3,z4,z6]),(1,[z250,z1,z2,z3,z4,z272]),(0,[z0,z427,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z428,z3,z4,z6]),(0,[z429,z0,z1,z2,z3,z4,z6]),(0,[z430,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z0,z214,z172,z2,z3,z4,z6]),(0,[z182,z250,z1,z2,z3,z4,z6]),(0,[z0,z431,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z413,z4,z6]),(0,[z0,z1,z2,z432,z3,z4,z6]),(0,[z433,z0,z1,z2,z3,z4,z6])]],
   [[(1,[z0,z1,z434,z3,z4,z6]),(0,[z0,z1,z2,z435,z3,z4,z6]),(0,[z0,z1,z2,z36,z3,z4,z6]),(0,[z0,z210,z76,z1,z2,z4,z6]),(0,[z0,z59,z1,z2,z3,z436,z6])],[(0,[z0,z1,z2,z3,z437,z4,z6]),(0,[z0,z137,z1,z2,z34,z4,z6]),(0,[z0,z1,z2,z3,z4,z208,z114])],[(0,[z438,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z439]),(0,[z0,z440,z1,z2,z3,z4,z6])],[(0,[z441,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z442,z6]),(0,[z0,z443,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z444,z3,z4,z6]),(0,[z182,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z445,z2,z3,z4,z6]),(0,[z0,z446,z1,z2,z3,z4,z6]),(0,[z447,z0,z1,z2,z3,z4,z6])],[(0,[z42,z0,z369,z2,z3,z4,z6]),(0,[z448,z0,z1,z2,z3,z4,z6])],[(0,[z0,z113,z1,z2,z3,z4,z77]),(0,[z0,z1,z2,z3,z449,z4,z6]),(0,[z0,z1,z450,z2,z3,z4,z6])],[(1,[z0,z369,z2,z3,z4,z6]),(0,[z121,z0,z1,z2,z122,z4,z6]),(0,[z0,z451,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z452,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z453,z6]),(0,[z454,z0,z1,z2,z3,z4,z6]),(0,[z0,z455,z1,z2,z3,z4,z6]),(0,[z0,z1,z456,z2,z3,z4,z6])],[(0,[z14,z1,z15,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z413,z6])],[(0,[z238,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z457,z4,z6]),(0,[z0,z1,z2,z458,z3,z4,z6])],[(0,[z171,z238,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z130,z181,z6]),(0,[z0,z459,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z460]),(0,[z0,z1,z2,z461,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z93]),(0,[z0,z1,z2,z3,z4,z6,z462]),(0,[z0,z25,z1,z2,z18,z4,z6])],[(0,[z0,z1,z2,z3,z4,z463,z6]),(0,[z14,z0,z1,z72,z3,z4,z6]),(0,[z0,z146,z23,z2,z3,z4,z6]),(1,[z0,z1,z2,z4,z202,z6]),(0,[z0,z1,z2,z3,z4,z464,z6]),(0,[z0,z1,z2,z3,z317,z4,z6]),(0,[z0,z1,z2,z3,z465,z4,z6])],[(0,[z0,z1,z2,z3,z466,z4,z6]),(0,[z0,z100,z1,z2,z188,z4,z6]),(0,[z0,z113,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z47,z4,z6]),(0,[z0,z1,z2,z3,z4,z49,z6]),(0,[z0,z1,z2,z3,z467,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z468]),(0,[z0,z1,z469,z2,z3,z4,z6])],[(0,[z0,z1,z2,z72,z3,z4,z6]),(0,[z0,z1,z2,z470,z3,z4,z6]),(0,[z0,z1,z471,z2,z3,z4,z6]),(0,[z0,z1,z2,z56,z3,z4,z6]),(0,[z472,z0,z1,z2,z3,z4,z6])],[(1,[z0,z100,z2,z188,z4,z6]),(0,[z0,z2,z3,z24,z4,z153,z6]),(1,[z0,z1,z2,z3,z255,z6]),(0,[z473,z0,z1,z2,z3,z4,z6]),(0,[z0,z474,z1,z2,z3,z4,z6])]],
   [[(0,[z475,z0,z1,z2,z3,z4,z6]),(0,[z0,z76,z1,z2,z3,z6,z19]),(0,[z0,z1,z2,z3,z28,z4,z178])],[(0,[z0,z1,z323,z2,z3,z4,z60]),(1,[z0,z1,z2,z3,z4,z382])],[(0,[z476,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z477,z4,z6]),(0,[z0,z1,z2,z34,z122,z4,z6]),(0,[z0,z1,z2,z3,z478,z4,z6]),(1,[z0,z424,z1,z2,z4,z6]),(0,[z0,z137,z1,z2,z106,z4,z6]),(0,[z0,z1,z2,z3,z4,z208,z6]),(0,[z0,z1,z2,z3,z4,z6,z479])],[(0,[z0,z214,z1,z2,z3,z4,z6]),(0,[z0,z480,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z55,z49,z6]),(0,[z0,z1,z2,z3,z18,z4,z208])],[(0,[z121,z0,z1,z2,z3,z4,z6]),(0,[z180,z0,z1,z2,z3,z181,z6]),(0,[z0,z76,z1,z2,z3,z4,z6])],[(1,[z0,z409,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z24,z4,z6]),(0,[z0,z481,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z482,z4,z6])],[(0,[z14,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z483]),(0,[z0,z1,z2,z3,z4,z67,z6]),(0,[z0,z1,z2,z3,z484,z4,z6])],[(0,[z0,z1,z2,z485,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z436,z6])]],
   [[(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z486,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z487]),(0,[z0,z1,z2,z488,z3,z4,z6])],[(0,[z0,z1,z2,z3,z489,z4,z6]),(0,[z0,z1,z490,z2,z3,z4,z6]),(0,[z0,z25,z1,z2,z55,z4,z6]),(0,[z0,z1,z2,z3,z491,z4,z6])],[(0,[z0,z1,z2,z3,z4,z43,z6]),(1,[z44,z0,z45,z3,z4,z6]),(0,[z0,z1,z2,z3,z154,z4,z153]),(0,[z0,z492,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z493,z4,z6]),(0,[z0,z1,z2,z3,z494,z4,z6]),(1,[z0,z1,z138,z34,z4,z6]),(1,[z0,z1,z323,z3,z4,z208]),(0,[z0,z76,z1,z2,z54,z4,z6])],[(0,[z0,z1,z2,z495,z3,z4,z6]),(0,[z0,z1,z2,z45,z3,z4,z6]),(0,[z0,z146,z1,z2,z27,z3,z6]),(0,[z0,z1,z2,z496,z3,z4,z6])],[(0,[z497,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z0,z1,z498,z2,z3,z4,z6]),(0,[z0,z499,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z500,z3,z4,z6]),(0,[z0,z50,z1,z2,z3,z4,z178])],[(0,[z0,z1,z2,z501,z3,z4,z6]),(0,[z502,z0,z1,z2,z3,z4,z6])],[(0,[z0,z409,z1,z41,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z503]),(0,[z0,z1,z2,z3,z4,z208,z164]),(0,[z504,z0,z1,z2,z3,z4,z6]),(0,[z505,z0,z1,z2,z3,z4,z6])],[(0,[z0,z506,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z34,z3,z4,z6]),(0,[z0,z507,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z508]),(0,[z0,z1,z2,z159,z3,z18,z4]),(0,[z0,z25,z1,z2,z3,z4,z178])]],
   [[(0,[z1,z15,z2,z72,z3,z4,z6]),(0,[z0,z100,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z509,z4,z6])],[(0,[z0,z1,z2,z3,z510,z4,z6]),(0,[z0,z1,z2,z3,z511,z4,z6]),(0,[z44,z0,z1,z2,z3,z4,z6]),(0,[z0,z351,z1,z2,z3,z4,z6]),(0,[z0,z23,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z512,z4,z6]),(0,[z0,z1,z2,z27,z3,z4,z208]),(1,[z0,z1,z2,z3,z317,z4])],[(0,[z0,z1,z513,z2,z3,z4,z6])],[(0,[z514,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z515,z4,z6]),(0,[z0,z1,z15,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z516]),(0,[z0,z100,z1,z2,z159,z4,z6])],[(0,[z44,z0,z1,z45,z3,z4,z6]),(0,[z0,z11,z1,z2,z3,z130,z6])],[(0,[z0,z1,z2,z3,z517,z4,z6]),(0,[z0,z1,z518,z2,z3,z4,z6]),(0,[z0,z519,z1,z2,z3,z4,z6]),(0,[z0,z260,z1,z2,z3,z18,z6])],[(0,[z0,z1,z2,z3,z4,z6,z520]),(0,[z0,z521,z1,z2,z3,z4,z6])],[(0,[z0,z1,z522,z2,z3,z4,z6]),(0,[z0,z1,z523,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z105,z4,z6]),(0,[z0,z1,z2,z524,z3,z4,z6])]],
   [[(0,[z0,z1,z525,z2,z3,z4,z6]),(0,[z212,z1,z2,z3,z203,z4,z6]),(0,[z0,z1,z2,z3,z4,z526,z6]),(0,[z0,z1,z2,z527,z3,z4,z6]),(0,[z0,z113,z1,z2,z3,z4,z60]),(0,[z0,z1,z2,z3,z4,z6,z528]),(0,[z0,z1,z529,z2,z3,z4,z6]),(0,[z530,z0,z1,z2,z3,z4,z6])],[(0,[z0,z531,z1,z2,z3,z4,z6]),(0,[z0,z532,z1,z2,z3,z4,z6]),(0,[z0,z533,z1,z2,z3,z4,z6]),(0,[z0,z1,z534,z2,z3,z4,z6]),(0,[z0,z535,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z28,z18,z4]),(0,[z0,z1,z2,z94,z3,z4,z6]),(0,[z0,z1,z2,z3,z536,z4,z6])],[(0,[z0,z1,z2,z537,z3,z4,z6]),(0,[z0,z1,z2,z538,z3,z4,z6]),(0,[z0,z539,z1,z2,z3,z4,z6])],[(1,[z0,z40,z1,z2,z3,z4]),(0,[z540,z0,z1,z2,z3,z4,z6])],[(0,[z541,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z122,z106,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z542]),(0,[z0,z11,z1,z2,z543,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z544]),(0,[z0,z1,z2,z3,z254,z4,z6]),(0,[z0,z210,z1,z2,z188,z4,z6]),(1,[z0,z25,z1,z2,z18,z4]),(0,[z0,z1,z545,z2,z3,z4,z6])],[(0,[z0,z1,z2,z546,z3,z4,z6]),(1,[z0,z1,z2,z4,z184,z6]),(0,[z0,z1,z2,z3,z4,z114,z60]),(0,[z0,z547,z1,z2,z3,z4,z6]),(0,[z0,z548,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z272,z60]),(0,[z0,z549,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z550,z4,z6])]],
   [[(0,[z0,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z26,z6])],[(0,[z551,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z552,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z553,z6]),(1,[z0,z1,z2,z3,z28,z178])],[(0,[z554,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z555,z6]),(0,[z0,z556,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z557,z6])],[(0,[z0,z1,z558,z2,z3,z4,z6]),(0,[z0,z559,z1,z2,z3,z4,z6]),(0,[z0,z97,z1,z2,z3,z4,z208]),(0,[z0,z1,z2,z3,z18,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z560]),(0,[z0,z1,z2,z561,z3,z4,z6]),(0,[z0,z1,z562,z2,z3,z4,z6]),(1,[z0,z1,z263,z2,z3,z4])],[(0,[z0,z563,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z564,z3,z4,z6]),(0,[z0,z113,z1,z2,z159,z3,z4]),(0,[z0,z50,z1,z2,z3,z18,z4])],[(1,[z121,z1,z2,z122,z4,z6]),(0,[z0,z1,z2,z565,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z98]),(0,[z0,z566,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z567]),(0,[z0,z1,z2,z55,z4,z6,z114]),(0,[z568,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z569,z2,z3,z4,z6]),(0,[z0,z570,z1,z2,z3,z4,z6]),(0,[z0,z100,z1,z2,z18,z4,z6]),(0,[z0,z23,z2,z3,z24,z4,z6]),(0,[z0,z1,z2,z3,z571,z4,z6]),(0,[z0,z1,z2,z3,z572,z4,z6]),(0,[z0,z573,z1,z2,z3,z4,z6]),(0,[z0,z574,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z214,z41,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z275,z4,z6]),(0,[z0,z1,z2,z575,z3,z4,z6]),(0,[z576,z0,z1,z2,z3,z4,z6]),(0,[z0,z577,z1,z2,z3,z4,z6]),(0,[z0,z25,z1,z2,z3,z18,z4])],[(0,[z0,z1,z2,z3,z4,z6,z272]),(0,[z0,z1,z2,z578,z3,z4,z6])],[],[(0,[z212,z0,z100,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z0,z1,z2,z579,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z580])],[(1,[z0,z109,z1,z2,z3,z6]),(0,[z212,z0,z1,z2,z203,z4,z6]),(0,[z0,z1,z581,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z582,z4,z6])],[(0,[z583,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z584,z2,z3,z4,z6]),(0,[z44,z0,z2,z45,z3,z4,z6]),(0,[z0,z585,z1,z2,z3,z4,z6]),(0,[z0,z586,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z587,z4,z6]),(0,[z0,z1,z2,z3,z4,z208,z178])],[(0,[z0,z1,z2,z588,z3,z4,z6]),(0,[z0,z1,z589,z2,z3,z4,z6]),(0,[z182,z0,z97,z1,z2,z3,z4]),(0,[z0,z97,z25,z1,z2,z3,z4])],[(1,[z69,z0,z1,z3,z4,z6]),(0,[z0,z1,z434,z2,z3,z4,z6]),(0,[z0,z136,z1,z2,z3,z4,z6]),(0,[z0,z146,z1,z2,z3,z4,z6])]],
   [[(0,[z590,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z591,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z592,z6]),(0,[z0,z210,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z593,z6])],[(0,[z594,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z595]),(0,[z0,z1,z2,z3,z596,z4,z6]),(0,[z0,z1,z2,z27,z3,z4,z6])],[(0,[z0,z41,z2,z45,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z597,z6]),(0,[z0,z1,z2,z3,z598,z4,z6]),(1,[z0,z1,z2,z3,z436,z6])],[(0,[z599,z0,z1,z2,z3,z4,z6]),(0,[z212,z121,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z600,z4,z6]),(0,[z0,z210,z1,z2,z159,z4,z6]),(0,[z0,z601,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z308,z4,z6])],[(0,[z180,z0,z23,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z602]),(0,[z603,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z604,z6]),(0,[z0,z605,z1,z2,z3,z4,z6])],[(0,[z0,z100,z1,z2,z55,z4,z6]),(1,[z0,z1,z2,z54,z55,z6])],[(0,[z0,z1,z2,z3,z4,z606,z6])],[(0,[z0,z1,z607,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z608]),(0,[z0,z146,z76,z1,z2,z3,z6]),(0,[z0,z113,z1,z2,z3,z28,z4]),(0,[z0,z59,z1,z2,z3,z4,z208]),(0,[z0,z609,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z382])]],
   [[(0,[z0,z244,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z610])],[(0,[z0,z1,z611,z2,z3,z4,z6]),(0,[z0,z612,z1,z2,z3,z4,z6]),(0,[z0,z1,z613,z2,z3,z4,z6]),(1,[z0,z351,z1,z2,z3,z6]),(0,[z0,z1,z259,z2,z3,z4,z6]),(0,[z0,z59,z1,z3,z4,z6,z60])],[(0,[z0,z1,z2,z3,z4,z614,z6]),(0,[z0,z1,z2,z3,z615,z4,z6]),(0,[z0,z1,z2,z159,z4,z6,z114])],[(0,[z0,z1,z2,z3,z616,z4,z6]),(0,[z0,z617,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z197,z3,z4,z6]),(0,[z0,z1,z618,z2,z3,z4,z6]),(0,[z0,z1,z2,z619,z3,z4,z6])],[(0,[z620,z0,z1,z2,z3,z4,z6])],[(1,[z0,z137,z1,z106,z4,z6]),(0,[z0,z1,z621,z2,z3,z4,z6])],[(0,[z622,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z10,z6]),(0,[z0,z1,z2,z3,z4,z623,z6]),(0,[z0,z11,z1,z2,z3,z49,z6]),(0,[z0,z1,z2,z3,z18,z4,z60]),(0,[z0,z1,z2,z3,z4,z6,z624]),(0,[z0,z50,z1,z2,z3,z28,z6]),(1,[z0,z270,z1,z2,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z625]),(0,[z0,z1,z2,z626,z3,z4,z6])]],
   [[(0,[z627,z0,z1,z2,z3,z4,z6]),(0,[z0,z113,z2,z3,z4,z77,z6]),(0,[z0,z59,z1,z2,z126,z4,z6]),(1,[z0,z59,z1,z3,z4,z60]),(0,[z0,z1,z2,z3,z4,z6,z628])],[(0,[z0,z1,z2,z159,z27,z3,z4])],[(0,[z0,z1,z629,z2,z3,z4,z6])],[(0,[z0,z1,z630,z2,z3,z4,z6])],[(0,[z0,z1,z631,z2,z3,z4,z6])],[(0,[z0,z1,z434,z41,z3,z4,z6]),(0,[z0,z1,z2,z3,z632,z4,z6]),(0,[z633,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z188,z3,z4,z6])],[(0,[z0,z634,z1,z2,z3,z4,z6]),(0,[z250,z0,z1,z2,z3,z4,z272]),(0,[z250,z0,z113,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z99,z6]),(0,[z0,z1,z2,z3,z130,z6,z178])],[(0,[z0,z172,z1,z2,z3,z4,z6]),(0,[z635,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z276,z6]),(0,[z0,z636,z1,z2,z3,z4,z6]),(0,[z0,z210,z1,z2,z18,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z637]),(0,[z0,z1,z2,z3,z4,z638,z6])]],
   [[(0,[z69,z0,z1,z41,z3,z4,z6]),(0,[z0,z639,z1,z2,z3,z4,z6]),(0,[z640,z0,z1,z2,z3,z4,z6]),(0,[z0,z641,z1,z2,z3,z4,z6]),(0,[z0,z642,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z54,z3,z6,z19])],[(0,[z643,z0,z1,z2,z3,z4,z6]),(0,[z0,z214,z1,z45,z3,z4,z6]),(0,[z0,z644,z1,z2,z3,z4,z6]),(0,[z0,z137,z1,z3,z106,z4,z6]),(1,[z0,z1,z2,z543,z4,z6]),(0,[z0,z1,z2,z3,z195,z4,z6]),(0,[z645,z0,z1,z2,z3,z4,z6])],[(0,[z646,z0,z1,z2,z3,z4,z6]),(0,[z647,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z648,z3,z4,z6]),(0,[z0,z1,z2,z3,z649,z4,z6]),(0,[z0,z1,z2,z3,z4,z178,z60])],[(0,[z0,z650,z1,z2,z3,z4,z6]),(0,[z0,z651,z1,z2,z3,z4,z6]),(0,[z156,z0,z23,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z652]),(0,[z0,z653,z1,z2,z3,z4,z6]),(0,[z654,z0,z1,z2,z3,z4,z6])],[(0,[z14,z0,z214,z1,z3,z4,z6]),(0,[z0,z655,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z54,z3,z4,z6])],[(1,[z0,z1,z259,z2,z3,z4]),(0,[z656,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z138,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z26,z4,z6])],[(0,[z0,z657,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z658,z3,z4,z6]),(0,[z182,z0,z1,z2,z3,z4,z272]),(0,[z0,z659,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z660,z4,z6]),(0,[z0,z661,z1,z2,z3,z4,z6])],[(0,[z662,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z663]),(0,[z0,z1,z2,z54,z159,z4,z6])]],
   [[(0,[z664,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z543,z3,z4,z6]),(0,[z0,z1,z665,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z666])],[(0,[z212,z0,z210,z1,z2,z4,z6]),(0,[z0,z1,z2,z667,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z668,z6]),(0,[z0,z1,z2,z669,z3,z4,z6]),(0,[z180,z1,z2,z3,z4,z181,z6]),(0,[z0,z25,z1,z2,z34,z4,z6]),(0,[z0,z1,z2,z3,z670,z4,z6])],[(0,[z0,z1,z2,z671,z3,z4,z6]),(0,[z0,z1,z2,z672,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z12])],[(0,[z0,z113,z1,z2,z3,z4,z98]),(0,[z0,z1,z2,z3,z4,z239,z6]),(0,[z0,z1,z138,z34,z3,z4,z6]),(1,[z0,z1,z2,z3,z230,z6])],[(0,[z673,z0,z1,z2,z3,z4,z6]),(0,[z0,z674,z1,z2,z3,z4,z6]),(0,[z0,z1,z263,z2,z3,z4,z6]),(0,[z0,z424,z1,z2,z3,z4,z6]),(1,[z0,z76,z1,z2,z6,z19])],[(0,[z0,z675,z1,z2,z3,z4,z6]),(0,[z676,z0,z1,z2,z3,z4,z6])],[(0,[z677,z0,z1,z2,z3,z4,z6]),(1,[z238,z172,z2,z3,z4,z6]),(0,[z42,z44,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z49,z6,z178]),(0,[z0,z59,z1,z2,z3,z4,z6]),(0,[z0,z1,z678,z2,z3,z4,z6]),(0,[z0,z50,z1,z2,z27,z3,z4])]],
   [[(0,[z679,z0,z1,z2,z3,z4,z6]),(1,[z0,z260,z1,z2,z3,z6]),(0,[z0,z1,z2,z27,z308,z4,z6])],[(0,[z0,z50,z1,z2,z132,z4,z6])],[(0,[z0,z1,z2,z3,z680,z4,z6]),(0,[z0,z681,z1,z2,z3,z4,z6]),(0,[z0,z25,z1,z2,z27,z3,z4])],[(0,[z682,z0,z1,z2,z3,z4,z6]),(0,[z1,z2,z122,z3,z203,z4,z6]),(0,[z0,z1,z2,z3,z4,z683,z6])],[(0,[z0,z1,z2,z3,z4,z208,z272]),(1,[z0,z1,z2,z3,z105,z6]),(0,[z0,z1,z2,z3,z684,z4,z6])],[(0,[z0,z1,z2,z3,z685,z4,z6]),(1,[z0,z146,z2,z3,z153,z6]),(0,[z686,z0,z1,z2,z3,z4,z6])],[(0,[z0,z687,z1,z2,z3,z4,z6]),(0,[z156,z0,z1,z2,z3,z181,z6]),(0,[z0,z1,z688,z2,z3,z4,z6]),(0,[z0,z689,z1,z2,z3,z4,z6]),(0,[z0,z690,z1,z2,z3,z4,z6]),(0,[z0,z1,z691,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z692,z4,z6])],[(0,[z0,z693,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z34,z203,z4,z6]),(0,[z0,z694,z1,z2,z3,z4,z6]),(0,[z695,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z109,z1,z41,z2,z3,z6]),(0,[z0,z1,z2,z3,z131,z49,z6]),(0,[z0,z1,z2,z3,z4,z6,z696])],[(0,[z182,z1,z2,z3,z4,z164,z6]),(0,[z0,z1,z2,z3,z4,z6,z697]),(0,[z0,z11,z1,z3,z4,z49,z6]),(0,[z0,z25,z76,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z18,z13,z6]),(0,[z0,z1,z2,z3,z28,z6,z178])],[(0,[z698,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z699,z4,z6]),(0,[z0,z76,z1,z2,z4,z6,z19])],[(0,[z0,z172,z2,z45,z3,z4,z6]),(0,[z0,z25,z1,z2,z106,z4,z6]),(0,[z0,z1,z2,z700,z3,z4,z6]),(0,[z0,z1,z2,z54,z18,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z701]),(0,[z0,z1,z702,z2,z3,z4,z6]),(0,[z0,z1,z34,z3,z106,z4,z6])],[(0,[z0,z1,z2,z3,z703,z4,z6])],[(0,[z0,z1,z704,z2,z3,z4,z6]),(0,[z42,z14,z1,z2,z3,z4,z6]),(0,[z0,z100,z2,z188,z3,z4,z6]),(0,[z0,z705,z1,z2,z3,z4,z6]),(0,[z0,z59,z1,z2,z3,z84,z6])],[(0,[z0,z1,z2,z3,z4,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z306,z1,z2,z3,z131,z6]),(0,[z0,z1,z259,z2,z4,z184])],[(0,[z171,z69,z41,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z707]),(0,[z0,z1,z2,z3,z708,z6]),(0,[z0,z1,z2,z488,z55,z6]),(0,[z0,z76,z1,z2,z4,z93]),(0,[z0,z1,z2,z491,z4,z114]),(0,[z0,z1,z2,z4,z709,z114])],[(0,[z0,z1,z2,z3,z4,z710]),(0,[z711,z41,z2,z3,z4,z6]),(0,[z0,z1,z2,z712,z4,z6])],[(0,[z0,z1,z2,z3,z4,z713]),(0,[z0,z1,z2,z3,z4,z714]),(0,[z0,z424,z23,z1,z2,z6]),(0,[z0,z1,z2,z3,z715,z6]),(0,[z0,z1,z2,z106,z4,z93]),(0,[z0,z1,z2,z716,z4,z6])],[(0,[z0,z717,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z718,z6]),(0,[z0,z1,z2,z3,z4,z719])],[(0,[z69,z0,z136,z1,z4,z6]),(0,[z0,z720,z1,z2,z3,z6]),(0,[z0,z1,z138,z712,z4,z6])],[(0,[z0,z1,z2,z721,z4,z6]),(0,[z0,z1,z2,z3,z150,z6]),(0,[z0,z1,z2,z722,z4,z6]),(0,[z0,z1,z2,z3,z154,z4]),(0,[z0,z1,z3,z712,z4,z6]),(0,[z0,z25,z1,z2,z222,z4])],[(0,[z0,z1,z2,z3,z4,z723]),(0,[z0,z1,z2,z3,z724,z6]),(0,[z0,z1,z2,z3,z725,z4]),(0,[z0,z137,z1,z106,z4,z239]),(0,[z0,z1,z2,z159,z4,z114])]],
   [[(0,[z0,z146,z424,z1,z2,z6]),(0,[z0,z1,z445,z3,z4,z60]),(0,[z0,z1,z2,z47,z49,z6]),(0,[z0,z1,z189,z3,z130,z6]),(0,[z0,z25,z1,z2,z18,z230])],[(0,[z0,z1,z726,z3,z4,z6]),(0,[z727,z1,z2,z3,z4,z6]),(0,[z0,z1,z34,z712,z4,z6]),(0,[z0,z1,z48,z3,z130,z6]),(0,[z0,z1,z2,z54,z56,z55])],[(0,[z0,z1,z2,z275,z4,z43]),(0,[z0,z1,z2,z3,z4,z728]),(0,[z0,z1,z2,z3,z276,z43]),(0,[z42,z267,z1,z3,z4,z6])],[(0,[z0,z1,z2,z729,z4,z6]),(0,[z0,z97,z2,z3,z413,z98]),(0,[z0,z1,z2,z27,z3,z26]),(0,[z0,z1,z2,z3,z28,z13])],[(0,[z0,z1,z730,z2,z3,z4]),(0,[z0,z1,z2,z731,z4,z6]),(0,[z0,z210,z2,z732,z4,z6]),(0,[z0,z1,z259,z2,z3,z4]),(0,[z0,z1,z2,z733,z4,z6]),(0,[z0,z1,z2,z3,z436,z60]),(0,[z0,z734,z1,z2,z3,z4]),(0,[z0,z1,z2,z735,z6,z19]),(0,[z0,z1,z2,z3,z28,z567])],[(0,[z0,z1,z2,z36,z4,z6]),(0,[z0,z1,z2,z3,z67,z233]),(0,[z0,z1,z2,z27,z3,z670])],[(0,[z0,z1,z3,z4,z736,z6]),(0,[z0,z737,z1,z2,z3,z4]),(0,[z0,z97,z2,z4,z202,z98]),(0,[z0,z59,z1,z3,z84,z60]),(0,[z0,z1,z2,z3,z738,z6]),(0,[z0,z1,z739,z3,z4,z6])],[(0,[z0,z740,z1,z2,z4,z6])]],
   [[(0,[z69,z0,z244,z1,z4,z6]),(0,[z0,z1,z2,z3,z741,z6]),(0,[z0,z675,z1,z106,z4,z6]),(0,[z0,z1,z2,z3,z4,z742]),(0,[z0,z1,z2,z3,z4,z743])],[(0,[z0,z1,z2,z744,z3,z4]),(0,[z1,z2,z3,z4,z745,z272]),(0,[z0,z746,z1,z2,z4,z6]),(1,[z0,z1,z2,z4,z709]),(0,[z0,z1,z2,z159,z312,z4])],[(0,[z679,z1,z2,z203,z4,z6]),(0,[z747,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z36,z4,z99]),(0,[z0,z1,z2,z3,z4,z12]),(0,[z0,z1,z2,z4,z709,z6])],[(0,[z171,z41,z2,z3,z4,z6]),(0,[z0,z50,z1,z2,z27,z132])],[(0,[z0,z1,z2,z3,z4,z748]),(0,[z1,z2,z749,z3,z4,z6]),(0,[z1,z2,z3,z131,z750,z6]),(0,[z182,z1,z2,z3,z4,z164]),(0,[z0,z25,z1,z2,z615,z4])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z751,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z752])],[(0,[z238,z172,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z753,z6])],[(1,[z1,z2,z754,z4,z6]),(0,[z0,z210,z2,z582,z4,z6]),(0,[z0,z1,z618,z106,z4,z6]),(0,[z0,z644,z1,z2,z3,z28])]],
   [[(0,[z1,z2,z122,z754,z4,z6]),(0,[z0,z1,z2,z4,z755,z6])],[(0,[z0,z100,z1,z2,z56,z4]),(0,[z0,z1,z2,z4,z756,z6]),(0,[z0,z1,z2,z3,z55,z317]),(0,[z0,z1,z2,z54,z55,z382])],[(0,[z0,z757,z1,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z758]),(0,[z180,z1,z2,z3,z750,z6]),(0,[z0,z1,z2,z3,z4,z99]),(0,[z0,z1,z2,z759,z4,z6])],[(0,[z0,z760,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z105,z6]),(0,[z0,z1,z2,z27,z132,z6])],[(1,[z711,z2,z3,z4,z6]),(0,[z0,z1,z2,z761,z4,z6]),(0,[z0,z1,z2,z762,z4,z6]),(0,[z0,z1,z2,z132,z49,z6]),(0,[z0,z1,z2,z308,z4,z208]),(0,[z0,z170,z76,z1,z2,z6]),(0,[z0,z763,z2,z3,z4,z6])],[(0,[z0,z1,z2,z764,z3,z4]),(0,[z0,z214,z35,z36,z4,z6]),(0,[z0,z1,z2,z3,z28,z382])],[(0,[z0,z70,z136,z1,z2,z4]),(0,[z0,z210,z631,z2,z4,z6]),(0,[z0,z100,z2,z4,z223,z6])],[(0,[z0,z1,z2,z36,z4,z7]),(0,[z0,z210,z2,z87,z4,z6]),(0,[z0,z1,z2,z765,z4,z6]),(0,[z0,z1,z2,z54,z55,z317]),(0,[z0,z1,z2,z94,z4,z178])]],
   [[(0,[z0,z1,z2,z3,z766,z6]),(0,[z0,z767,z1,z2,z4,z6]),(0,[z0,z768,z1,z2,z3,z6]),(0,[z0,z11,z1,z3,z769,z6]),(0,[z0,z1,z2,z54,z55,z93])],[(1,[z0,z1,z712,z4,z6]),(0,[z0,z1,z2,z47,z130,z6]),(0,[z0,z1,z2,z770,z4,z6]),(0,[z0,z771,z1,z2,z4,z6])],[(0,[z0,z244,z1,z2,z4,z6]),(0,[z0,z1,z2,z772,z4,z6]),(0,[z0,z612,z1,z3,z49,z6])],[(0,[z0,z1,z2,z773,z4,z6]),(0,[z0,z1,z2,z3,z4,z774]),(0,[z0,z1,z2,z28,z18,z19])],[(0,[z0,z1,z3,z775,z4,z6]),(0,[z0,z1,z3,z4,z6,z776]),(0,[z0,z1,z2,z3,z4,z777]),(0,[z0,z2,z3,z4,z778,z6]),(0,[z0,z1,z2,z3,z84,z6])],[(0,[z0,z1,z2,z3,z28,z625]),(0,[z0,z1,z2,z3,z130,z382]),(0,[z0,z50,z1,z2,z94,z27])],[(0,[z0,z1,z2,z779,z4,z6]),(0,[z0,z1,z2,z254,z4,z6]),(0,[z0,z1,z2,z3,z4,z220]),(0,[z0,z1,z2,z94,z4,z114])],[(0,[z0,z1,z2,z3,z4,z7]),(0,[z0,z137,z1,z712,z4,z6]),(0,[z0,z1,z780,z2,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z10,z6]),(0,[z44,z0,z781,z3,z4,z6]),(0,[z0,z1,z2,z782,z4,z6]),(0,[z0,z11,z1,z543,z49,z6])],[(0,[z0,z214,z525,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z783])],[(0,[z0,z214,z35,z3,z4,z99]),(0,[z0,z1,z2,z54,z670,z6])],[(0,[z0,z214,z35,z3,z105,z6]),(0,[z0,z1,z2,z254,z4,z99]),(0,[z0,z1,z2,z3,z784,z6]),(0,[z0,z1,z2,z785,z4,z6])],[(0,[z0,z1,z749,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z786]),(0,[z0,z1,z2,z787,z4,z6]),(0,[z30,z1,z2,z3,z4,z272]),(0,[z0,z1,z2,z3,z788,z6]),(0,[z0,z1,z2,z254,z105,z6]),(0,[z0,z1,z2,z3,z4,z789]),(0,[z0,z1,z2,z3,z790,z6]),(0,[z0,z1,z2,z3,z735,z6])],[(0,[z0,z1,z2,z791,z4,z6]),(0,[z0,z792,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z793,z4])],[(0,[z0,z1,z2,z3,z4,z794]),(0,[z0,z1,z2,z3,z4,z795]),(0,[z0,z1,z2,z195,z436,z6]),(0,[z0,z1,z2,z56,z4,z114])],[(1,[z0,z1,z3,z4,z743])]],
   [[(0,[z0,z1,z2,z796,z4,z6]),(0,[z0,z1,z2,z797,z4,z6])],[(0,[z0,z109,z70,z1,z2,z3]),(0,[z0,z1,z2,z275,z4,z6]),(0,[z0,z1,z2,z3,z276,z6]),(0,[z0,z1,z2,z3,z798,z6])],[(0,[z0,z244,z1,z434,z4,z6]),(0,[z0,z113,z1,z2,z3,z26]),(0,[z0,z1,z2,z3,z4,z233]),(0,[z0,z11,z1,z3,z49,z12]),(0,[z0,z1,z2,z195,z4,z208]),(0,[z0,z1,z2,z54,z735,z6])],[(0,[z0,z100,z1,z2,z197,z4]),(0,[z0,z268,z1,z2,z159,z4]),(0,[z0,z146,z2,z3,z778,z6]),(0,[z0,z50,z1,z2,z3,z593]),(0,[z0,z1,z2,z47,z4,z12]),(0,[z0,z1,z2,z3,z13,z208])],[(0,[z0,z136,z1,z2,z4,z6]),(0,[z0,z40,z409,z1,z2,z3]),(0,[z0,z1,z2,z3,z4,z799])],[(0,[z121,z1,z2,z754,z4,z6]),(0,[z800,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z801,z6]),(0,[z0,z1,z2,z3,z4,z802]),(0,[z0,z1,z2,z132,z130,z6]),(0,[z0,z1,z2,z803,z4,z6])],[(0,[z0,z804,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z805]),(0,[z0,z214,z35,z3,z4,z7]),(0,[z0,z1,z2,z94,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z85]),(0,[z0,z214,z35,z3,z10,z6]),(0,[z0,z1,z2,z254,z4,z7]),(0,[z0,z1,z2,z55,z230,z6])],[(0,[z0,z1,z2,z254,z10,z6]),(0,[z0,z146,z2,z3,z638,z6]),(0,[z0,z1,z2,z806,z4,z6]),(0,[z0,z113,z1,z2,z94,z4]),(0,[z0,z1,z2,z3,z807,z6]),(0,[z0,z1,z2,z808,z3,z4])],[(0,[z0,z113,z1,z2,z3,z413])],[(0,[z0,z1,z2,z234,z276,z6]),(0,[z0,z1,z2,z3,z809,z6]),(0,[z0,z76,z1,z2,z362,z6])],[(0,[z0,z1,z2,z3,z4,z810]),(0,[z0,z1,z2,z3,z4,z811]),(0,[z0,z1,z2,z812,z3,z4]),(0,[z0,z1,z2,z3,z813,z6]),(0,[z0,z1,z814,z2,z3,z4]),(0,[z0,z23,z2,z3,z24,z6]),(0,[z0,z59,z1,z195,z4,z60]),(0,[z0,z1,z2,z308,z4,z6]),(0,[z0,z1,z2,z159,z3,z13])],[(0,[z0,z1,z2,z3,z4,z815]),(0,[z0,z1,z2,z3,z816,z4]),(0,[z0,z1,z2,z817,z4,z6])],[(0,[z0,z1,z2,z3,z818,z6]),(0,[z0,z1,z2,z3,z67,z239]),(0,[z0,z1,z2,z34,z230,z6])],[(0,[z0,z210,z1,z2,z56,z4]),(0,[z0,z1,z2,z154,z4,z184]),(0,[z0,z270,z23,z1,z2,z6]),(0,[z0,z1,z2,z3,z4,z819]),(0,[z0,z1,z2,z820,z3,z6])]],
   [[(0,[z0,z1,z2,z821,z4,z6]),(0,[z0,z1,z2,z3,z822,z6]),(0,[z0,z100,z2,z4,z103,z6]),(0,[z0,z1,z2,z255,z202,z6]),(0,[z0,z661,z1,z3,z49,z6])],[(0,[z0,z133,z2,z3,z4,z43]),(0,[z0,z1,z2,z3,z823,z6]),(0,[z0,z1,z2,z824,z4,z6]),(0,[z0,z1,z2,z3,z28,z394]),(0,[z0,z1,z2,z126,z4,z6]),(0,[z0,z1,z2,z825,z3,z4]),(0,[z0,z1,z826,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z827]),(0,[z0,z1,z2,z234,z4,z85]),(0,[z1,z749,z72,z3,z4,z6]),(0,[z0,z1,z471,z34,z4,z6]),(0,[z0,z50,z270,z1,z2,z6])],[(0,[z695,z1,z2,z122,z4,z6]),(0,[z0,z1,z2,z3,z828,z6])],[(0,[z171,z434,z41,z3,z4,z6]),(0,[z0,z1,z2,z3,z829,z6]),(0,[z0,z1,z2,z3,z258,z43]),(0,[z0,z1,z2,z3,z830,z6]),(1,[z0,z781,z3,z4,z6]),(0,[z0,z1,z2,z3,z831,z6]),(0,[z0,z1,z2,z147,z4,z114]),(0,[z0,z1,z2,z3,z832,z178])],[(0,[z171,z109,z41,z2,z3,z6]),(0,[z0,z260,z1,z2,z6,z19])],[(0,[z42,z1,z72,z3,z4,z43]),(0,[z0,z1,z2,z833,z3,z4]),(0,[z834,z1,z2,z3,z4,z6]),(0,[z0,z97,z1,z2,z201,z4]),(0,[z0,z1,z2,z3,z4,z835])],[(0,[z0,z705,z1,z2,z6,z19]),(0,[z0,z1,z2,z3,z185,z178]),(0,[z0,z76,z1,z2,z132,z6]),(0,[z0,z1,z2,z3,z26,z382]),(0,[z0,z50,z1,z2,z308,z4])]],
   [[(0,[z0,z244,z109,z1,z2,z6]),(0,[z0,z836,z1,z2,z3,z4]),(0,[z1,z2,z754,z203,z4,z6]),(0,[z0,z1,z581,z3,z130,z6]),(0,[z0,z210,z2,z150,z87,z6])],[(0,[z0,z837,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z838]),(0,[z0,z1,z2,z3,z317,z13]),(0,[z0,z1,z2,z3,z26,z18])],[(0,[z0,z1,z2,z3,z4,z839])],[(0,[z0,z1,z2,z3,z258,z85]),(0,[z0,z1,z2,z3,z840,z6]),(0,[z0,z1,z2,z3,z4,z841]),(0,[z0,z1,z2,z3,z4,z842]),(0,[z0,z1,z2,z4,z735,z6]),(0,[z0,z1,z2,z27,z3,z832])],[(0,[z0,z70,z1,z2,z3,z4]),(0,[z0,z1,z3,z4,z843,z6]),(0,[z0,z369,z2,z3,z4,z43]),(0,[z0,z1,z2,z844,z4,z6]),(0,[z0,z1,z2,z3,z845,z6]),(0,[z0,z1,z2,z3,z769,z6]),(0,[z0,z1,z846,z2,z3,z4])],[(0,[z0,z1,z2,z3,z847,z6]),(0,[z69,z0,z214,z3,z4,z6]),(0,[z0,z1,z2,z275,z276,z6]),(0,[z42,z1,z72,z3,z4,z85]),(0,[z0,z1,z2,z55,z623,z6]),(0,[z0,z1,z2,z3,z294,z6]),(0,[z0,z1,z3,z4,z208,z743])],[(0,[z0,z848,z1,z2,z4,z6])],[(0,[z0,z1,z849,z3,z4,z6]),(0,[z0,z850,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z851]),(0,[z0,z23,z2,z3,z211,z6]),(0,[z0,z1,z2,z106,z230,z6]),(0,[z0,z1,z2,z3,z49,z382])]],
   [[(0,[z180,z1,z2,z3,z181,z6]),(0,[z0,z1,z2,z3,z852,z6]),(0,[z0,z1,z2,z3,z4,z853]),(0,[z0,z1,z2,z854,z4,z6]),(0,[z0,z1,z2,z126,z84,z6]),(0,[z0,z170,z1,z2,z18,z4]),(0,[z0,z270,z1,z2,z55,z6])],[(0,[z0,z1,z2,z4,z855,z6]),(0,[z0,z856,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z857,z6]),(0,[z0,z1,z2,z55,z735,z6]),(0,[z0,z1,z2,z54,z3,z382])],[(0,[z0,z858,z1,z2,z3,z6]),(0,[z0,z25,z1,z2,z27,z55])],[(0,[z0,z859,z2,z3,z4,z6]),(0,[z0,z1,z2,z860,z4,z6]),(0,[z0,z1,z2,z861,z3,z4]),(0,[z0,z351,z1,z263,z2,z3]),(0,[z0,z1,z2,z862,z4,z6]),(0,[z0,z1,z2,z3,z13,z6])],[(0,[z0,z1,z3,z4,z6,z863]),(0,[z0,z864,z2,z3,z4,z6]),(0,[z0,z1,z2,z275,z4,z85]),(0,[z0,z1,z2,z3,z276,z85]),(0,[z0,z1,z2,z3,z865,z6])],[(0,[z0,z866,z2,z3,z4,z6]),(0,[z0,z76,z480,z1,z2,z6])],[(0,[z0,z1,z2,z867,z4,z6]),(0,[z0,z210,z351,z2,z87,z6])],[(0,[z0,z109,z40,z1,z2,z3]),(0,[z0,z1,z2,z868,z4,z6]),(0,[z0,z351,z100,z1,z2,z6]),(0,[z0,z1,z2,z159,z27,z19]),(0,[z0,z1,z2,z869,z4,z6])]],
   [[(0,[z0,z1,z2,z870,z3,z4])],[(0,[z0,z1,z2,z3,z871,z6]),(0,[z0,z210,z1,z2,z197,z4]),(0,[z0,z1,z2,z27,z3,z382])],[],[(0,[z0,z1,z2,z3,z4,z872]),(0,[z0,z1,z2,z3,z873,z6])],[(0,[z69,z0,z45,z3,z4,z6]),(0,[z0,z70,z1,z434,z3,z4]),(0,[z0,z1,z2,z3,z874,z6]),(0,[z0,z1,z2,z3,z875,z6]),(0,[z0,z1,z2,z3,z876,z6]),(0,[z0,z1,z2,z3,z832,z6])],[(0,[z212,z689,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z877]),(0,[z0,z1,z2,z878,z3,z4])],[(0,[z0,z879,z1,z2,z3,z6]),(0,[z0,z1,z880,z2,z3,z4]),(0,[z0,z1,z2,z34,z67,z6])],[(0,[z0,z1,z2,z4,z881,z6])]],
   [[(0,[z0,z1,z2,z3,z882,z6]),(0,[z0,z1,z2,z883,z4,z6])],[(0,[z171,z409,z41,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z884]),(0,[z0,z548,z1,z2,z3,z178])],[(0,[z0,z1,z2,z885,z4,z6]),(0,[z0,z1,z2,z234,z4,z6])],[(0,[z121,z198,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z750,z6]),(0,[z0,z1,z2,z3,z4,z239]),(0,[z0,z653,z1,z2,z6,z19]),(0,[z0,z1,z2,z94,z4,z93])],[(0,[z0,z1,z2,z886,z4,z6])],[(0,[z0,z1,z2,z3,z4,z887]),(0,[z0,z146,z1,z2,z3,z154])],[(0,[z182,z101,z1,z2,z3,z4]),(0,[z0,z175,z1,z2,z159,z4]),(0,[z0,z50,z1,z2,z312,z3])],[(0,[z0,z1,z2,z3,z888,z6]),(0,[z0,z1,z2,z3,z889,z6]),(0,[z0,z1,z2,z890,z4,z6]),(0,[z0,z50,z1,z2,z27,z308])]],
   [[(0,[z0,z214,z35,z3,z4,z6])],[(0,[z0,z1,z2,z891,z3,z4]),(0,[z0,z1,z2,z18,z4,z333])],[(0,[z0,z1,z892,z3,z4,z6]),(0,[z180,z327,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z893,z6]),(0,[z0,z1,z2,z3,z294,z233]),(0,[z0,z260,z1,z2,z54,z6])],[(0,[z0,z1,z2,z3,z258,z6]),(0,[z0,z146,z365,z2,z3,z6]),(0,[z0,z214,z781,z3,z4,z6]),(1,[z0,z1,z3,z769,z6])],[(0,[z0,z894,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z895]),(0,[z156,z38,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z896,z6])],[(0,[z0,z1,z2,z897,z4,z6]),(0,[z0,z1,z2,z4,z6,z898]),(0,[z42,z1,z72,z3,z4,z6]),(0,[z0,z1,z2,z732,z4,z6]),(0,[z0,z97,z2,z3,z4,z580])],[(0,[z0,z1,z899,z3,z4,z6]),(0,[z182,z1,z2,z3,z4,z745]),(0,[z0,z1,z2,z3,z900,z4]),(0,[z0,z1,z2,z3,z13,z60])],[(0,[z0,z1,z2,z3,z901,z6]),(0,[z0,z1,z2,z902,z4,z6]),(0,[z0,z210,z2,z197,z87,z4]),(0,[z0,z424,z1,z2,z154,z4]),(0,[z0,z1,z2,z106,z67,z6]),(0,[z0,z1,z2,z159,z4,z567]),(0,[z0,z50,z1,z2,z54,z18])]],
   [[(0,[z0,z1,z903,z2,z3,z4]),(0,[z0,z1,z2,z3,z904,z6])],[(0,[z0,z1,z2,z4,z6,z905]),(0,[z31,z172,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z906,z6]),(0,[z0,z1,z2,z3,z907,z6]),(0,[z0,z50,z270,z1,z2,z27])],[(1,[z0,z2,z3,z778,z6]),(0,[z0,z146,z1,z2,z3,z317]),(0,[z0,z577,z1,z106,z4,z6])],[(0,[z0,z369,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z908,z6]),(0,[z0,z1,z2,z3,z909,z4])],[(0,[z0,z210,z263,z2,z87,z4])],[(0,[z0,z1,z2,z234,z258,z6]),(0,[z212,z1,z2,z754,z4,z6]),(0,[z0,z910,z1,z2,z4,z6]),(0,[z0,z1,z2,z159,z4,z410]),(0,[z0,z119,z76,z1,z2,z6]),(0,[z0,z1,z2,z94,z27,z4])],[(0,[z0,z1,z2,z3,z911,z6]),(0,[z250,z1,z2,z3,z4,z745]),(0,[z0,z260,z100,z1,z2,z6]),(0,[z0,z1,z469,z3,z4,z208]),(0,[z0,z1,z2,z308,z28,z4])],[(0,[z171,z40,z41,z2,z3,z4]),(0,[z0,z1,z3,z912,z4,z6]),(0,[z42,z1,z72,z234,z4,z6])]],
   [[(0,[z0,z913,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z914,z6]),(0,[z0,z1,z2,z3,z915,z4]),(0,[z0,z1,z2,z916,z4,z6]),(0,[z0,z1,z2,z3,z917,z6]),(0,[z0,z1,z2,z201,z4,z6]),(0,[z0,z11,z1,z3,z49,z6])],[(0,[z0,z214,z133,z3,z4,z6]),(0,[z0,z214,z35,z254,z4,z6]),(0,[z0,z1,z2,z47,z4,z6]),(0,[z0,z1,z2,z54,z316,z6]),(0,[z0,z1,z2,z3,z596,z178]),(0,[z0,z25,z1,z2,z3,z13])],[(0,[z0,z109,z136,z1,z2,z6]),(0,[z918,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z919,z4,z6])],[(0,[z0,z1,z2,z920,z4,z6]),(0,[z0,z1,z2,z3,z4,z745]),(0,[z0,z781,z45,z3,z4,z6]),(0,[z0,z100,z2,z188,z4,z6]),(0,[z0,z1,z2,z3,z255,z6]),(0,[z0,z1,z2,z3,z921,z6]),(0,[z0,z1,z2,z94,z18,z4])],[(0,[z0,z1,z2,z922,z4,z6])],[],[(0,[z0,z244,z409,z1,z2,z6]),(0,[z0,z1,z2,z923,z4,z6]),(0,[z0,z1,z2,z924,z4,z6]),(0,[z0,z1,z2,z4,z925,z6]),(0,[z0,z926,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z4,z927]),(0,[z0,z1,z2,z413,z202,z6])]],
   [[(0,[z42,z1,z72,z3,z258,z6]),(0,[z0,z928,z1,z2,z3,z6])],[(0,[z0,z1,z75,z3,z130,z6])],[(0,[z212,z1,z2,z203,z4,z6]),(0,[z0,z1,z2,z3,z4,z929]),(0,[z0,z210,z2,z209,z4,z6]),(0,[z0,z351,z1,z2,z197,z3]),(0,[z0,z76,z1,z2,z422,z6]),(0,[z0,z1,z490,z3,z49,z6]),(0,[z0,z577,z1,z3,z49,z6]),(0,[z0,z1,z2,z500,z6,z19])],[],[(0,[z0,z133,z2,z275,z4,z6]),(0,[z0,z133,z2,z3,z276,z6]),(0,[z0,z97,z420,z2,z3,z4]),(0,[z0,z1,z2,z930,z4,z6]),(0,[z0,z1,z2,z3,z931,z6]),(0,[z0,z35,z781,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z93])],[(0,[z0,z1,z2,z3,z932,z6]),(0,[z0,z933,z1,z2,z3,z6])],[(0,[z0,z1,z934,z2,z3,z4]),(0,[z1,z2,z3,z750,z4,z6]),(0,[z0,z1,z138,z34,z4,z6]),(0,[z0,z1,z2,z3,z4,z935]),(0,[z0,z1,z323,z3,z4,z208]),(0,[z0,z25,z260,z1,z2,z6])],[(0,[z0,z136,z1,z434,z4,z6]),(0,[z0,z1,z2,z275,z258,z6]),(0,[z0,z1,z2,z3,z936,z4]),(0,[z1,z2,z3,z754,z4,z6]),(0,[z0,z443,z1,z3,z4,z60]),(0,[z0,z1,z2,z159,z4,z93]),(0,[z0,z1,z2,z3,z937,z4])]],
   [[(0,[z0,z1,z938,z3,z4,z6]),(0,[z0,z210,z396,z2,z4,z6]),(0,[z0,z2,z3,z4,z6,z939]),(0,[z0,z1,z2,z3,z940,z6])],[(0,[z0,z1,z2,z941,z4,z6]),(0,[z42,z1,z72,z275,z4,z6]),(0,[z42,z1,z72,z3,z276,z6]),(0,[z0,z11,z1,z3,z49,z220]),(0,[z0,z25,z1,z2,z26,z18]),(0,[z0,z270,z1,z2,z6,z178])],[(0,[z0,z942,z2,z3,z4,z6]),(0,[z0,z210,z351,z1,z2,z6]),(0,[z0,z2,z3,z732,z4,z6]),(0,[z0,z1,z2,z3,z4,z943]),(0,[z0,z1,z2,z47,z4,z220]),(0,[z0,z944,z1,z2,z4,z6])],[(0,[z0,z133,z2,z3,z4,z85])],[(0,[z0,z1,z2,z3,z945,z6]),(0,[z0,z946,z1,z2,z4,z6]),(0,[z0,z1,z2,z947,z3,z4]),(0,[z0,z100,z2,z493,z4,z6]),(1,[z0,z1,z2,z735,z6])],[(0,[z0,z146,z424,z2,z153,z6]),(0,[z0,z1,z2,z3,z317,z4]),(0,[z0,z76,z1,z2,z6,z567]),(0,[z0,z1,z2,z132,z4,z6]),(0,[z0,z1,z2,z54,z56,z4]),(0,[z0,z1,z2,z670,z4,z114])],[(0,[z42,z1,z749,z3,z4,z6]),(0,[z0,z948,z1,z2,z3,z6]),(0,[z0,z1,z2,z4,z949,z6]),(0,[z0,z1,z2,z3,z436,z208]),(0,[z0,z1,z2,z3,z317,z19])],[(0,[z0,z1,z2,z950,z3,z6]),(0,[z0,z369,z2,z275,z4,z6]),(0,[z0,z369,z2,z3,z276,z6])]],
   [[(0,[z0,z1,z2,z3,z951,z6]),(0,[z0,z1,z2,z952,z4,z6]),(0,[z0,z76,z1,z2,z230,z6]),(0,[z0,z25,z76,z1,z2,z178])],[(0,[z0,z1,z2,z953,z4,z6])],[(0,[z0,z1,z2,z3,z4,z954]),(0,[z0,z1,z2,z3,z955,z6]),(0,[z0,z1,z2,z3,z4,z956])],[(0,[z0,z957,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z958,z6]),(0,[z0,z1,z2,z3,z4,z959])],[(0,[z0,z1,z2,z3,z4,z960]),(0,[z0,z137,z1,z106,z67,z6]),(0,[z0,z25,z1,z2,z4,z221])],[(0,[z0,z1,z2,z3,z4,z961]),(0,[z0,z1,z2,z3,z962,z6]),(0,[z0,z1,z2,z195,z4,z6]),(0,[z0,z1,z2,z3,z963,z6])],[(0,[z0,z409,z136,z1,z2,z6]),(0,[z0,z369,z2,z3,z4,z85]),(0,[z0,z1,z2,z964,z4,z6]),(0,[z0,z1,z2,z965,z3,z4])],[(0,[z966,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z967])]],
   [[(0,[z0,z1,z2,z3,z4,z968]),(0,[z0,z1,z2,z3,z969,z6]),(0,[z0,z1,z48,z3,z769,z6]),(0,[z0,z59,z1,z3,z436,z60]),(0,[z0,z25,z1,z2,z18,z13])],[(0,[z0,z1,z2,z970,z4,z6]),(0,[z0,z11,z1,z47,z49,z6]),(0,[z0,z260,z1,z2,z6,z114])],[(0,[z0,z25,z1,z2,z684,z4]),(0,[z0,z1,z2,z308,z4,z60]),(0,[z0,z548,z1,z2,z4,z114])],[(0,[z0,z1,z2,z754,z4,z6]),(0,[z0,z1,z2,z197,z3,z4]),(0,[z0,z1,z2,z4,z971,z6]),(0,[z0,z1,z2,z3,z294,z239]),(0,[z0,z1,z2,z18,z4,z93])],[(0,[z69,z0,z109,z1,z3,z6]),(0,[z0,z1,z2,z3,z972,z6]),(0,[z156,z1,z2,z3,z131,z6]),(1,[z1,z2,z3,z750,z6]),(0,[z0,z146,z2,z3,z706,z6]),(0,[z0,z1,z2,z973,z4,z6]),(0,[z0,z50,z1,z2,z552,z3]),(0,[z0,z1,z2,z3,z974,z6])],[(0,[z0,z1,z2,z3,z4,z975]),(1,[z0,z1,z2,z3,z832])],[],[(0,[z0,z1,z2,z3,z4,z976])]],
   [[(0,[z0,z1,z263,z2,z3,z4]),(0,[z0,z1,z2,z4,z977,z6]),(0,[z0,z1,z2,z34,z4,z233])],[(0,[z0,z1,z2,z3,z978,z6]),(0,[z0,z1,z2,z3,z979,z6]),(0,[z0,z1,z2,z3,z49,z12]),(0,[z0,z1,z323,z3,z4,z743])],[(0,[z0,z1,z2,z980,z4,z6]),(0,[z121,z1,z2,z122,z4,z6]),(0,[z0,z981,z1,z2,z4,z6]),(0,[z0,z1,z630,z34,z4,z6]),(0,[z0,z1,z2,z56,z308,z4])],[(0,[z0,z982,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z983,z6]),(0,[z0,z1,z2,z197,z3,z150])],[(0,[z0,z1,z2,z984,z3,z4]),(0,[z0,z985,z1,z3,z4,z6]),(0,[z0,z97,z2,z3,z4,z939]),(0,[z0,z1,z2,z195,z84,z6])],[(0,[z0,z1,z2,z3,z4,z986]),(0,[z0,z97,z2,z3,z209,z4])],[(0,[z171,z70,z41,z2,z3,z4]),(0,[z0,z70,z409,z1,z2,z3])],[(0,[z0,z987,z1,z2,z3,z6]),(0,[z0,z1,z2,z988,z4,z6]),(0,[z0,z1,z2,z989,z4,z6]),(0,[z0,z1,z2,z56,z3,z4])]],
   [[(0,[z0,z109,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z990,z6]),(0,[z0,z1,z2,z3,z4,z991]),(0,[z1,z2,z3,z4,z992,z6]),(0,[z0,z113,z1,z2,z201,z4]),(0,[z0,z76,z1,z2,z735,z6]),(0,[z0,z1,z2,z55,z4,z93])],[(0,[z0,z1,z2,z3,z4,z993]),(0,[z0,z1,z2,z994,z4,z6])],[(0,[z69,z0,z1,z3,z4,z6]),(0,[z0,z133,z2,z3,z4,z6]),(0,[z0,z1,z995,z2,z3,z4]),(0,[z0,z97,z2,z3,z4,z98]),(0,[z0,z50,z1,z2,z27,z3])],[(0,[z0,z1,z2,z3,z996,z6]),(0,[z0,z40,z136,z1,z2,z4]),(0,[z0,z997,z1,z2,z3,z6]),(0,[z0,z1,z2,z998,z3,z4])],[(0,[z0,z244,z70,z1,z2,z4]),(0,[z0,z1,z2,z999,z4,z6]),(0,[z0,z1,z2,z3,z1000,z6]),(0,[z250,z1,z2,z3,z4,z272])],[(0,[z0,z1001,z1,z2,z3,z6]),(0,[z0,z50,z1,z2,z3,z221])],[(0,[z0,z1,z434,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1002]),(0,[z0,z1,z2,z3,z1003,z6]),(0,[z0,z1,z2,z1004,z4,z6]),(0,[z0,z1,z2,z3,z1005,z6])]],
   [[(0,[z0,z1,z2,z195,z4,z60])],[(0,[z0,z1,z1006,z3,z4,z6]),(0,[z0,z1,z2,z106,z4,z233]),(0,[z0,z1,z2,z54,z55,z6]),(0,[z0,z1,z2,z3,z4,z709])],[(0,[z1,z711,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z769,z6])],[(0,[z0,z2,z732,z87,z4,z6]),(0,[z0,z1,z2,z3,z4,z1007])],[(0,[z0,z1,z2,z1008,z4,z6]),(0,[z0,z1,z2,z1009,z4,z6]),(0,[z0,z1,z2,z1010,z4,z6]),(1,[z1,z2,z3,z4,z745]),(0,[z0,z1,z2,z4,z1011,z6]),(0,[z0,z1,z2,z159,z4,z709])],[(0,[z0,z1,z2,z3,z4,z1012]),(0,[z0,z133,z2,z234,z4,z6]),(0,[z0,z351,z1,z2,z3,z6]),(0,[z0,z23,z2,z3,z778,z6])],[(0,[z0,z1013,z2,z3,z4,z6]),(0,[z0,z1,z456,z3,z130,z6]),(0,[z0,z2,z3,z4,z6,z1014])],[(0,[z1,z2,z3,z4,z745,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z1015]),(0,[z0,z1,z2,z3,z413,z6]),(0,[z0,z270,z1,z2,z230,z6])],[(0,[z0,z1,z2,z4,z1016,z6]),(0,[z0,z1017,z1,z2,z4,z6]),(0,[z0,z1,z2,z54,z207,z6]),(0,[z0,z137,z1,z106,z4,z6])],[(0,[z0,z1,z2,z3,z130,z12]),(0,[z0,z1,z2,z3,z4,z1018]),(0,[z0,z1,z2,z4,z1019,z6])],[(0,[z0,z1,z2,z3,z4,z1020]),(0,[z0,z210,z260,z1,z2,z6]),(0,[z0,z1,z2,z4,z202,z6]),(0,[z0,z1,z2,z1021,z4,z6])],[(0,[z0,z1,z2,z1022,z4,z6]),(0,[z0,z1023,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1024,z6]),(0,[z0,z23,z2,z3,z484,z6])],[(0,[z0,z1025,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1026,z6]),(0,[z0,z1,z2,z3,z4,z1027]),(0,[z0,z424,z1,z259,z2,z4]),(0,[z0,z1,z2,z3,z1028,z6])],[(0,[z69,z0,z70,z1,z3,z4]),(0,[z0,z133,z2,z3,z258,z6]),(0,[z0,z214,z110,z3,z4,z6]),(0,[z0,z1,z2,z1029,z4,z6]),(0,[z0,z1,z2,z1030,z4,z6]),(0,[z0,z1,z2,z159,z308,z4])],[(0,[z171,z244,z41,z2,z4,z6]),(0,[z0,z146,z396,z2,z3,z6]),(0,[z0,z1,z155,z3,z4,z208])]],
   [[(0,[z42,z133,z72,z3,z4,z6]),(0,[z0,z369,z2,z234,z4,z6]),(0,[z0,z1,z2,z1031,z4,z6]),(0,[z1032,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z1033,z4,z6]),(0,[z0,z1,z2,z3,z1034,z6]),(0,[z0,z1,z2,z3,z4,z382])],[(0,[z1035,z1,z2,z3,z4,z6]),(0,[z0,z424,z1,z2,z4,z6])],[(0,[z0,z1,z2,z1036,z4,z6]),(0,[z0,z1,z2,z543,z4,z12]),(0,[z0,z642,z1,z2,z27,z3])],[(0,[z0,z2,z188,z732,z4,z6]),(0,[z0,z1037,z1,z2,z4,z6]),(0,[z0,z1,z2,z626,z18,z4])],[(0,[z0,z409,z1,z2,z3,z6]),(0,[z0,z1038,z1,z2,z4,z6]),(0,[z0,z1039,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z4,z1040]),(0,[z0,z1,z2,z3,z1041,z6]),(0,[z0,z1,z2,z3,z1042,z6]),(0,[z0,z1,z2,z543,z4,z6]),(0,[z0,z1,z2,z524,z4,z114]),(0,[z0,z50,z1,z2,z3,z13])],[(0,[z0,z1043,z1,z2,z3,z6]),(0,[z654,z1,z2,z3,z4,z164]),(0,[z0,z1,z2,z3,z1044,z6])],[(0,[z172,z711,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1045]),(0,[z1,z2,z3,z750,z181,z6]),(0,[z0,z25,z1,z2,z56,z4]),(0,[z0,z1,z2,z3,z26,z178])]],
   [[(0,[z0,z76,z1,z2,z3,z382]),(0,[z0,z1,z2,z18,z4,z709])],[(0,[z69,z0,z133,z3,z4,z6]),(0,[z0,z369,z2,z3,z258,z6]),(0,[z0,z1,z2,z1046,z4,z6]),(0,[z44,z0,z45,z3,z4,z6]),(0,[z0,z97,z2,z3,z4,z638]),(0,[z0,z1,z2,z3,z1047,z6]),(0,[z0,z1,z2,z55,z28,z114]),(0,[z0,z50,z1,z2,z3,z832])],[(0,[z0,z1,z2,z3,z4,z1048]),(0,[z0,z1049,z1,z2,z3,z6]),(0,[z0,z1,z589,z34,z4,z6]),(0,[z0,z1,z3,z4,z743,z60]),(0,[z0,z1,z2,z3,z28,z222])],[(0,[z42,z369,z72,z3,z4,z6]),(0,[z0,z97,z2,z201,z4,z98]),(0,[z0,z1,z2,z3,z832,z28])],[(0,[z0,z146,z2,z184,z153,z6]),(0,[z0,z661,z1,z3,z4,z60]),(0,[z0,z302,z1,z2,z18,z4])],[(0,[z0,z1,z2,z1050,z3,z4]),(0,[z0,z1,z498,z3,z4,z208])],[(0,[z0,z366,z1,z3,z4,z60]),(0,[z0,z97,z2,z3,z255,z98]),(0,[z0,z1,z2,z1051,z4,z6]),(0,[z0,z1,z2,z3,z26,z114])],[(0,[z0,z1,z2,z3,z4,z1052]),(0,[z0,z1,z2,z3,z1053,z4]),(0,[z0,z97,z1,z2,z3,z26])]],
   [[(0,[z0,z1,z1054,z3,z4,z6]),(0,[z0,z1,z2,z1055,z4,z6]),(0,[z1,z2,z3,z1056,z4,z6]),(0,[z0,z1,z2,z36,z105,z6]),(0,[z0,z1,z2,z3,z230,z6]),(0,[z0,z1,z2,z54,z132,z6])],[(0,[z171,z136,z41,z2,z4,z6]),(0,[z0,z1,z2,z1057,z4,z6]),(0,[z0,z76,z1,z2,z6,z19])],[(0,[z69,z0,z409,z1,z3,z6]),(0,[z0,z1,z2,z1058,z4,z6]),(0,[z0,z1,z2,z626,z55,z6])],[(0,[z0,z244,z40,z1,z2,z4]),(0,[z0,z2,z781,z3,z4,z6]),(0,[z0,z1,z2,z3,z1059,z6]),(0,[z0,z170,z1,z2,z27,z3]),(0,[z0,z1,z2,z159,z230,z6])],[(0,[z0,z1,z2,z1060,z4,z6]),(0,[z0,z409,z1,z434,z3,z6]),(0,[z0,z1,z2,z3,z1061,z6]),(0,[z0,z260,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z4,z1062]),(0,[z0,z1,z2,z1063,z4,z6])],[(0,[z0,z97,z1,z2,z94,z4]),(0,[z0,z137,z1,z106,z4,z233]),(0,[z0,z1,z2,z543,z4,z220]),(0,[z0,z1,z2,z3,z309,z178])],[(0,[z0,z100,z305,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z1064]),(0,[z0,z146,z270,z1,z2,z6]),(0,[z0,z97,z1,z2,z3,z413]),(0,[z0,z1,z2,z3,z1065,z6]),(0,[z0,z1,z3,z4,z6,z743]),(0,[z0,z451,z1,z2,z3,z28])]],
   [[(0,[z0,z1,z2,z3,z1066,z6]),(0,[z0,z1,z2,z27,z3,z280]),(0,[z0,z1,z2,z159,z571,z4]),(0,[z0,z1,z2,z201,z413,z6]),(0,[z0,z1,z2,z312,z55,z6])],[(0,[z0,z1,z2,z3,z1067,z6]),(0,[z0,z1068,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z1069,z6]),(0,[z0,z146,z2,z3,z153,z6])],[(0,[z0,z40,z1,z2,z3,z4]),(0,[z0,z1070,z1,z2,z3,z6]),(0,[z0,z1071,z1,z2,z3,z4]),(0,[z454,z1,z2,z3,z181,z6]),(0,[z0,z1,z2,z126,z436,z6]),(0,[z0,z1,z2,z56,z4,z19])],[(0,[z0,z307,z1,z2,z6,z19]),(0,[z0,z1,z2,z3,z317,z178])],[(0,[z0,z1,z2,z3,z4,z1072]),(0,[z0,z25,z1,z2,z18,z4])],[(0,[z156,z1,z2,z3,z750,z6]),(0,[z0,z1,z2,z36,z10,z6]),(0,[z0,z1,z2,z3,z105,z99]),(0,[z0,z1,z2,z4,z184,z6]),(0,[z0,z50,z1,z2,z3,z317])],[(0,[z0,z1,z2,z3,z1073,z6]),(0,[z0,z1,z2,z201,z255,z6])],[(0,[z0,z1,z2,z3,z1074,z6]),(0,[z0,z1,z2,z3,z4,z1075]),(0,[z0,z59,z1,z3,z4,z743]),(0,[z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z221,z6,z19])]],
   [[(0,[z0,z1076,z2,z3,z4,z6]),(0,[z0,z2,z3,z1077,z4,z6]),(0,[z0,z1,z2,z1078,z4,z6]),(0,[z0,z1,z2,z54,z159,z178]),(0,[z0,z1,z2,z3,z28,z178])],[(0,[z0,z1,z2,z3,z1079,z6]),(0,[z0,z1,z2,z1080,z4,z6])],[(0,[z0,z1,z2,z3,z1081,z4]),(0,[z0,z1,z2,z3,z1082,z6])],[(0,[z0,z711,z2,z3,z4,z6]),(0,[z0,z1083,z1,z2,z4,z6]),(0,[z0,z23,z584,z2,z3,z6]),(0,[z0,z50,z76,z1,z2,z114])],[(0,[z69,z0,z40,z1,z3,z4]),(0,[z0,z1,z2,z3,z4,z1084]),(0,[z0,z1,z2,z1085,z4,z6])],[],[(0,[z0,z1,z1086,z3,z4,z6]),(0,[z0,z100,z2,z732,z4,z6])],[(0,[z0,z1,z2,z1087,z4,z6]),(0,[z0,z1,z2,z3,z4,z1088]),(0,[z0,z1,z2,z3,z1089,z6]),(0,[z250,z92,z1,z2,z3,z4]),(0,[z0,z146,z2,z3,z154,z153]),(0,[z0,z23,z1,z2,z3,z154]),(0,[z0,z1,z2,z1090,z4,z6]),(0,[z0,z1,z2,z18,z230,z6])]],
   [[(0,[z0,z1091,z1,z2,z3,z4]),(0,[z1,z2,z3,z4,z164,z745]),(0,[z0,z1,z2,z3,z778,z6]),(0,[z0,z59,z1,z126,z4,z60])],[(0,[z647,z41,z2,z3,z4,z6]),(0,[z0,z1,z2,z1092,z4,z6]),(0,[z0,z1,z2,z3,z1093,z4])],[(0,[z0,z40,z1,z434,z3,z4]),(0,[z0,z1,z2,z3,z4,z1094]),(0,[z0,z1,z2,z3,z1095,z6]),(0,[z0,z1,z2,z1096,z4,z6]),(0,[z0,z1,z2,z3,z10,z99]),(0,[z0,z1,z2,z3,z105,z7]),(0,[z0,z548,z1,z2,z6,z19]),(0,[z0,z1,z2,z132,z28,z6])],[(0,[z0,z1097,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1098]),(0,[z0,z1099,z1,z2,z3,z4]),(0,[z0,z1,z263,z2,z3,z150]),(0,[z0,z1,z2,z3,z4,z939]),(0,[z0,z443,z1,z106,z4,z6])],[(0,[z0,z1,z2,z1100,z4,z6])],[(0,[z0,z1,z2,z3,z1101,z6]),(0,[z0,z146,z259,z2,z3,z153]),(0,[z0,z1,z2,z3,z4,z1102])],[(0,[z0,z1,z2,z3,z1103,z6]),(0,[z0,z1,z2,z3,z4,z43]),(0,[z0,z23,z2,z3,z536,z6])],[(0,[z0,z2,z3,z4,z1104,z6]),(0,[z0,z1,z2,z3,z383,z178]),(0,[z0,z1,z2,z54,z222,z6])]],
   [[(0,[z0,z1,z2,z3,z67,z6]),(0,[z0,z1,z712,z106,z4,z6]),(0,[z0,z1,z2,z538,z4,z114]),(0,[z0,z25,z260,z1,z2,z18])],[(0,[z0,z1,z2,z3,z6,z1105]),(0,[z0,z137,z1,z106,z294,z6]),(0,[z0,z1,z2,z3,z436,z6]),(0,[z0,z25,z1,z2,z4,z709])],[(0,[z0,z1,z2,z3,z6,z1106]),(0,[z0,z1,z2,z34,z4,z93]),(0,[z0,z1,z2,z626,z3,z178])],[(0,[z0,z1,z2,z3,z1107,z6]),(0,[z44,z0,z133,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1108,z6]),(0,[z0,z23,z1,z2,z3,z317]),(0,[z0,z1,z621,z34,z4,z6]),(0,[z0,z1,z368,z3,z4,z208])],[(0,[z1109,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1110,z6]),(0,[z0,z1,z3,z769,z49,z6]),(0,[z0,z1,z2,z3,z832,z4])],[(0,[z0,z1111,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1112,z6]),(0,[z0,z1,z2,z3,z10,z7]),(1,[z0,z2,z732,z4,z6])]],
   [[(0,[z238,z711,z2,z3,z4,z6]),(0,[z0,z1,z2,z234,z4,z43]),(0,[z0,z1,z2,z3,z4,z1113]),(0,[z0,z1114,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1115,z6]),(0,[z1,z2,z3,z4,z6,z1116]),(0,[z0,z1,z2,z3,z4,z1117]),(0,[z0,z1,z2,z3,z4,z1118]),(0,[z0,z270,z1,z2,z6,z19])],[(0,[z0,z1,z2,z3,z1119,z6]),(0,[z0,z2,z3,z4,z939,z98]),(0,[z0,z1120,z1,z2,z3,z6])],[(0,[z0,z1,z1121,z3,z4,z6]),(0,[z0,z109,z1,z434,z3,z6]),(0,[z0,z1,z2,z1122,z4,z6]),(0,[z0,z25,z1,z2,z308,z4])],[(0,[z0,z1,z2,z1123,z4,z6]),(0,[z0,z2,z3,z778,z153,z6])],[(0,[z0,z1124,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z1125,z6]),(0,[z0,z1,z781,z3,z4,z6]),(0,[z0,z270,z1,z2,z4,z6])],[(0,[z0,z1,z2,z1126,z4,z6]),(0,[z0,z113,z523,z2,z3,z4]),(0,[z0,z1,z2,z3,z1127,z6]),(0,[z0,z2,z3,z24,z778,z6]),(0,[z0,z1,z3,z130,z769,z6]),(0,[z0,z260,z1,z2,z132,z6])],[(0,[z171,z711,z2,z3,z4,z6]),(0,[z0,z59,z1,z3,z4,z60])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 548) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 548).take 539) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1087).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1088)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [548, 539, 1] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 123).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 123).take 133).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [123, 133] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

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

end PEqualNP.Outside.L_meta_47084

theorem PEqualNP.Outside.L_meta_47084 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241384 * 2 ^ 32 + 3907578016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241384 * 2 ^ 32 + 3907578016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_47084.solve