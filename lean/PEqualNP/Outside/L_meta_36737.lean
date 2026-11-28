import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36737

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
  Nat.testBit (4008372970 * 2 ^ 32 + 4006144136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x402400b204a12054#64 ++ 0xba002410921a21aa#64 ++ 0xf8ff03ff1fe3f1ff#64 ++ 0xffd13e78fb1e31ff#64 : BitVec 256),
   (0x19082c0521465229#64 ++ 0x400c892620c19c15#64 ++ 0x3f1dfc0fe3fffe3f#64 ++ 0xffeec9a724e3fe3f#64 : BitVec 256),
   (0x2a41555002689482#64 ++ 0xb2b070c5c7034b4c#64 ++ 0x3fe1fff003fcffce#64 ++ 0xf2b0f1c7c703cfcc#64 : BitVec 256),
   (0x80019a694800e903#64 ++ 0x493b01f805b406f0#64 ++ 0xc001fffffc00fff3#64 ++ 0x5b3f01f807fc0ff0#64 : BitVec 256),
   (0x0001e38e93900002#64 ++ 0x9437fe00076ef000#64 ++ 0x0001ffffffff0003#64 ++ 0x9c3ffe0007fff000#64 : BitVec 256),
   (0x3490000000000003#64 ++ 0x403fdbeb68000000#64 ++ 0xfffe000000000003#64 ++ 0xe03ffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [7, 10]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [6, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0001ffffffff0003 0x9c3ffe0007fff000

def z1 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3f1dfc0fe3fffe3f 0xffeec9a724e3fe3f

def z2 : W := mkw 0x2001410002000002 0x903070c147024000 0x3fe1fff003fc0002 0xf030f1c7c703c000

def z3 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3fe1fff003fcffce 0xf2b0f1c7c703cfcc

def z4 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xfffe000000000003 0xe03ffffff8000000

def z5 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xf8ff03ff1fe3f1ff 0xffd13e78fb1e31ff

def z6 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc001fffffc00fff3 0x5b3f01f807fc0ff0

def z7 : W := mkw 0xa4919a694800e903 0x493b53f94db406f0 0xc0e3fffffc00fff3 0x5b3f37f8dffc0ff0

def z8 : W := mkw 0x00018a0900004003 0x403b012005a40410 0x0001fffffc00fe33 0x5b3f01a007fc0e30

def z9 : W := mkw 0x0001000000000002 0x0030000005000000 0x0001fff000000002 0x1030000007000000

def z10 : W := mkw 0x0000280501004001 0x400c892000c09410 0x0001fc0fe3fffe33 0xdf2ec9a004e3fe30

def z11 : W := mkw 0x1490000000000001 0x400f8b2a28000000 0xc01e000000000001 0x000f0e3838000000

def z12 : W := mkw 0x2000000000000002 0x003050c140000000 0x3fe0000000000002 0xe030f1c7c0000000

def z13 : W := mkw 0x3491104000008003 0x403fdbeb6d000240 0xfffffff00000ffc3 0xf23fffffff000fc0

def z14 : W := mkw 0x19080c0120465229 0x4008012620810c15 0x3f1c00000000fe3c 0x63c001a720000e3f

def z15 : W := mkw 0x3491e38e93900003 0xd43fffeb6f6ef000 0xffffffffffff0003 0xfc3ffffffffff000

def z16 : W := mkw 0x0001410002000000 0x9000200007024000 0x0001fff003fc0000 0x100000000703c000

def z17 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x0700fc00e01c0e00 0x002ec18704e1ce00

def z18 : W := mkw 0x54b400b204a12055 0xfa0faf3aba1a21aa 0xf8ff03ff1fe3f1ff 0xffdf3e78fb1e31ff

def z19 : W := mkw 0xc0259aeb4c81e957 0x493b05f815bc26f2 0xc01ffffffc03fff3 0x5f7f0ff83ffc3ff3

def z20 : W := mkw 0x000000a200802000 0x98002410021a20a0 0xc00103ff1fe3f1f3 0xdf113e78031e31f0

def z21 : W := mkw 0x0000618693900000 0x9404fe00024af000 0x0000000003ff0000 0x8400fe000003f000

def z22 : W := mkw 0x2490000000000002 0x003352c948000000 0xc0e2000000000000 0x00113658d8000000

def z23 : W := mkw 0x2491e38e93900002 0x9437fec94f6ef000 0xc0e3ffffffff0003 0x9c3ffe58dffff000

def z24 : W := mkw 0x2a41554002489482 0x00b050c545014a44 0x0700fc00001c0e00 0x0020c1870401ce00

def z25 : W := mkw 0x3b497d55236ed6ab 0xf2bcf9e7e7c3df5d 0x3ffdffffe3ffffff 0xfffef9e7e7e3ffff

def z26 : W := mkw 0x3d982c052146522b 0x403fdbef68c19c15 0xfffffc0fe3fffe3f 0xfffffffffce3fe3f

def z27 : W := mkw 0xb4919a694800e903 0x493fdbfb6db406f0 0xfffffffffc00fff3 0xfb3ffffffffc0ff0

def z28 : W := mkw 0x0000000000000000 0x0000000000000000 0xf8fe000000000003 0xe0113e78f8000000

def z29 : W := mkw 0x1000000000000001 0x400c892220000000 0x3f1c000000000003 0xe02ec9a720000000

def z30 : W := mkw 0x09082c0521465228 0x0000000400c19c15 0x0001fc0fe3fffe3c 0x1fc0000004e3fe3f

def z31 : W := mkw 0x64b400b204a12056 0xba3376d9da1a21aa 0xf8ff03ff1fe3f1ff 0xffd13e78fb1e31ff

def z32 : W := mkw 0x80019a694800e900 0x0900001005b406f0 0xc001fffffc00fff3 0x5b11007807fc0ff0

def z33 : W := mkw 0x0000080100004001 0x4008012000800410 0x381dfc0fe3e3fe3f 0xffee09a024e23e3f

def z34 : W := mkw 0x3490000000000002 0x0037dacb68000000 0xfffe000000000000 0xa011fe5ff8000000

def z35 : W := mkw 0x592c2cb725e7727d 0xfa0cad36b2dbbdbf 0x3f1dffffffffffff 0xffeec9a727ffffff

def z36 : W := mkw 0x0001e30c93100002 0x0437da000564d000 0x0001fffffc1c0003 0x183fc00007fdc000

def z37 : W := mkw 0x0000008200800000 0x90002400020a2000 0x000103ff1fe30003 0x9c113e00031e3000

def z38 : W := mkw 0x0000008200800000 0x90002400020a2000 0x000103ff1fe30000 0x1c000000031e3000

def z39 : W := mkw 0x1000000000000000 0x0004880220000000 0x3f1c000000000000 0xa000c80720000000

def z40 : W := mkw 0x0a41555002689480 0xb280200487034b4c 0x3f01fff003fcffce 0xf2a0c1870703cfcc

def z41 : W := mkw 0x2000000000000002 0x003050c140000000 0xfffe000000000003 0xe031fffff8000000

def z42 : W := mkw 0x0001820800000002 0x0033000005240000 0x000003f01c000000 0x00110000031c0000

def z43 : W := mkw 0x3b483c55216ed6a9 0x628c89e7e0c19f5d 0x3ffdfc0fe3ffffff 0xffeec9e7e4e3ffff

def z44 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0x0700000000000003 0x803fff8700000000

def z45 : W := mkw 0x0001820800000002 0x0033000005240000 0x0001fffffc000003 0x183f000007fc0000

def z46 : W := mkw 0x8001fbefdb90e903 0xdd3ffff807fef6f0 0xc001fffffffffff3 0xdf3ffff807fffff0

def z47 : W := mkw 0x80008a2948006903 0x493b01f800b404b0 0xc000000ffc000033 0x493f01f800fc0030

def z48 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001fc0fe0000003 0x182e000004e00000

def z49 : W := mkw 0x0001e38e93900000 0x94002400076ef000 0x0001ffffffff0000 0x1c00000007fff000

def z50 : W := mkw 0x3490000000000001 0x400801eb68000000 0xfffe000000000000 0x600001fff8000000

def z51 : W := mkw 0x0800040000401000 0x0000000400010804 0x3f01fc0003fcfe0e 0xf2a0c1870403ce0c

def z52 : W := mkw 0x0a41555002689480 0xb280200487034b4c 0x0001fff003fcffcc 0x128000000703cfcc

def z53 : W := mkw 0x0800040000401000 0x0000000400010804 0x3f1dfc0f03fffe3f 0xffe0c9a72403fe3f

def z54 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3f1c000fe3ff003d 0xadcec82720e3f03f

def z55 : W := mkw 0x3490000000000001 0x400fdb2b68000000 0xfffe000000000001 0xa00ffe3ff8000000

def z56 : W := mkw 0x3490000000000001 0x400f8beb68000000 0xfffe000000000001 0x600f0ffff8000000

def z57 : W := mkw 0x2a40451002681480 0xb2807005c203490c 0x3fe0000003fc000c 0xa080f007c003c00c

def z58 : W := mkw 0x2a41f7de93f89482 0xb6b7fec5c76ffb4c 0x3fe1ffffffffffcf 0xfebfffc7c7ffffcc

def z59 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc000fc00e000fff0 0x432e01f804e00ff0

def z60 : W := mkw 0x3d982c0521465229 0x400cdb2768c19c15 0x3ffffc0fe3fffe3f 0xffeeffa7fce3fe3f

def z61 : W := mkw 0x3490002000002003 0x483fdbfb681000a0 0xffff03ff1c00f1f3 0xfb3ffffffb1c01f0

def z62 : W := mkw 0x80019a494800c903 0x413b01e805a40650 0x0000fc00e0000e00 0x002e018004e00e00

def z63 : W := mkw 0x9909be6d6946fb2b 0x493f89fe25f59ef5 0xff1dffffffffffff 0xffffc9ff27ffffff

def z64 : W := mkw 0xc0248abb4ca16955 0xfb0b253892be25ba 0xf8ff03ffffe3f1ff 0xffdf3e78fbfe31ff

def z65 : W := mkw 0x74b4009204a10054 0xb204fe03fa0a210a 0x3ffe000003e3000c 0xa4c0fe07f802300f

def z66 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3f1cfc00e3ff0e0c 0xa4eec98724e3fe0f

def z67 : W := mkw 0x80019a494800c903 0x413b01e805a40650 0x0001fffffc000e03 0x183f018007fc0e00

def z68 : W := mkw 0x0000080100004001 0x4008012000800410 0x0001fc0fe000fe33 0x5b2e01a004e00e30

def z69 : W := mkw 0x4024009204a10054 0xb2002400920a210a 0x38fe000003e3000c 0xa4c03e00f802300f

def z70 : W := mkw 0x7ef555f206e9b4d7 0xfabfffffff1b6bee 0xffffffff1fffffff 0xffffffffff1fffff

def z71 : W := mkw 0x4024a2be95b12054 0xbe07ae10927eb1aa 0xf8ff03ffffe3f1ff 0xffdf3e78fbfe31ff

def z72 : W := mkw 0x3491820800000003 0x403fdbeb6d240000 0xfffffffffc000003 0xf83ffffffffc0000

def z73 : W := mkw 0x0000000000000000 0x0000000000000000 0x381c000003e3000c 0xa4c008002002300f

def z74 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0x3ffe000000000000 0xa02eff87f8000000

def z75 : W := mkw 0x2a41d75802689482 0xb2b370c5c7274b4c 0x3fe1fffffffcffcf 0xfabff1c7c7ffcfcc

def z76 : W := mkw 0x800018614800e901 0x490801f8009006f0 0xc00000000000fff0 0x430001f800000ff0

def z77 : W := mkw 0xea65dffb4ee9fdd7 0xfbbb75fdd7bf6ffe 0xffffffffffffffff 0xffffffffffffffff

def z78 : W := mkw 0xb4919a494800c903 0x413fdbeb6da40650 0x0700fc00e0000e00 0x002ec18704e00e00

def z79 : W := mkw 0x9909be4d6946db2b 0x413f89ee25e59e55 0x3f1dfc0fe3fffe3f 0xffeec9a724e3fe3f

def z80 : W := mkw 0x800118614800e903 0x493801f8059006f0 0xc001fff00000fff2 0x533001f807000ff0

def z81 : W := mkw 0x800192684800a902 0x093300d8053402e0 0xc00003f01c0001c0 0x00110058031c01c0

def z82 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc00003f01c00fff0 0x431101f8031c0ff0

def z83 : W := mkw 0x0909ef8fb3d65228 0x9400240407effc15 0x0001fffffffffe3c 0x1fc0000007fffe3f

def z84 : W := mkw 0x1490000000000001 0x4008012a28000000 0xc01e000000000000 0x0000003838000000

def z85 : W := mkw 0x8000082148006901 0x49080138009004b0 0xc000000000000030 0x0100003800000030

def z86 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3f1cfc00e01c0e03 0xe02ec9a724e1ce00

def z87 : W := mkw 0x80019a694800e902 0x0933001005b406f0 0x0001fffffc00fff3 0x1b3f000007fc0ff0

def z88 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xf81dffffffe3ffff 0xffff09f827fe3fff

def z89 : W := mkw 0x0800041000601000 0xb20020048203090c 0x3fe1fff003fcffce 0xf2b0f1c7c703cfcc

def z90 : W := mkw 0x592c2cb725e7727d 0xfa0cad36b2dbbdbf 0xffffffffffffffff 0xffffffffffffffff

def z91 : W := mkw 0x0000002000002000 0x08000010001000a0 0xc00003f01c0001c0 0x00110058031c01c0

def z92 : W := mkw 0x08000c0100405001 0x4008012400810c14 0x3f01fc0fe3fcfe3f 0xfbaec1a704e3ce3c

def z93 : W := mkw 0x0000000000000003 0x403b01e800000000 0xc000000000000003 0x403f01f800000000

def z94 : W := mkw 0x8001fbefdb90e900 0x9d00241007fef6f0 0x0001fffffffffff0 0x1f00000007fffff0

def z95 : W := mkw 0x0001eb8f93904003 0xd43fff2007eef410 0x0001fffffffffe33 0xdf3fffa007fffe30

def z96 : W := mkw 0x6a6555f206e9b4d6 0xbab074d5d71b6bee 0xffffffff1fffffff 0xfff1ffffff1fffff

def z97 : W := mkw 0x2a40659693f81480 0xb684fe05c24bf90c 0x3fe0000003ff000c 0xa480fe07c003f00c

def z98 : W := mkw 0x3490000000000003 0x403851eb68000000 0xfffe000000000002 0xe030f1fff8000000

def z99 : W := mkw 0x0000008200800000 0x90002400020a2000 0xf8ff03ff1fe30003 0xfc113e78fb1e3000

def z100 : W := mkw 0x1108280521064229 0x400c892220c09411 0x001c000fe0030031 0x0d4e082020e03033

def z101 : W := mkw 0x1000000000000001 0x400c892220000000 0x001c000000000001 0x000e082020000000

def z102 : W := mkw 0x0001105000208002 0xb23020c087020348 0x38e1fff003e0ffce 0xf2b031c0c7020fcc

def z103 : W := mkw 0x0000000000000000 0x0004da0000000000 0x0000000000000000 0x8000fe0000000000

def z104 : W := mkw 0x0001514002008002 0x903070c007024240 0x0001fff003fcffc2 0xd230f1c00703cfc0

def z105 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0x000103ff1fe3f1fc 0x1fc00000031e31ff

def z106 : W := mkw 0x3491e38e93900002 0x9437fe036f6ef000 0x3fffffffffff0003 0xbc3ffe07fffff000

def z107 : W := mkw 0x0000828a90900000 0x04030600002c2000 0x000000001c000000 0x00010600001c0000

def z108 : W := mkw 0x3490000000000001 0x400801eb68000000 0xfffe000000000003 0xe0113ffff8000000

def z109 : W := mkw 0x0000001000200000 0xb200200082020108 0x38e103f003e0f1ce 0xf2903040c30201cc

def z110 : W := mkw 0x0001e39e93b00002 0xb637fe00876ef108 0x38e1fffffffff1cf 0xfebffe40c7fff1cc

def z111 : W := mkw 0x0000002000002000 0x08000010001000a0 0xc000000f1c000031 0x09010038001c0030

def z112 : W := mkw 0x0001c38a92900002 0x94337600072e6000 0x000003f01c000000 0x00113600031c0000

def z113 : W := mkw 0x2a41d7da92f89482 0xb6b376c5c72f6b4c 0x3fe1fff01ffcffce 0xf2b1f7c7c71fcfcc

def z114 : W := mkw 0x3ed1f7de93f89483 0xf6bfffefef6ffb4c 0xffffffffffffffcf 0xfebfffffffffffcc

def z115 : W := mkw 0x3490000000000000 0x0004da0368000000 0x3ffe000000000000 0xa000fe07f8000000

def z116 : W := mkw 0x2a4155700268b482 0xbab070d5c7134bec 0xffe1ffff1ffcffff 0xfbb1f1ffc71fcffc

def z117 : W := mkw 0x2a41554002489482 0x00b050c545014a44 0x0701fff0001cffc2 0x5230c1c70701cfc0

def z118 : W := mkw 0x0001e30c93100002 0x0437da000564d000 0x0000fc00e01c0000 0x002ec00004e1c000

def z119 : W := mkw 0x359828052106422b 0x403fdbeb68c09411 0xfffe000fe0030033 0xed7ffffff8e03033

def z120 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xf8fe03f01c0001c3 0xe0113e78fb1c01c0

def z121 : W := mkw 0x3d9824042146122b 0x403fdbef68419805 0xfffe000003ff000f 0xe4fffffff803f00f

def z122 : W := mkw 0x6a6555d206e994d6 0xb2b074c5d70b6b4e 0x3ffffff003ffffce 0xf6f0ffc7ff03ffcf

def z123 : W := mkw 0x3b49ffdfb3fed6ab 0xf6bfffe7e7efff5d 0x3ffdffffffffffff 0xffffffe7e7ffffff

def z124 : W := mkw 0x0000418292900000 0x94007600020a6000 0x0000000000000000 0x0000360000000000

def z125 : W := mkw 0xaa419e794868fd83 0x6bbb01fdc5b50ffc 0xffe1fffffc00ffff 0x7bbf01ffc7fc0ffc

def z126 : W := mkw 0x9108aa2d69066b29 0x490f893a20f494b1 0xc01c000ffc030031 0x0d4f083820fc3033

def z127 : W := mkw 0x592c24b625e7327c 0xba04ac16b25bb9af 0xffff03ff1ffff1ff 0xffd1fe7ffb1ff1ff

def z128 : W := mkw 0x80019a694800e900 0x0900001005b406f0 0x0001fffffc00fff0 0x1b00000007fc0ff0

def z129 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3fe003f00000ffcc 0x629031c7c3000fcc

def z130 : W := mkw 0x09080c0120465228 0x0000000400810c15 0x000000000000fe3c 0x03c0000000000e3f

def z131 : W := mkw 0x592c0cb324e7727d 0xfa082536b29b2dbf 0xffff03ff1fe3ffff 0xffd13ffffb1e3fff

def z132 : W := mkw 0x2a40041000681480 0x22800005c001090c 0x3fe000000000000c 0x20800007c000000c

def z133 : W := mkw 0x2a40145000689482 0x22b050c5c0010b4c 0x3fe000000000ffce 0xe2b0f1c7c0000fcc

def z134 : W := mkw 0x0000000000000000 0x0000000000000000 0x000103ff1c000003 0x18110000031c0000

def z135 : W := mkw 0x2241515002288482 0xb2b070c1c7024348 0x00e003f0000001c0 0x00103040c30001c0

def z136 : W := mkw 0x0000200401000000 0x0004880000409000 0x0000000fe0030001 0x0c0e080000e03000

def z137 : W := mkw 0x6a65f7fe97f9b4d6 0xbeb7fed5d77ffbee 0xffffffffffffffff 0xffffffffffffffff

def z138 : W := mkw 0x402400a204812054 0x98002410121a20a2 0xc01f03ff1fe30033 0x9d513e383b1e3033

def z139 : W := mkw 0x3d982c0521465229 0x400c89ef68c19c15 0xfffffc0fe3fffe3f 0xffeec9fffce3fe3f

def z140 : W := mkw 0x0001c38a92900002 0x9437fe00072e6000 0x000003f01c000003 0x803ffe00031c0000

def z141 : W := mkw 0x592c0c312467727d 0x6a080136b0910dbf 0xfffe00000000fffc 0x63c001fff8000fff

def z142 : W := mkw 0x1908240421461228 0x0004880620419805 0x3f1c000003ff000c 0xa4c0c8072003f00f

def z143 : W := mkw 0x0001418202800002 0x90307400070a6000 0x0001ffff1fff0003 0x9c31fe00071ff000

def z144 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xf8fe000f1fe3003d 0xadc13e38f81e303f

def z145 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xc0e303ff1fe301c3 0x9c113e58db1e31c0

def z146 : W := mkw 0x80019a694800e901 0x490801f805b406f0 0xc001fffffc00fff0 0x5b0001f807fc0ff0

def z147 : W := mkw 0x0000a28e91900000 0x04078e00006cb000 0x0001fc0fffff0003 0x9c2fce0004fff000

def z148 : W := mkw 0x3d98240421461228 0x0004da0768419805 0x3ffe000003ff000c 0xa4c0fe07f803f00f

def z149 : W := mkw 0x0001e38e93900000 0x9407ae00076ef000 0x0001ffffffff0001 0x1c0f0e0007fff000

def z150 : W := mkw 0x2a40145000689480 0x228000c5c0010b4c 0x3fe1fc0003fcffce 0xf2a0c1c7c403cfcc

def z151 : W := mkw 0x4024001004210054 0x220000009000010a 0x38fe00000000000c 0x20c00000f800000f

def z152 : W := mkw 0x2241515002288482 0xb2b070c1c7024348 0x3fe003f0000001c2 0xe030f1c7c30001c0

def z153 : W := mkw 0xb4908a2948006903 0x493fdbfb68b404b0 0xfffe000ffc000033 0xe93ffffff8fc0030

def z154 : W := mkw 0xc0259afb4ca1e957 0xfb3b25f897be27fa 0xf8ffffffffe3ffff 0xffff3ff8fffe3fff

def z155 : W := mkw 0x1108080120064229 0x4008012220800411 0x001c000000000030 0x0140002020000033

def z156 : W := mkw 0x2000000000000000 0x000000c140000000 0x3fe0000000000000 0x600001c7c0000000

def z157 : W := mkw 0x1001e38e93900003 0xd43fff22276ef000 0x3f1dffffffff0003 0xfc3fffa727fff000

def z158 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x381dfffffffff03f 0xfffffe2027fff03f

def z159 : W := mkw 0x74b400b204a12057 0xfa3ffffbfa1a21aa 0xffff03ff1fe3f1ff 0xfffffffffb1e31ff

def z160 : W := mkw 0x0000208691900000 0x04048e000048b000 0x0000000000030000 0x04000e0000003000

def z161 : W := mkw 0x1000200401000001 0x400c892220409000 0x3f1dfc0fe3ff0003 0xfc2ec9a724e3f000

def z162 : W := mkw 0x19080c0120465229 0x4008012620810c15 0x3f1dfc0fe000fe3f 0x7bee01a724e00e3f

def z163 : W := mkw 0x2490000000000002 0x003352c948000000 0xffe2000000000002 0xe031f7dfd8000000

def z164 : W := mkw 0x0000000000000000 0x0000000000000000 0x381d000f03e3f03f 0xffc008202002303f

def z165 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xc7e2000000000000 0x003ff7dfd8000000

def z166 : W := mkw 0x800192684800a902 0x093300d8053402e0 0xc00103ff1c00f1f3 0x5b110078031c01f0

def z167 : W := mkw 0x4a6555f206e9b4d4 0xba802414971b6bee 0x0001ffff1ffffffc 0x1fc00000071fffff

def z168 : W := mkw 0x0801144000409002 0x003000c405010a44 0x3f01fff003fcffce 0xf2b0c1c70703cfcc

def z169 : W := mkw 0x2a40451002681480 0xb2807005c203490c 0x3fe1fc0003fcfe0e 0xf2a0f187c403ce0c

def z170 : W := mkw 0x402400a204812054 0x08000410101820a2 0xc01e000f1c030031 0x0d410e38381c3033

def z171 : W := mkw 0x0000e38e93900000 0x9407fe00026ef000 0x0000000fffff0001 0x8c0ffe0000fff000

def z172 : W := mkw 0x3d980c012046522b 0x403fdbef68810c15 0xfffe00000000fe3f 0xe3fffffff8000e3f

def z173 : W := mkw 0x0000208601800000 0x9004ac00024ab000 0x0001ffffffff0003 0x9c3ffe0007fff000

def z174 : W := mkw 0x0001104000008002 0x003000c005000240 0x0001fff00000ffc2 0x523001c007000fc0

def z175 : W := mkw 0x0001f3ce93908002 0x9437fec0076ef240 0x0001ffffffffffc3 0xde3fffc007ffffc0

def z176 : W := mkw 0x0001c30802000002 0x9033700007264000 0x0001fffffffc0003 0x983ff00007ffc000

def z177 : W := mkw 0x1108280521064229 0x400c892220c09411 0x001dfc0fe003fe33 0x5f6e09a024e03e33

def z178 : W := mkw 0x0000200401000000 0x0004880000409000 0x0001fc0fe3ff0003 0x9c2ec80004e3f000

def z179 : W := mkw 0x4024003004212054 0x2a000010901001aa 0xf8fe00000000f1fc 0x63c00078f80001ff

def z180 : W := mkw 0x3491410002000003 0xd03ffbeb6f024000 0xfffffff003fc0003 0xf03fffffff03c000

def z181 : W := mkw 0x2a41555002689480 0xb28020c5c7034b4c 0x3fe1fff003fcffcc 0x728001c7c703cfcc

def z182 : W := mkw 0xb4919a694800e903 0x493b01fb6db406f0 0xfffffffffc00fff3 0x7b3f01fffffc0ff0

def z183 : W := mkw 0x0001410002000002 0x9037fa0007024000 0x0001fff003fc0003 0x903ffe000703c000

def z184 : W := mkw 0x3490001000200003 0xf23ffbebea020108 0xffff03f003e0f1cf 0xf2bffffffb0201cc

def z185 : W := mkw 0xc0248aab4c816955 0x490b053810bc24b2 0xc01e000ffc030031 0x0d4f0e3838fc3033

def z186 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xf8ff03ff1fe3f1fc 0x7fc00078fb1e31ff

def z187 : W := mkw 0x4025e3be97b12054 0xbe002410977ef1aa 0xf8fffffffffff1ff 0xffd13e78fffff1ff

def z188 : W := mkw 0x80019a494800c903 0x413b01e805a40650 0x0001fff0e000ffc2 0x523e01c007e00fc0

def z189 : W := mkw 0xaa401c714868fd81 0x6b8801fdc0910ffc 0xffe000000000fffc 0x638001ffc0000ffc

def z190 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001fc000000fe02 0x5220018004000e00

def z191 : W := mkw 0x502400b204a12055 0xfa0cad32b21a21aa 0xffff03ff1fe3f1ff 0xfffffffffb1e31ff

def z192 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xc0e303ff1c00f1f3 0x5b113678db1c01f0

def z193 : W := mkw 0x0000001000200000 0xb200200082020108 0x000103f003e0f1cc 0x12800000030201cc

def z194 : W := mkw 0x09082c0521465228 0x0000000400c19c15 0x3f01fc0fe3fffe3e 0xffe0c18704e3fe3f

def z195 : W := mkw 0x80008a0948004901 0x410b012800a40410 0x00000000e0000000 0x000e000000e00000

def z196 : W := mkw 0x8a41df794a68fd80 0xbb80201487b74ffc 0x0001fffffffcfffc 0x1b80000007ffcffc

def z197 : W := mkw 0x0001a28e91900002 0x04378e00056cb000 0x0001fffffc030003 0x1c3f0e0007fc3000

def z198 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0xf8ffffffffff0003 0xfc3ffe78fffff000

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001000f03e3f03c 0x1fc000000002303f

def z200 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0x0700000000000000 0x002ec18700000000

def z201 : W := mkw 0x0001924800008002 0x003300c005240240 0x0001fffffc00ffc3 0x5a3f01c007fc0fc0

def z202 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3f1c000003fffe3c 0xe7c0c9a72003fe3f

def z203 : W := mkw 0xc02418714c21e955 0x6b0801f8909007fa 0xf8fe00000000fffc 0x63c001f8f8000fff

def z204 : W := mkw 0x0000000000000002 0x0033520000000000 0x0000000000000000 0x0011360000000000

def z205 : W := mkw 0x0000000000000002 0x0037da0000000000 0x0000000000000003 0x803ffe0000000000

def z206 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0x000003f01c0001c0 0x00000000031c01c0

def z207 : W := mkw 0xaa41d7784a68bd82 0xbbb370ddc7374bec 0xffe1fff01ffcffce 0xf2b1f1dfc71fcfcc

def z208 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xc71e000000000001 0x002fcfbf38000000

def z209 : W := mkw 0x602400b204a12056 0xba3074d1d21a21aa 0xffff03ff1fe3f1ff 0xfff1fffffb1e31ff

def z210 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0xfffffc0fe3fffe3f 0xfffffffffce3fe3f

def z211 : W := mkw 0x0000008200800002 0x9037fe00020a2000 0x000103ff1fe30003 0x9c3ffe00031e3000

def z212 : W := mkw 0x80019a494800c903 0x413b01e805a40650 0xc000fc00e0000e03 0x403f01f804e00e00

def z213 : W := mkw 0x0000a28e91900000 0x04078e00006cb000 0x0000000ffc030001 0x0c0f0e0000fc3000

def z214 : W := mkw 0x2a40145000689480 0x228000c5c0010b4c 0x3fe000000000ffcc 0x628001c7c0000fcc

def z215 : W := mkw 0x3fd97d55236ed6ab 0xf2bffbefefc3df5d 0xffffffffe3ffffff 0xffffffffffe3ffff

def z216 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xc0e303ff1fe3f1fc 0x1fd13658db1e31ff

def z217 : W := mkw 0x26d1515002288482 0xb2b372c9cf024348 0xc0e203f0000001c0 0x00113658db0001c0

def z218 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0x0001fffffc00fff0 0x1b2e018007fc0ff0

def z219 : W := mkw 0x1909ef0db356522b 0x443fdb2625e5dc15 0x0700fc00e01c0e00 0x002ec18704e1ce00

def z220 : W := mkw 0x2490000000000002 0x0037dac948000000 0xc0e2000000000003 0x803ffe58d8000000

def z221 : W := mkw 0x0000000000000002 0x0037da0000000000 0x0000000000000000 0x002ec00000000000

def z222 : W := mkw 0x3490000000000001 0x400cdbeb68000000 0xfffe000000000000 0xe000fffff8000000

def z223 : W := mkw 0x512c28a72587627d 0x480c8d3230d8b4b3 0xc01e000ffc030031 0x0d4f0e3838fc3033

def z224 : W := mkw 0x0001e38e93900002 0x94332400076ef000 0x0001ffffffff0003 0x1c3f000007fff000

def z225 : W := mkw 0x3d99ef8fb3d6522b 0xd43fffef6feffc15 0xfffffffffffffe3f 0xfffffffffffffe3f

def z226 : W := mkw 0x4025e3be97b12056 0xbe37fe10977ef1aa 0xf8fffffffffff1ff 0xfffffe78fffff1ff

def z227 : W := mkw 0xb4919a694800e903 0x493fdbfb6db406f0 0xc701fffffc00fff3 0x5b3fc1ff07fc0ff0

def z228 : W := mkw 0x0000618693900002 0x9437fe00024af000 0x0000000003ff0003 0x843ffe000003f000

def z229 : W := mkw 0x2a41554002489482 0x00b050c545014a44 0x3f01fc0003fcfe0e 0xf2a0c1870403ce0c

def z230 : W := mkw 0x39082c052146522b 0x403cd9e760c19c15 0x3ffdfc0fe3fffe3f 0xfffef9e7e4e3fe3f

def z231 : W := mkw 0x3ed0451002681483 0xf2bffbefea03490c 0xfffe000003fc000f 0xe0bffffff803c00c

def z232 : W := mkw 0x8000aaafd9906901 0x4d0f8f3800fcb4b0 0xc000000ffc030031 0x0d0f0e3800fc3030

def z233 : W := mkw 0x80019a694800e901 0x4908013005b406f0 0x0001fffffc00fff3 0x5b2e01a007fc0ff0

def z234 : W := mkw 0x0000002000002000 0x08000010001000a0 0xc00103ff1c00f1f3 0x5b110078031c01f0

def z235 : W := mkw 0x3d982c052146522b 0x403fdbef68c19c15 0xfffefc00e01c0e03 0xe03ffffffce1ce00

def z236 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc000fc0ffc000e31 0x092f01b804fc0e30

def z237 : W := mkw 0xc0259afb4ca1e954 0xbb00241097be27fa 0x0001ffffffe3fffc 0x1fc0000007fe3fff

def z238 : W := mkw 0xb4919a494800c903 0x413fdbeb6da40650 0xfffefc00e0000e03 0xe03ffffffce00e00

def z239 : W := mkw 0x1108280521064229 0x400c892220c09411 0x00000000e0000000 0x000e000000e00000

def z240 : W := mkw 0x0001e38e93900002 0x0437de00056cf000 0x0000fc0ffc1f0001 0x0c2fce0004fdf000

def z241 : W := mkw 0x1909ef8fb3d6522b 0xd43fff2627effc15 0x3f1dfffffffffe3f 0xffffffa727fffe3f

def z242 : W := mkw 0xa0019a694800e903 0x493b51f945b406f0 0xffe1fffffc00fff3 0xfb3ff1ffc7fc0ff0

def z243 : W := mkw 0x4025e39e97b10056 0xb637fe00976ef10a 0x38ffffffffff000f 0xbcfffe00fffff00f

def z244 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x07e0fff0001c0fc0 0x0030f1c7c701cfc0

def z245 : W := mkw 0x0000001000200000 0xb200200082020108 0xf8ff03f003e0f1cf 0xf2913e78fb0201cc

def z246 : W := mkw 0x19082c1521665229 0xf20ca926a2c39d1d 0x3ffdffffe3ffffff 0xfffef9e7e7e3ffff

def z247 : W := mkw 0x2a41e79e93f81482 0xb6b7fe05c76ff90c 0x3fe1ffffffff000f 0xbcbffe07c7fff00c

def z248 : W := mkw 0x4024003004212054 0xba002010921201aa 0xf8ff03f003e0f1fe 0xf3d03078fb0201ff

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0x381c000000000003 0xe000082020000000

def z250 : W := mkw 0x0000000000000000 0x0000000000000000 0xf8ff000f03e3f03f 0xffd13e78f802303f

def z251 : W := mkw 0x0000000000000001 0x4008012000000000 0x0000000000000003 0x402e01a000000000

def z252 : W := mkw 0x3490000000000003 0x403b53eb68000000 0xfffe000000000000 0x601137fff8000000

def z253 : W := mkw 0x0001410002000002 0x9030700007024000 0x0001fff003fc0002 0x9030f0000703c000

def z254 : W := mkw 0x0000001000200000 0xb200200082020108 0x38fd03ff03e3f1ff 0xffd03860e30231ff

def z255 : W := mkw 0x80019a694800e902 0x093300d805b406f0 0xc001fffffc00fff0 0x1b11005807fc0ff0

def z256 : W := mkw 0x2ed1555002689482 0xb2b372cdcf034b4c 0xffe3fff003fcffce 0xf2b1f7dfdf03cfcc

def z257 : W := mkw 0x2490000000000003 0x403b53e948000000 0xc0e2000000000003 0x403f37f8d8000000

def z258 : W := mkw 0x2000001000200002 0xb23070c1c2020108 0x3fe103f003e0f1ce 0xf2b0f1c7c30201cc

def z259 : W := mkw 0x0001820800000000 0x0000000005240000 0x0001fffffc000000 0x1800000007fc0000

def z260 : W := mkw 0x2800040000401002 0x003050c540010804 0x3fe1fc0003fcfe0e 0xf2b0f1c7c403ce0c

def z261 : W := mkw 0x74b400b204a12057 0xfa3ffffbfa1a21aa 0xfffe03f01c0001c3 0xe03ffffffb1c01c0

def z262 : W := mkw 0x0001104000008000 0x0000000005000240 0x0001fff00000ffc0 0x1200000007000fc0

def z263 : W := mkw 0x0000000000000002 0x0037da0000000000 0xf8fe000000000003 0xe03ffe78f8000000

def z264 : W := mkw 0xc0259afb4ca1e957 0xfb3b25f897be27fa 0xc0e3fffffc00fff3 0x5b3f37f8dffc0ff0

def z265 : W := mkw 0x0001e38e93900000 0x94002400076ef000 0x0001ffffffff0003 0x9c113e0007fff000

def z266 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0000fff0fc1c0000 0x003ff60007fdc000

def z267 : W := mkw 0x1490000000000003 0x403fdb2a28000000 0xc01e000000000003 0x803ffe3838000000

def z268 : W := mkw 0x2a41555002689482 0x22b050c5c5014b4c 0x3fe0fc00001cffcc 0x62a0c1c7c401cfcc

def z269 : W := mkw 0x6a6555700669b4d6 0xbab070d5d7134bee 0xfffffff003fcfffe 0xf3f0f1ffff03cfff

def z270 : W := mkw 0x0909ef8fb3d6522a 0x9437fe0407effc15 0x0001fffffffffe3f 0x9ffffe0007fffe3f

def z271 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xc0e203f01c0001c0 0x00113658db1c01c0

def z272 : W := mkw 0xd92dbeff6de7fb7f 0xfb3fadfeb7ffbfff 0xffffffffffffffff 0xffffffffffffffff

def z273 : W := mkw 0x09082c0521465228 0x0004880400c19c15 0x0001fc0fe3fffe3f 0x9feec80004e3fe3f

def z274 : W := mkw 0x0b497d55236ed6a8 0xb280200487c3df5d 0x0001ffffe3fffffc 0x1fc0000007e3ffff

def z275 : W := mkw 0xbd99be6d6946fb2b 0x493fdbff6df59ef5 0xffffffffffffffff 0xffffffffffffffff

def z276 : W := mkw 0x592c249625e7127c 0xb204ac06b24bb90f 0x3ffe000003ff000c 0xa4c0fe07f803f00f

def z277 : W := mkw 0x1490000000000001 0x400f8b2a28000000 0xf8fe000000000003 0xe01f3e78f8000000

def z278 : W := mkw 0x0000000000000002 0x0030500000000000 0x0000000000000002 0x8030f00000000000

def z279 : W := mkw 0x19096d052346522b 0xd03cf92627c3dc15 0x3f1dffffe3fffe3f 0xfffef9a727e3fe3f

def z280 : W := mkw 0x74b5e3be97b12057 0xfe3ffffbff7ef1aa 0xfffffffffffff1ff 0xfffffffffffff1ff

def z281 : W := mkw 0x2a40145000689480 0xb28020c5c2030b4c 0x3fe103f003e0ffce 0xf29031c7c3020fcc

def z282 : W := mkw 0x3ed1555002689483 0xf2bffbefef034b4c 0xfffffff003fcffcf 0xf2bfffffff03cfcc

def z283 : W := mkw 0x3ed1555002689483 0xf2bffbefef034b4c 0x3fe1fff003fcffce 0xf2bef1c7c703cfcc

def z284 : W := mkw 0x1000080100004001 0x400c892220800410 0x3f1dfc0fe000fe33 0xfb2ec9a724e00e30

def z285 : W := mkw 0x09082c0521465228 0x0000000400c19c15 0x0000fc00e01c0e00 0x0000000004e1ce00

def z286 : W := mkw 0x0000001000200000 0xb200200082020108 0x38e0000003e0000c 0xa0803000c002000c

def z287 : W := mkw 0x0000410002000000 0x9000700002024000 0x0000000003fc0000 0x8000f0000003c000

def z288 : W := mkw 0x9909be6d6946fb2b 0x493f89fe25f59ef5 0xc701fffffc1cfff3 0x5b3fc1ff07fdcff0

def z289 : W := mkw 0x19093c452146d22b 0x403c89e625c19e55 0x3f1dffffe3ffffff 0xfffec9e727e3ffff

def z290 : W := mkw 0x3491e30c93100003 0x443fdbeb6d64d000 0xfffefc00e01c0003 0xe03ffffffce1c000

def z291 : W := mkw 0x482404b204e13054 0xba002414921b29ae 0xffffffff1fffffff 0xfff1ffffff1fffff

def z292 : W := mkw 0x2490000000000002 0x003352c948000000 0x0000000000000000 0x0000000000000000

def z293 : W := mkw 0x4025e3ae97912056 0x9c37fe10177ef0a2 0xc01fffffffff0033 0x9d7ffe383ffff033

def z294 : W := mkw 0xaa41df794a68fd83 0xfbbb71fdc7b74ffc 0xffe1fffffffcffff 0xfbbff1ffc7ffcffc

def z295 : W := mkw 0x1490000000000003 0x403f8bea28000000 0xc01e000000000003 0x403f0ff838000000

def z296 : W := mkw 0x0000000000000000 0x0000000000000000 0x38fe000000000000 0xa0003e00f8000000

def z297 : W := mkw 0x0000002000002000 0x08000010001000a0 0xc00000000000f1f0 0x43000078000001f0

def z298 : W := mkw 0x1490000000000001 0x400f8b2a28000000 0x0000000000000000 0x000e000000000000

def z299 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x0701fc0fe3fffe3c 0x1feec18704e3fe3f

def z300 : W := mkw 0x2a40451002681480 0xb2807005c203490c 0x3fe103f003fcf1ce 0xf290f047c303c1cc

def z301 : W := mkw 0x19086586b3d61228 0x9404fe06224bf805 0x3f1c000003ff000c 0xa4c0fe072003f00f

def z302 : W := mkw 0x1108280521064229 0x400c892220c09411 0x381d000fe3e3f03f 0xffce082020e2303f

def z303 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xf8fffffffc00fff3 0xfb3f3ff8fffc0ff0

def z304 : W := mkw 0x0000200401000000 0x0004880000409000 0x0000000003ff0000 0x8400c8000003f000

def z305 : W := mkw 0x1908ae8fb1d65229 0x440f8f2620edbc15 0x3f1dfc0ffffffe3f 0xffefcfa724fffe3f

def z306 : W := mkw 0x2a40144000489480 0x008000c540010a44 0x0700000000000e00 0x0000018700000e00

def z307 : W := mkw 0x0001e38e93900000 0x9404ac00076ef000 0x0001ffffffff0003 0x9c2ec80007fff000

def z308 : W := mkw 0x0000000000000000 0x0000000000000000 0x000103f00000f1c2 0x52100040030001c0

def z309 : W := mkw 0x80008a2948006901 0x490b013800b404b0 0xc000000ffc000031 0x090f003800fc0030

def z310 : W := mkw 0x0000a28e91900000 0x9407ae00026eb000 0x000103ffffe30003 0x9c1f3e0003fe3000

def z311 : W := mkw 0xa241d3784a28ad82 0xbbb370d9c73643e8 0xc0e003f01c0001c0 0x00113058c31c01c0

def z312 : W := mkw 0x2a41f7de93f89482 0xb6b074c5c76ffb4c 0x3fe1ffffffffffce 0xfeb0f1c7c7ffffcc

def z313 : W := mkw 0x0001822800002002 0x08330010053400a0 0xc001fffffc00f1f3 0x5b3f007807fc01f0

def z314 : W := mkw 0x1908240421461228 0x0004880620419805 0x3f1dfc0fe3ff000f 0xbceec80724e3f00f

def z315 : W := mkw 0x3d982c052146522b 0x403fdbef68c19c15 0x3f1dfc0fe3fffe3f 0xffeec9a724e3fe3f

def z316 : W := mkw 0x0001410002000002 0x9030700007024000 0x000003f000000000 0x0010300003000000

def z317 : W := mkw 0x512c28b725a7627d 0xfa0cad32b2dab5bb 0xf8ff03ffffe3f1ff 0xffdf3e78fbfe31ff

def z318 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3ffdffff03ffffff 0xfff0f9e7e703ffff

def z319 : W := mkw 0x3ed1554002489483 0x40bfdbef6d014a44 0xfffefc00001c0e03 0xe03ffffffc01ce00

def z320 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3fe0fc0003fc0e0c 0xa0a0f187c403ce0c

def z321 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x0701fc0fe01cfe33 0x5b2ec1a704e1ce30

def z322 : W := mkw 0x402400b204a12054 0x2a000410901821aa 0xf8fe000f1c03f1fd 0x6fc10e78f81c31ff

def z323 : W := mkw 0x3ed0145000689483 0x62bfdbefe8010b4c 0xfffe00000000ffcf 0xe2bffffff8000fcc

def z324 : W := mkw 0x0000618693900000 0x94002400024af000 0x0000000003ff0000 0x040000000003f000

def z325 : W := mkw 0x0001c38a92900002 0x94337600072e6000 0x0001fff01ffc0002 0x9031f600071fc000

def z326 : W := mkw 0xa241db794a28ed83 0xfbbb71f9c7b647f8 0xc0e1fffffc00fff3 0x5b3f31f8c7fc0ff0

def z327 : W := mkw 0x2a40450002481480 0x0080500540014804 0x07000000001c0000 0x0000c0070001c000

def z328 : W := mkw 0x402400a204812054 0x08000410101820a2 0xc01f03ff1c03f1f3 0x5f510e783b1c31f3

def z329 : W := mkw 0x8001fb4ddb10c903 0x453fdbe805e4d650 0x0000fc00e01c0e00 0x002ec18004e1ce00

def z330 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001000f0000f033 0x5b00002000000030

def z331 : W := mkw 0x19080c0120465229 0x4008012620810c15 0x0700000000000e00 0x0000018700000e00

def z332 : W := mkw 0x3490000000000002 0x0037da0368000000 0x3ffe000000000003 0xa03ffe07f8000000

def z333 : W := mkw 0x0001a20c01000002 0x0037880005649000 0x0001ffffffff0003 0x9c3fc80007fff000

def z334 : W := mkw 0x4024002004012054 0x08000010101000a2 0xc01e000000000030 0x0140003838000033

def z335 : W := mkw 0x94919a694800e903 0x493f8bfa2db406f0 0xc01ffffffc00fff3 0x5b3f0ff83ffc0ff0

def z336 : W := mkw 0x3490000000000001 0x400c89eb68000000 0xfffe000000000003 0xe02ec9fff8000000

def z337 : W := mkw 0xc0259a794c21e957 0x6b3b01f895b407fa 0xf8fffffffc00ffff 0x7bff01f8fffc0fff

def z338 : W := mkw 0x402400b204a12057 0xfa3b25f8921a21aa 0xf8ff03ff1fe3f1ff 0xffff3ff8fb1e31ff

def z339 : W := mkw 0x2491c38a92900002 0x943376c94f2e6000 0xc0e203f01c000000 0x00113658db1c0000

def z340 : W := mkw 0x8001924848008902 0x013300c805240240 0x0000000000000000 0x0000000000000000

def z341 : W := mkw 0x0000008200800000 0x90002400020a2000 0x000003f01c000000 0x00113600031c0000

def z342 : W := mkw 0x80009a694800e901 0x490b01f800b406f0 0xc000000ffc00fff1 0x4b0f01f800fc0ff0

def z343 : W := mkw 0x1908240421461228 0x0004880620419805 0x07000000001c0000 0x0000c0070001c000

def z344 : W := mkw 0x80019a694800e902 0x093000d005b406f0 0x0001fffffc00fff2 0x5b3001c007fc0ff0

def z345 : W := mkw 0xaa41df594a68dd83 0xf3bb71edc7a74f5c 0x3fe1fff0e3fcffce 0xf2bef1c7c7e3cfcc

def z346 : W := mkw 0x3491e30c93100003 0x443fdbeb6d64d000 0x0700fc00e01c0000 0x002ec18704e1c000

def z347 : W := mkw 0x80008a2948006900 0x0900001000b404b0 0x0000000ffc000030 0x0900000000fc0030

def z348 : W := mkw 0x0000820800000000 0x0003000000240000 0x0000000ffc000001 0x080f000000fc0000

def z349 : W := mkw 0x4024009204a10054 0xb2002400920a210a 0x38ff000f03e3f03f 0xffc03e20f802303f

def z350 : W := mkw 0x0001618693900002 0x9434fe00074af000 0x0001fff003ff0002 0x9430fe000703f000

def z351 : W := mkw 0x1800040000401001 0x400c892620010804 0x3f1dfc0003fcfe0f 0xf2aec9a72403ce0c

def z352 : W := mkw 0x402400b204a12056 0xba37fe10921a21aa 0xf8ff03ff1fe3f1ff 0xfffffe78fb1e31ff

def z353 : W := mkw 0x2a40555002689480 0xb28070c5c2034b4c 0x3fe0000003fcffcc 0xe280f1c7c003cfcc

def z354 : W := mkw 0x0001e30c93100002 0x0437da000564d000 0x0001fc0fe3ff0003 0x9c2ec80004e3f000

def z355 : W := mkw 0x80019a694800e901 0x490b013805b406f0 0xc001fffffc00fff1 0x1b0f003807fc0ff0

def z356 : W := mkw 0x4024009204a10054 0xb2002400920a210a 0x38ff03f003e3f1ce 0xf6d03e40fb0231cf

def z357 : W := mkw 0x74b4003004212055 0x6a0801fbf81001aa 0xfffe00000000f1fc 0x63c001fff80001ff

def z358 : W := mkw 0x09082c0521465228 0x0000000400c19c15 0x381dfc0fe3fffe3f 0xffc0082024e3fe3f

def z359 : W := mkw 0x0000000000000000 0x0000000000000000 0xf8fe000000000000 0x60000078f8000000

def z360 : W := mkw 0x4025e3be97b12054 0xbe002410977ef1aa 0x0001fffffffff1fc 0x1fc0000007fff1ff

def z361 : W := mkw 0x800018614800e901 0x490801f8009006f0 0xc00103ff1c00fff3 0x5b1101f8031c0ff0

def z362 : W := mkw 0x0000000000000003 0x403fdbe800000000 0xc000000000000003 0xc03ffff800000000

def z363 : W := mkw 0x4024003004212054 0x2a000010901001aa 0xf8ff000f03e3f1ff 0xffc00878f80231ff

def z364 : W := mkw 0x99099e696846fb2b 0x493b01fe25b50ef5 0xff1dfffffc00ffff 0x7bff01ff27fc0fff

def z365 : W := mkw 0x3ed1554002489483 0x40bfdbef6d014a44 0x0700fc00001c0e00 0x002ec1870401ce00

def z366 : W := mkw 0x0a40451002681480 0xb28020048203490c 0x0000000003fc000c 0x008000000003c00c

def z367 : W := mkw 0xc02418f34ca1e955 0xfb0825f8929a27fa 0xf8ff03ff1fe3ffff 0xffd13ff8fb1e3fff

def z368 : W := mkw 0x19082c0521465229 0x4008012620c19c15 0x3f1dfc0fe3fffe3c 0x7fc001a724e3fe3f

def z369 : W := mkw 0x4024003004212054 0x2a000010901001aa 0xf8fe00000000f1ff 0xe3d13e78f80001ff

def z370 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc000fff0fc000fc0 0x003f01d807fc0fc0

def z371 : W := mkw 0x0001820800000002 0x0037da0005240000 0x0001fffffc000003 0x983ffe0007fc0000

def z372 : W := mkw 0x2a41f75c93789482 0xb6b7fac5c767db4c 0x3fe1fff0e3fcffce 0xf2bef1c7c7e3cfcc

def z373 : W := mkw 0x88019e694840f903 0x493b01fc05b50ef4 0xff01fffffffcffff 0xfbbfc1ff07ffcffc

def z374 : W := mkw 0x3a41555002689483 0xf2bcf9e7e7034b4c 0x3ffdfff003fcffcf 0xf2bef9e7e703cfcc

def z375 : W := mkw 0x1490a28e91900001 0x440f8f2a286cb000 0xc01e000ffc030001 0x0c0f0e3838fc3000

def z376 : W := mkw 0xbed1df794a68fd83 0xfbbffbffefb74ffc 0xfffffffffffcffff 0xfbbfffffffffcffc

def z377 : W := mkw 0x0001410002000002 0x0030500005004000 0x0000fc00001c0000 0x0020c0000401c000

def z378 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x000003f01fff0000 0x8411fe00031ff000

def z379 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z380 : W := mkw 0x0001c38a92900002 0x94337600072e6000 0x0001fffffc000003 0x183f360007fc0000

def z381 : W := mkw 0x2001e38e93900002 0x9437fec1476ef000 0x3fe1ffffffff0003 0xfc3fffc7c7fff000

def z382 : W := mkw 0x2b497d55236ed6aa 0xb2b070c5c7c3df5d 0x3fe1ffffe3fffffe 0xfff0f1c7c7e3ffff

def z383 : W := mkw 0x3490a28e91900003 0x443fdfeb686cb000 0xfffe000ffc030003 0xec3ffffff8fc3000

def z384 : W := mkw 0x8001baefd990e903 0x4d3f8ff805fcb6f0 0xc001fffffc03fff3 0x5f3f0ff807fc3ff0

def z385 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0x3f1c000000000003 0xe02ec9a720000000

def z386 : W := mkw 0x0000002000002000 0x08000010001000a0 0xf81d03ff1fe3f1ff 0xffd10878231e31ff

def z387 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xc01f03ff1fe3f1fd 0x1fc10e383b1e31ff

def z388 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0x3fe0000000000002 0xe03ef1c7c0000000

def z389 : W := mkw 0x3490000000000001 0x400801eb68000000 0x0700000000000000 0x0000018700000000

def z390 : W := mkw 0x0000000000000000 0x0000000000000000 0x38e0000000000002 0xe0103040c0000000

def z391 : W := mkw 0x0001e3ae93902002 0x9c37fe10077ef0a0 0xc001fffffffff1f3 0xdf3ffe7807fff1f0

def z392 : W := mkw 0x99081c616846fb29 0x490801fe20910ef5 0xff1c00000000fffc 0x63c001ff20000fff

def z393 : W := mkw 0x0000009200a00000 0xb2002400820a2108 0x38e103ff1fe3f1cf 0xfe913e40c31e31cc

def z394 : W := mkw 0x2a41554002489482 0x90b070c547034a44 0x0701fff003fc0e02 0x9030f1870703ce00

def z395 : W := mkw 0x3b497d55236ed6ab 0xf2bcf9e7e7c3df5d 0x3fe1fff0e3fcffce 0xf2bef1c7c7e3cfcc

def z396 : W := mkw 0x1908240421461228 0x0004880620419805 0x3f1d000f03fff03f 0xffc0c8272003f03f

def z397 : W := mkw 0x2241f3de93b88482 0xb6b7fec1c76ef348 0x00e1ffffffff01c3 0x9c3ffe40c7fff1c0

def z398 : W := mkw 0x0000a28e91900002 0x0437de00006cb000 0x0000000ffc030003 0x8c3ffe0000fc3000

def z399 : W := mkw 0x99083c656946fb29 0x490c89fe20d19ef5 0xff1dfc0fe3ffffff 0xffeec9ff24e3ffff

def z400 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xffff000f03e3f03f 0xfffffffff802303f

def z401 : W := mkw 0x0000080100004001 0x4008012000800410 0x0000fc00e0000e00 0x002e018004e00e00

def z402 : W := mkw 0x2000000000000003 0x403b51e940000000 0xffe0000000000003 0xe03ff1ffc0000000

def z403 : W := mkw 0x1908240421461228 0x0004880620419805 0x3f1dfc0003fffe0e 0xf6e0c9872403fe0f

def z404 : W := mkw 0x1b497d55236ed6a9 0xf28ca926a7c3df5d 0x3f1dffffe3ffffff 0xffeec9a727e3ffff

def z405 : W := mkw 0x54b400a204812055 0x480f8f3a381820a2 0xc01e000f1c030031 0x0d4f0e38381c3033

def z406 : W := mkw 0xf4b59afb4ca1e957 0xfb3ffffbffbe27fa 0xffffffffffe3ffff 0xfffffffffffe3fff

def z407 : W := mkw 0x0000000000000000 0x0000000000000000 0xc01e000000000001 0x00010e3838000000

def z408 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001000f03e30003 0x9c00080000023000

def z409 : W := mkw 0x1108aa8fb1964229 0x440f8f2220ecb411 0x001c000ffc030031 0x0d4f0e2020fc3033

def z410 : W := mkw 0x4024003004212054 0x2a000010901001aa 0x000000000000f1fc 0x03c00000000001ff

def z411 : W := mkw 0x3490000000000000 0x0004da0368000000 0xfffe000000000003 0xe011fe7ff8000000

def z412 : W := mkw 0x402541b206a12056 0xba307410971a61aa 0xf8ffffff1ffff1ff 0xfff1fe78ff1ff1ff

def z413 : W := mkw 0x8001d3eada90a902 0x9d3376d8073e62e0 0xc00003f01c0001c0 0x00113658031c01c0

def z414 : W := mkw 0x0800040000401000 0x0000000400010804 0x3f0000000000fe0c 0x6280018700000e0c

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0x001c000f00030031 0x0d40082020003033

def z416 : W := mkw 0x0000200401000002 0x0037da0000409000 0x0001fc0fe3ff0003 0x9c3ffe0004e3f000

def z417 : W := mkw 0x80019a494800c903 0x413b01e805a40650 0x0001fc0fe000fe33 0x5b2e01a004e00e30

def z418 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3fe003f003fc01cc 0xa090f047c303c1cc

def z419 : W := mkw 0x8001dbebda90e903 0xdd3b77f807be66f0 0xc001fffffc00fff3 0x5b3f37f807fc0ff0

def z420 : W := mkw 0x4024008204810054 0x0000040010082002 0x001e000000030000 0x04400e0038003003

def z421 : W := mkw 0xaa41ffffdbf8fd83 0xffbffffdc7fffffc 0xffe1ffffffffffff 0xffbfffffc7fffffc

def z422 : W := mkw 0x6a6445b206e934d4 0xba807415d21b69ae 0xffff03ff1ffff1ff 0xffd1fe7ffb1ff1ff

def z423 : W := mkw 0x3490000000000002 0x0034dac368000000 0x3ffe000000000002 0xe030ffc7f8000000

def z424 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xf8e303f01fe0f1ce 0xf2913658db1e01cc

def z425 : W := mkw 0x6a6414700469b4d4 0x2a8000d5d0110bee 0xfffe00000000fffc 0x63c001fff8000fff

def z426 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3f01fc00e3fcfe0e 0xf2aec18704e3ce0c

def z427 : W := mkw 0x402420b605a12054 0xba04ac10925ab1aa 0xf8fffffffffff1ff 0xfffffe78fffff1ff

def z428 : W := mkw 0x2490000000000000 0x000000c948000000 0xc0e2000000000000 0x00000058d8000000

def z429 : W := mkw 0x800010604800a900 0x090000d8001002e0 0xc0000000000001c0 0x00000058000001c0

def z430 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x000003fffc030001 0x0c1f3e0003fc3000

def z431 : W := mkw 0x3ed0451002681480 0xb284fa07ea03490c 0x3ffe000003fc000c 0xa080fe07f803c00c

def z432 : W := mkw 0x2a41555002689483 0xf2bb71edc7034b4c 0xffe1fff003fcffcf 0xf2bff1ffc703cfcc

def z433 : W := mkw 0x402408b304a16055 0xfa082530929a25ba 0xf8ffffffffe3ffff 0xffff3ff8fffe3fff

def z434 : W := mkw 0x1491e38e93900003 0xd43fff2a2f6ef000 0xc01fffffffff0003 0x9c3ffe383ffff000

def z435 : W := mkw 0x2a41755403689482 0xb2b4f8c5c743db4c 0x3fe1ffffe3ffffcf 0xfebef9c7c7e3ffcc

def z436 : W := mkw 0x80019a494800c900 0x0100000005a40650 0x0000fc00e0000e00 0x0000000004e00e00

def z437 : W := mkw 0x0000000000000001 0x400801e800000000 0xc000000000000000 0x400001f800000000

def z438 : W := mkw 0x0000200401000000 0x0004880000409000 0x381dfc0fe3fff03f 0xffeec82024e3f03f

def z439 : W := mkw 0x0000000000000003 0x403b01e800000000 0x0000000000000000 0x002e018000000000

def z440 : W := mkw 0x3490200401000003 0x403fdbeb68409000 0xfffffc0fe3ff0003 0xfc3ffffffce3f000

def z441 : W := mkw 0x4024a2ae95912054 0x0c078e10107cb0a2 0xc01e000ffc030031 0x0d4f0e3838fc3033

def z442 : W := mkw 0xb49192684800a903 0x493fdbfb6d3402e0 0xfffe03f01c0001c3 0xe03ffffffb1c01c0

def z443 : W := mkw 0x492c2cb725e7727c 0xba00241492dbbdbf 0x0001fffffffffffc 0x1fc0000007ffffff

def z444 : W := mkw 0x0001820800000003 0x403b01e805240000 0xc001fffffc000003 0x583f01f807fc0000

def z445 : W := mkw 0xb49018614800e903 0x493fdbfb689006f0 0xfffe00000000fff3 0xe33ffffff8000ff0

def z446 : W := mkw 0x0001104000008003 0x403b01e805000240 0xc001fff00000ffc3 0x523f01f807000fc0

def z447 : W := mkw 0x2001104000008002 0x003050c145000240 0x3fe1fff00000ffc2 0xf230f1c7c7000fc0

def z448 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xc700000000000003 0x403fc1ff00000000

def z449 : W := mkw 0x0000082100006001 0x48080130009004b0 0xc001fffffc00fff3 0x5b3f01f807fc0ff0

def z450 : W := mkw 0x0001e30c93100000 0x040000000564d000 0x0000fc00e01c0000 0x0000000004e1c000

def z451 : W := mkw 0x9109ba6d6906eb2b 0x493f89fa25f496f1 0xc01dfffffc03fff3 0x5f7f09f827fc3ff3

def z452 : W := mkw 0x3490000000000000 0x0004da0368000000 0x0700000000000000 0x0000c00700000000

def z453 : W := mkw 0x3ed1555002689482 0xb2b4fac7ef034b4c 0x3ffffff003fcffce 0xf2b0ffc7ff03cfcc

def z454 : W := mkw 0x402461b697b12054 0xbe04fe10925af1aa 0xf8ff03ff1ffff1ff 0xffd1fe78fb1ff1ff

def z455 : W := mkw 0x0000080100004000 0x0000000000800410 0x0001fc0fe000fe30 0x1b00000004e00e30

def z456 : W := mkw 0x2490000000000000 0x0000520148000000 0x00e2000000000000 0x00003600d8000000

def z457 : W := mkw 0x3c90040000401003 0x403fdbef68010804 0xfffffc0003fcfe0f 0xf2bffffffc03ce0c

def z458 : W := mkw 0x3d982c052146522b 0x403fdbef68c19c15 0x0700fc00e01c0e00 0x002ec18704e1ce00

def z459 : W := mkw 0x2000000000000002 0x003050c140000000 0x0700000000000000 0x0020c18700000000

def z460 : W := mkw 0x3490008200800003 0xd03fffeb6a0a2000 0xffff03ff1fe30003 0xfc3ffffffb1e3000

def z461 : W := mkw 0x3b486514236e16a8 0xb284f807e243d90d 0x3ffc000003ff000c 0xa4c0f807e003f00f

def z462 : W := mkw 0x1109eb8fb396422b 0xd43fff2227eef411 0x001dffffffff0033 0x9d7ffe2027fff033

def z463 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0xfffffff003fcffcf 0xf2b1ffffff03cfcc

def z464 : W := mkw 0x1108280521064229 0x400c892220c09411 0x001dfc0fe3ff0033 0x9d6ec82024e3f033

def z465 : W := mkw 0x0801450002401002 0x9030700407034804 0x3f01fff003fcfe0e 0xf2b0f1870703ce0c

def z466 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xfffe000000000000 0x602ec1fff8000000

def z467 : W := mkw 0x800192684800a903 0x493b01f8053402e0 0xc00003f01c0001c3 0x403f01f8031c01c0

def z468 : W := mkw 0x3b495d51226ed6ab 0xf2b871e7e7834f5d 0x3ffdfff003fcfffe 0xf3f0f1e7e703cfff

def z469 : W := mkw 0x7dbc2cb725e7727f 0xfa3ffffffadbbdbf 0xffffffffffffffff 0xffffffffffffffff

def z470 : W := mkw 0x8909be6d6946fb2b 0x493b01fc05f59ef5 0xc001ffffffffffff 0x5fff01f807ffffff

def z471 : W := mkw 0x1000000000000001 0x400c892220000000 0xfffe000000000003 0xe03ffffff8000000

def z472 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x0701fff003fcffcc 0x12a0c1870703cfcc

def z473 : W := mkw 0x9909be6d6946fb29 0x490c893625f59ef5 0x3f1dffffffffffff 0xffeec9a727ffffff

def z474 : W := mkw 0x0000a28e91900000 0x04000400006cb000 0x0000000ffc030000 0x0c00000000fc3000

def z475 : W := mkw 0x800018614800e903 0x493b01f8009006f0 0xc00000000000fff3 0x433f01f800000ff0

def z476 : W := mkw 0x0000000000000000 0x0000000000000000 0x3f00000000000002 0xe020c18700000000

def z477 : W := mkw 0x0800040000401000 0x0000000400010804 0x0001fc0003fcfe0c 0x128000000403ce0c

def z478 : W := mkw 0x0000000000000003 0x403b01e800000000 0xf8fe000000000003 0xe03f3ff8f8000000

def z479 : W := mkw 0xaa41df794a68fd82 0xbbb070d5c7b74ffc 0x3fe1fffffffcfffe 0xfbb0f1c7c7ffcffc

def z480 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xf8fe000003e3f1fc 0xe7c03e78f80231ff

def z481 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xc0fe03ff1c0301f1 0x0d513e78fb1c31f3

def z482 : W := mkw 0x6a6555f206e9b4d6 0xbab074d5d71b6bee 0xffe3fff01ffcffce 0xf2b1f7dfdf1fcfcc

def z483 : W := mkw 0x592defbfb7f7727f 0xfe3fff36b7fffdbf 0xffffffffffffffff 0xffffffffffffffff

def z484 : W := mkw 0x80018a2948006903 0x493b013805b404b0 0xc001fffffc000033 0x193f003807fc0030

def z485 : W := mkw 0x0000002000002000 0x08000010001000a0 0x000103ff1c00f1f0 0x1b000000031c01f0

def z486 : W := mkw 0x4024009204a10054 0xb2002400920a210a 0x00e2000000000000 0x00003600d8000000

def z487 : W := mkw 0x3b497d45234ed6ab 0x40bcd9e765c1de55 0x3f1dfc0fe3fffe3f 0xffeec9a724e3fe3f

def z488 : W := mkw 0x0000200401000000 0x0000000000409000 0x0001fc0fe3ff0000 0x1c00000004e3f000

def z489 : W := mkw 0x0000a20c91100000 0x04078a0000649000 0x00000000e0000000 0x000e000000e00000

def z490 : W := mkw 0xb491fbefdb90e903 0xdd3ffffb6ffef6f0 0xfffffffffffffff3 0xff3ffffffffffff0

def z491 : W := mkw 0x0001104000008002 0x003000c005000240 0x0000fc0000000e00 0x0020018004000e00

def z492 : W := mkw 0x6a6555f206e9b4d6 0xbab074d5d71b6bee 0x3fe1ffff1ffffffe 0xfff0f1c7c71fffff

def z493 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0000fc00e3ff0000 0x842efe0004e3f000

def z494 : W := mkw 0xbb49ff7d6b6effab 0xfbbff9ffe7f7dffd 0xfffdffffffffffff 0xfffff9ffe7ffffff

def z495 : W := mkw 0x1909ef8fb3d65229 0xd40cad2627effc15 0x3f1dfffffffffe3f 0xffeec9a727fffe3f

def z496 : W := mkw 0x4024003004212054 0x2a000010901001aa 0xc0e20000000001c0 0x00000058d80001c0

def z497 : W := mkw 0x74b400a204812057 0x483fdffb781820a2 0xfffe000f1c030033 0xed7ffffff81c3033

def z498 : W := mkw 0x800018614800e901 0x490801f8009006f0 0xc001fc0fe000fff3 0x5b2e01f804e00ff0

def z499 : W := mkw 0x0001610403000002 0x9034f8000742d000 0x0001ffffe3ff0003 0x9c3ef80007e3f000

def z500 : W := mkw 0x2a40451002681482 0xb2b070c5c203490c 0x3fe0000003fc000e 0xe0b0f1c7c003c00c

def z501 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0001ffffffff0000 0x1c2ec00007fff000

def z502 : W := mkw 0x4025c3ba96b12056 0xbe337610973e61aa 0xc0e203f01c0001c0 0x00113658db1c01c0

def z503 : W := mkw 0x0241515002288480 0xb280200087024348 0x000003f0000001c0 0x00000000030001c0

def z504 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0x38ff03ff1fe3f1fc 0xbfc03e00fb1e31ff

def z505 : W := mkw 0x402400a204812054 0x08000410101820a2 0xf81f000f1fe3f03f 0xffc10e38381e303f

def z506 : W := mkw 0x0000003000202000 0xba002010821201a8 0xf8e103ff1fe0f1ff 0xfb913078c31e01fc

def z507 : W := mkw 0x0001e38e93900003 0xd43fffe8076ef000 0xc001ffffffff0003 0xdc3ffff807fff000

def z508 : W := mkw 0x90019a694800e903 0x493f89fa25b406f0 0xff1dfffffc00fff3 0xfb3fc9ff27fc0ff0

def z509 : W := mkw 0x592c2ca725c7727d 0x480c8d3630d9bcb7 0xff1ffc0ffffffe3f 0xffefcfbf3cfffe3f

def z510 : W := mkw 0x0000002000002000 0x08000010001000a0 0xf8ff03ff1c00f1f3 0xfb113e78fb1c01f0

def z511 : W := mkw 0x2a41f74c93589482 0x04b7dac54565da44 0x0700fc00e01c0e00 0x002ec18704e1ce00

def z512 : W := mkw 0x7b6d7df727eff6ff 0xfabcfdf7f7dbffff 0xffffffffffffffff 0xffffffffffffffff

def z513 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3f1cfc00e01cfe3c 0x63eec1a724e1ce3f

def z514 : W := mkw 0x1000000000000001 0x400c892220000000 0x0700000000000000 0x002ec18700000000

def z515 : W := mkw 0x0108280521064228 0x0000000000c09411 0x0000000fe0030030 0x0d40000000e03033

def z516 : W := mkw 0x0000000000000002 0x003000c000000000 0x0000000000000002 0x403001c000000000

def z517 : W := mkw 0x8001ebafdb906903 0xdd3fff3807fef4b0 0xc001ffffffff0033 0x9d3ffe3807fff030

def z518 : W := mkw 0x3490080100004003 0x403fdbeb68800410 0xfffffc0fe000fe33 0xfb3ffffffce00e30

def z519 : W := mkw 0x0000008200800000 0x0000040000082000 0x0000000f1c030001 0x0c010e00001c3000

def z520 : W := mkw 0x0a41555002689482 0xb2b0700487034b4c 0x0001fff003fcffce 0x92b0f0000703cfcc

def z521 : W := mkw 0x0000001000200000 0xb200200082020108 0x00e003f0000001c0 0x00103040c30001c0

def z522 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3f1c000fe003fe3d 0x6fce09a720e03e3f

def z523 : W := mkw 0x0a41555002689480 0xb280200487034b4c 0x38e1fff003fcffce 0xf2903040c703cfcc

def z524 : W := mkw 0x19080c0120465229 0x4008012620810c15 0x3f1dfc0003fcfe3e 0xf3e0c1a72403ce3f

def z525 : W := mkw 0x80019a694800e903 0x493fdbf805b406f0 0xc001fffffc00fff3 0xdb3ffff807fc0ff0

def z526 : W := mkw 0x402510f204a1a056 0xba3024d0971a23ea 0xf8ffffff1fe3ffff 0xfff13ff8ff1e3fff

def z527 : W := mkw 0x4024009204a10054 0xb2002400920a210a 0x38ff03ff1fe3000f 0xbcd13e00fb1e300f

def z528 : W := mkw 0x0000618693900000 0x9404fe00024af000 0x0001fc0fe3ff0003 0x9c2efe0004e3f000

def z529 : W := mkw 0x1d982c0521465229 0x400f8b2e28c19c15 0xff1ffc0fe3fffe3f 0xffefcfbf3ce3fe3f

def z530 : W := mkw 0x0001e30c93100002 0x0437da000564d000 0x0000fc00e01c0003 0x803ffe0004e1c000

def z531 : W := mkw 0x0000008200800000 0x90002400020a2000 0x0000000003e30000 0x84003e0000023000

def z532 : W := mkw 0x0a41555002689482 0xb2b020c487034b4c 0x0001fff003fcffce 0x52b001c00703cfcc

def z533 : W := mkw 0x19080c0120465229 0x4008012620810c15 0x3f1d000f03e3fe3f 0xffc009a720023e3f

def z534 : W := mkw 0x36d1515002288483 0xf2bffbebef024348 0xfffe03f0000001c3 0xe03ffffffb0001c0

def z535 : W := mkw 0x8001f3eedb90a902 0x9d37fed8077ef2e0 0xc001ffffffff01c3 0x9c3ffe5807fff1c0

def z536 : W := mkw 0x6a6414f204e9b4d4 0xba8024d5d21b2bee 0xffff03ff1fe3ffff 0xffd13ffffb1e3fff

def z537 : W := mkw 0x000118410000c003 0x403801e005800650 0x0001ffffe000fff3 0x5b3e01e007e00ff0

def z538 : W := mkw 0x8a41df794a68fd83 0xfbbb21fc87b74ffc 0xc001fffffffcffff 0x5bbf01f807ffcffc

def z539 : W := mkw 0x626551f206a9a4d6 0xbab074d1d71a63ea 0xc0e203f01c0001c0 0x00113658db1c01c0

def z540 : W := mkw 0x0490000000000000 0x0003020808000000 0xc002000000000000 0x0001061818000000

def z541 : W := mkw 0x3491c38a92900003 0xd43fffeb6f2e6000 0xfffe03f01c000003 0xe03ffffffb1c0000

def z542 : W := mkw 0x19082c0521465228 0x0004880620c19c15 0x3f1dfc0fe3fffe3c 0xbfc0c80724e3fe3f

def z543 : W := mkw 0x3490000000000003 0x403b01eb68000000 0xfffe000000000003 0x603f01fff8000000

def z544 : W := mkw 0x2240411002280480 0xb2807001c2024108 0x00e0000000000000 0x00003000c0000000

def z545 : W := mkw 0x0000000000000001 0x400b012800000000 0xc000000000000001 0x000f003800000000

def z546 : W := mkw 0x0001828a00800002 0x90332400072e2000 0x0001ffffffe30003 0x9c3f3e0007fe3000

def z547 : W := mkw 0x0000001000200000 0x2200000080000108 0x38e000000000f1cc 0x62800040c00001cc

def z548 : W := mkw 0x0800040000401000 0x0000000400010804 0x0700fc00001c0e00 0x0020c1870401ce00

def z549 : W := mkw 0x492c2cb725e7727c 0xba00241492dbbdbf 0xf8ffffffffffffff 0xffd13e78ffffffff

def z550 : W := mkw 0x592c2c9725e7527d 0xf20cad26b2cbbd1f 0x3ffffc0fe3fffe3f 0xffeeffa7fce3fe3f

def z551 : W := mkw 0x4025e3be97b12056 0xbe37fe10977ef1aa 0xc0e3ffffffff01c3 0x9c3ffe58dffff1c0

def z552 : W := mkw 0x80008a2948006901 0x490b013800b404b0 0xc00103fffc00f1f3 0x5b1f007803fc01f0

def z553 : W := mkw 0x800192684800a902 0x093300d8053402e0 0xc001fffffc0001c3 0x183f005807fc01c0

def z554 : W := mkw 0x1108280521064229 0x400c892220c09411 0x3f1c000fe0030033 0xed6ec9a720e03033

def z555 : W := mkw 0xaa41df494a48dd83 0x41bb51ed45a54e54 0x0700fc00e01c0e00 0x002ec18704e1ce00

def z556 : W := mkw 0x8001fb6ddb10e903 0x4d3fdbf805f4d6f0 0xc001fffffc1cfff3 0x5b3fc1f807fdcff0

def z557 : W := mkw 0x3000000000000003 0x403cd9e360000000 0x3ffc000000000003 0xe03ef9e7e0000000

def z558 : W := mkw 0x0000080100004001 0x4008012000800410 0x000000000000fe30 0x430001a000000e30

def z559 : W := mkw 0x2a415d510268d483 0xf2b871e5c7834f5c 0x3fe1ffffe3fcffff 0xfbbef1e7c7e3cffc

def z560 : W := mkw 0x1909ef0db356522b 0x443fdb2625e5dc15 0x3f1dfc0fe3fffe3f 0xffeec9a724e3fe3f

def z561 : W := mkw 0x0001104000008002 0x003000c005000240 0x000003f0000001c0 0x00100040030001c0

def z562 : W := mkw 0x2241515002288482 0xb2b070c1c7024348 0x38e103f003e0f1ce 0xf2903040c30201cc

def z563 : W := mkw 0x1490000000000000 0x00048a0228000000 0x001e000000000000 0x00000e0038000000

def z564 : W := mkw 0x3b486d15236e56a9 0xf28cf927e2c3dd1d 0x3ffdfc0fe3fffe3f 0xffeef9a7e4e3fe3f

def z565 : W := mkw 0xa49192684800a902 0x093352d94d3402e0 0xc0e203f01c0001c0 0x00113658db1c01c0

def z566 : W := mkw 0xc0259afb4ca1e954 0xbb00241097be27fa 0xf8ffffffffe3ffff 0xffd13e78fffe3fff

def z567 : W := mkw 0x0908240421461228 0x0000000400419805 0x0000000003ff000c 0x04c000000003f00f

def z568 : W := mkw 0x2000000000000000 0x0000500140000000 0x3fe0000000000000 0xa000f007c0000000

def z569 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0x38e103ff1fe3f1fe 0xffd03040c31e31ff

def z570 : W := mkw 0xc0259afb4ca1e957 0xfb3b25f897be27fa 0xc001ffffffe3ffff 0x5fff01f807fe3fff

def z571 : W := mkw 0x4024619697b10054 0xb604fe00924af10a 0x38fe000003ff000c 0xa4c0fe00f803f00f

def z572 : W := mkw 0x9909ffeffbd6fb2b 0xdd3ffffe27fffef5 0xff1dffffffffffff 0xffffffff27ffffff

def z573 : W := mkw 0x1000000000000001 0x4008012220000000 0x3f1c000000000000 0x600001a720000000

def z574 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x0701fc0fe3ff0e03 0x9c2ec98704e3fe00

def z575 : W := mkw 0x94908a2948006901 0x490f8b3a28b404b0 0xc01e000ffc000031 0x090f0e3838fc0030

def z576 : W := mkw 0x0000618693900000 0x9404fe00024af000 0x000103ff1fff0003 0x9c11fe00031ff000

def z577 : W := mkw 0x19086d87b3d65229 0xd40cff2622cbfc15 0x3f1dfc0fe3fffe3f 0xffeeffa724e3fe3f

def z578 : W := mkw 0x2a41555002689480 0xb2807005c7034b4c 0x3fe1fff003fcffcc 0xb280f007c703cfcc

def z579 : W := mkw 0x592c2c352567727d 0x6a0c8936b0d19dbf 0xfffffc0fe3ffffff 0xffeec9fffce3ffff

def z580 : W := mkw 0x2241515002288482 0xb2b070c1c7024348 0x00e1fff00000ffc2 0x523031c0c7000fc0

def z581 : W := mkw 0x3490000000000001 0x400cdb2368000000 0x3ffe000000000003 0xe02effa7f8000000

def z582 : W := mkw 0x0000610493100000 0x0404da000040d000 0x00000000001c0000 0x0000c0000001c000

def z583 : W := mkw 0x1490000000000001 0x400f8b2a28000000 0xff1e000000000003 0xe02fcfbf38000000

def z584 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x001dfc0fe3fffe3d 0x1fce082024e3fe3f

def z585 : W := mkw 0x74b4009204a10057 0xf23fffebfa0a210a 0xfffe000003e3000f 0xe4fffffff802300f

def z586 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000003 0x80113e0000000000

def z587 : W := mkw 0x3490618693900003 0xd43fffeb6a4af000 0xfffe000003ff0003 0xe43ffffff803f000

def z588 : W := mkw 0x2241514002088482 0x00b050c145004240 0x0000000000000000 0x0000000000000000

def z589 : W := mkw 0x1909ef8fb3d6522b 0xd43fff2627effc15 0x0701ffffffff0e03 0x9c3fff8707fffe00

def z590 : W := mkw 0x0a41554002489480 0x0080000405014a44 0x0000fc00001c0e00 0x000000000401ce00

def z591 : W := mkw 0x1909e78eb3d6122a 0x9437fe06276ff805 0x3f1dffffffff000f 0xbcfffe0727fff00f

def z592 : W := mkw 0x0000000000000000 0x0004880000000000 0x0000000000000003 0x802ec80000000000

def z593 : W := mkw 0x3490618693900000 0x9404fe036a4af000 0x3ffe000003ff0000 0xa400fe07f803f000

def z594 : W := mkw 0x402400a204812054 0x08000410101820a2 0xf8fe000f1c030033 0xed513e78f81c3033

def z595 : W := mkw 0x0001e38e93900002 0x94307400076ef000 0x0001ffffffff0002 0x9c30f00007fff000

def z596 : W := mkw 0x8909be6d6946fb28 0x0900001405f59ef5 0x0001fffffffffffc 0x1fc0000007ffffff

def z597 : W := mkw 0x3ed0145000689481 0x628801efe8010b4c 0xfffe00000000ffcc 0x628001fff8000fcc

def z598 : W := mkw 0x2a4155d202e89482 0xb2b074c5c70b6b4c 0x3fe1ffff1fffffcf 0xfeb1ffc7c71fffcc

def z599 : W := mkw 0xaa415d714a68fd83 0xfbb871fdc7934ffc 0xffe1fff003fcfffe 0xf3b0f1ffc703cffc

def z600 : W := mkw 0x4025c3ba96b12056 0xbe337610973e61aa 0xf8ff03ff1fe3f1ff 0xffd13e78fb1e31ff

def z601 : W := mkw 0x0a41f7de93f89480 0xb6802404876ffb4c 0x0001ffffffffffcc 0x1e80000007ffffcc

def z602 : W := mkw 0x3b481c51206ed6a9 0x628801e7e0810f5d 0x3ffc00000000fffc 0x63c001e7e0000fff

def z603 : W := mkw 0x2490000000000002 0x003352c948000000 0xf8fe000000000003 0xe0113e78f8000000

def z604 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xc00103ff1fe3f1ff 0x5fd10078031e31ff

def z605 : W := mkw 0x1908240421461229 0x400c892620419805 0x3f1c000003ff000f 0xe4eec9a72003f00f

def z606 : W := mkw 0x3b497d45234ed6ab 0x40bcd9e765c1de55 0x0700fc00e01c0e00 0x002ec18704e1ce00

def z607 : W := mkw 0x2000000000000002 0x003050c140000000 0x00e0000000000000 0x00103040c0000000

def z608 : W := mkw 0x0001e30c93100002 0x9437fa000766d000 0x0001fff0e3fc0002 0x903ef00007e3c000

def z609 : W := mkw 0x8001fbcfdb90c903 0xd53fffe807eef650 0x0001ffffffff0e03 0x9c3fff8007fffe00

def z610 : W := mkw 0x8001ba6d4900e903 0x493f89f805f496f0 0xc001fffffffffff3 0xdf3fc9f807fffff0

def z611 : W := mkw 0x0000080100004003 0x403b01e800800410 0xc001fc0fe000fe33 0x5b3f01f804e00e30

def z612 : W := mkw 0x9908ae2d69467b29 0x490f893e20f59cb5 0xff1dfc0ffffffe3f 0xffefc9bf24fffe3f

def z613 : W := mkw 0xb49018614800e901 0x490801fb689006f0 0xfffe00000000fff0 0x630001fff8000ff0

def z614 : W := mkw 0x3ed1555002689483 0xf2b871efef034b4c 0xfffffff003fcffce 0xf2b0f1ffff03cfcc

def z615 : W := mkw 0x0001c38a92900002 0x94337600072e6000 0x000103ff1fe30003 0x9c113e00031e3000

def z616 : W := mkw 0x8001fbefdb90e902 0x9d37fe1007fef6f0 0x0001fffffffffff3 0x9f3ffe0007fffff0

def z617 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xc0fe000000000001 0x001f3e78f8000000

def z618 : W := mkw 0x800192684800a902 0x093300d8053402e0 0xc001fff01c00ffc2 0x523101d8071c0fc0

def z619 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x00e1fff003fcffcc 0x12903040c703cfcc

def z620 : W := mkw 0x0001c30892100002 0x0433520005244000 0x0000000000000000 0x0000000000000000

def z621 : W := mkw 0x80019aeb4880e903 0xd93b25f807be26f0 0xc001ffffffe3fff3 0xdf3f3ff807fe3ff0

def z622 : W := mkw 0x8000822848002900 0x09030018003400a0 0xc00000001c000000 0x00010018001c0000

def z623 : W := mkw 0x0a40145000689480 0x2280000480010b4c 0x000000000000ffcc 0x0280000000000fcc

def z624 : W := mkw 0x2241515002288482 0xb2b070c1c7024348 0x00e1fff003fc01c2 0x9030f040c703c1c0

def z625 : W := mkw 0x2241d3da92b88482 0xb6b376c1c72e6348 0x00e003f01c0001c0 0x00113640c31c01c0

def z626 : W := mkw 0x74b400b204a12055 0xfa0825fbfa1a21aa 0xffff03ff1fe3f1ff 0xffd13ffffb1e31ff

def z627 : W := mkw 0x800018414800c901 0x410801e800800650 0x0000000000000e00 0x0000018000000e00

def z628 : W := mkw 0x2a4175d693f89482 0xb6b4fec5c74bfb4c 0x3fe1fff003ffffce 0xf6b0ffc7c703ffcc

def z629 : W := mkw 0x402400a204812054 0x08000410101820a2 0x0000000f1c030030 0x0d400000001c3033

def z630 : W := mkw 0xaa41df694a48fd83 0x49bb51fd45b54ef4 0xc701fffffc1cfff3 0x5b3fc1ff07fdcff0

def z631 : W := mkw 0x1909ae0d2146522b 0x403f892625e59c15 0x3f1dfffffffffe3f 0xffffc9a727fffe3f

def z632 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000000000003 0x4011007800000000

def z633 : W := mkw 0x0000002000002003 0x483b01f8001000a0 0xc00103ff1c00f1f3 0x5b3f01f8031c01f0

def z634 : W := mkw 0x0000000000000002 0x0033000000000000 0x0000000000000003 0x003f000000000000

def z635 : W := mkw 0x402400a204812054 0x08000410101820a2 0xc00200001c000000 0x00010618181c0000

def z636 : W := mkw 0x0000000000000002 0x003300c800000000 0xc000000000000000 0x0011005800000000

def z637 : W := mkw 0x2000000000000002 0x0037dac140000000 0x3fe0000000000003 0xe03fffc7c0000000

def z638 : W := mkw 0x626551f206a9a4d6 0xbab074d1d71a63ea 0xf8ff03ff1fe3f1ff 0xffd13e78fb1e31ff

def z639 : W := mkw 0x3b497554236e96aa 0xb2b4f8c7e743db4d 0x3ffdfff003ffffce 0xf6f0f9c7e703ffcf

def z640 : W := mkw 0x0800040000401000 0x0000000400010804 0x3f00000003fc000c 0xa080c0070003c00c

def z641 : W := mkw 0x800192684800a900 0x09000010053402e0 0x000003f01c0001c0 0x00000000031c01c0

def z642 : W := mkw 0x8001db694a00e903 0xd93b71f807b646f0 0xc001fffffffcfff3 0xdb3ff1f807ffcff0

def z643 : W := mkw 0x2a41555002689482 0xb2b7fac5c7034b4c 0x3fe1fff003fcffcf 0xf2bfffc7c703cfcc

def z644 : W := mkw 0x74b400b204a12054 0xba04fe13fa1a21aa 0xffff03ff1fe3f1ff 0xffd1fe7ffb1e31ff

def z645 : W := mkw 0x800018614800e900 0x09000010009006f0 0x000000000000fff0 0x0300000000000ff0

def z646 : W := mkw 0x19082c8721c65229 0xd00cad2622cbbc15 0x3f1dfffffffffe3f 0xffffffa727fffe3f

def z647 : W := mkw 0x0801e78e93d01002 0x9437fe04076ff804 0x3f01fffffffffe0f 0xfebfff8707fffe0c

def z648 : W := mkw 0x0000080100004001 0x4008012000800410 0x0000000fe0000031 0x090e002000e00030

def z649 : W := mkw 0x64b400b204a12056 0xba3376d9da1a21aa 0xc0e203f01c0001c0 0x00113658db1c01c0

def z650 : W := mkw 0x0800240401401000 0x0004880400419804 0x3f01fc0fe3fffe0f 0xfeaec98704e3fe0c

def z651 : W := mkw 0x3d980c0120465229 0x400801ef68810c15 0xfffe00000000fe3c 0x63c001fff8000e3f

def z652 : W := mkw 0x1000000000000003 0x403f89ea20000000 0xff1c000000000003 0xe03fc9ff20000000

def z653 : W := mkw 0x0001e38e93900000 0x9404fe00076ef000 0x0001ffffffff0000 0x9c00fe0007fff000

def z654 : W := mkw 0x8001fbefdb90e903 0xdd3b25f807fef6f0 0xc001fffffffffff3 0x5f3f01f807fffff0

def z655 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xf8fe03f01fe301cc 0xa4d13e58fb1e31cf

def z656 : W := mkw 0x2a41554002489482 0x00b050c545014a44 0x3fe0fc00001c0e02 0xe030f1c7c401ce00

def z657 : W := mkw 0x4024009204a10054 0xb2002400920a210a 0xf8fe000003e3000f 0xe4d13e78f802300f

def z658 : W := mkw 0x1598280521064229 0x400f8b2a28c09411 0xc01e000fe0030031 0x0d4f0e3838e03033

def z659 : W := mkw 0x80019a794820e903 0xfb3b21f887b607f8 0xf8e1ffffffe0ffff 0xfbbf31f8c7fe0ffc

def z660 : W := mkw 0x3491e38e93900003 0xd43fffeb6f6ef000 0x0701ffffffff0003 0x9c3fff8707fff000

def z661 : W := mkw 0x0000000000000000 0x9000200002020000 0x000103f003e00002 0x9010300003020000

def z662 : W := mkw 0x0000104000008000 0x000000c000000240 0x000000000000ffc0 0x420001c000000fc0

def z663 : W := mkw 0x2a41f7ce93d89482 0x94b7fec5476ffa44 0x0701ffffffff0e03 0x9c3fff8707fffe00

def z664 : W := mkw 0x9909be4d6946db2b 0x413f89ee25e59e55 0x0700fc00e01c0e00 0x002ec18704e1ce00

def z665 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x071cfc0fe01f0e31 0x0d6ec9a724e1fe33

def z666 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0e2000000000000 0x00113658d8000000

def z667 : W := mkw 0xc02592fa4ca1a956 0xbb3324d8973e23ea 0xf8ff03ff1fe3f1ff 0xffd13e78fb1e31ff

def z668 : W := mkw 0x0000200401000000 0x0004880000409000 0x0000fc00e01c0000 0x002ec00004e1c000

def z669 : W := mkw 0x1908040020461228 0x0000000620010805 0x3f1c00000000000c 0x20c000072000000f

def z670 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xf8fe03f01c00f1fc 0x63d13678fb1c01ff

def z671 : W := mkw 0x2a41145000689482 0x22b000c5c5010b4c 0x3fe1fff00000ffce 0x72b001c7c7000fcc

def z672 : W := mkw 0x1000000000000003 0x403fdb2220000000 0x3f1c000000000003 0xe03fffa720000000

def z673 : W := mkw 0x0001411002200002 0xb230700087024108 0x38e1fff003fcf1ce 0xf2b0f040c703c1cc

def z674 : W := mkw 0x1108200421060228 0x0004880220409001 0x001c000000030000 0x0440080020003003

def z675 : W := mkw 0x19080c0120465229 0x400c892620810c15 0x3f1c00000000fe3f 0xe3eec9a720000e3f

def z676 : W := mkw 0x000110600000a002 0x083000d0051002e0 0xc001ffff1c00fff3 0x5b3101f8071c0ff0

def z677 : W := mkw 0x0000008200800000 0x90002400020a2000 0x381d03ff1fe3f03f 0xffd13e20231e303f

def z678 : W := mkw 0x0000000000000000 0x0000000000000000 0x3801000003e0f00e 0xf28000000002000c

def z679 : W := mkw 0x6a64459206e914d4 0xb2807405d20b690e 0x3ffe000003ff000c 0xa4c0fe07f803f00f

def z680 : W := mkw 0x19082c052146522b 0x403f89ee20c19c15 0xff1dfc0fe3fffe3f 0xffffc9ff24e3fe3f

def z681 : W := mkw 0x0000000000000000 0x00078a0000000000 0x0000000000000001 0x000f0e0000000000

def z682 : W := mkw 0x80008a2948006901 0x490b013800b404b0 0xc001fc0ffc00fe33 0x5b2f01b804fc0e30

def z683 : W := mkw 0x0001e38e93900002 0x94337600076ef000 0x0001ffffffff0000 0x1c11360007fff000

def z684 : W := mkw 0x4024009204a10054 0xb2002400920a210a 0x0000000003e3000c 0x04c000000002300f

def z685 : W := mkw 0x19082c2521467229 0x480c893620d19cb5 0xff1dffffffffffff 0xffffc9ff27ffffff

def z686 : W := mkw 0x0000000000000000 0x0000000000000000 0x381c00000000f03c 0x63c000202000003f

def z687 : W := mkw 0xc025fbffdfb1e957 0xff3ffff897fef7fa 0xf8ffffffffffffff 0xfffffff8ffffffff

def z688 : W := mkw 0x74b4003004212057 0x6a3fdbfbf81001aa 0xfffe00000000f1ff 0xe3fffffff80001ff

def z689 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0x381d03ff1fe3f1ff 0xffc00820231e31ff

def z690 : W := mkw 0x4a6555f206e9b4d4 0xba802414971b6bee 0xf8ffffff1fffffff 0xffd13e78ff1fffff

def z691 : W := mkw 0x0a41f7de93f89482 0xb6b7fe04876ffb4c 0x0001ffffffffffcf 0x9ebffe0007ffffcc

def z692 : W := mkw 0x4025e3be97b12056 0xbe37fe10977ef1aa 0x0001fffffffff1ff 0x9ffffe0007fff1ff

def z693 : W := mkw 0x09082c0521465229 0x4008012400c19c15 0x0001fc0fe3fffe3f 0x5fee01a004e3fe3f

def z694 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001fc0003fc0002 0x9020c0000403c000

def z695 : W := mkw 0x2240105000288480 0x228000c1c0000348 0x00e00000000001c0 0x00000040c00001c0

def z696 : W := mkw 0x3490000000000000 0x0000000368000000 0x3ffe000000000000 0x20000007f8000000

def z697 : W := mkw 0x0001820800000002 0x0033000005240000 0x0000fc00e0000000 0x002e000004e00000

def z698 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc00003fffc0001f1 0x091f007803fc01f0

def z699 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0x000103ff1fe3f1ff 0x9fd13e00031e31ff

def z700 : W := mkw 0x2a41451002681482 0xb2b07005c703490c 0x3fe1fff003fc000e 0xb0b0f007c703c00c

def z701 : W := mkw 0xc02592fa4ca1a956 0xbb3324d8973e23ea 0xc0e203f01c0001c0 0x00113658db1c01c0

def z702 : W := mkw 0x0001c38a92900000 0x94002400072e6000 0x000003f01c000000 0x00000000031c0000

def z703 : W := mkw 0x19082c052146522b 0x403fdb2620c19c15 0x3f1dfc0fe3fffe3f 0xffffffa724e3fe3f

def z704 : W := mkw 0x4024003004212054 0x2a000010901001aa 0xf8ff03ff1c00f1ff 0x7bd10078fb1c01ff

def z705 : W := mkw 0x1000000000000001 0x400c892220000000 0x3f1d000f03e3f03f 0xffeec9a72002303f

def z706 : W := mkw 0x402582ba04a12056 0xba332410973e21aa 0xf8ffffffffe3f1ff 0xffff3e78fffe31ff

def z707 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xfffe000000000000 0xe011fffff8000000

def z708 : W := mkw 0x80008a2948006901 0x490b013800b404b0 0xc001fffffc00fff3 0x5b3f01f807fc0ff0

def z709 : W := mkw 0x2491e38e93900002 0x9437fec94f6ef000 0x0001ffffffff0003 0x9c3ffe0007fff000

def z710 : W := mkw 0x492c24b625e7327c 0xba002414925bb9af 0x000103ff1ffff1fc 0x1fc00000031ff1ff

def z711 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc00003fffc00fff1 0x4b1f01f803fc0ff0

def z712 : W := mkw 0x9108282569066b29 0x490c893a20d094b1 0xc01c000fe0030031 0x0d4e083820e03033

def z713 : W := mkw 0x0001e38e93900000 0x04078e00056cf000 0x0000fc0ffc1f0001 0x0c0f0e0004fdf000

def z714 : W := mkw 0xb491924848008903 0x413fdbeb6d240240 0xfffe000000000003 0xe03ffffff8000000

def z715 : W := mkw 0x2ed1555002689482 0xb2b372cdcf034b4c 0xfffffff003fcffcf 0xf2b1ffffff03cfcc

def z716 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3f1dfc0fe3fffe3c 0xbfeec98724e3fe3f

def z717 : W := mkw 0x592c2cb725e7727d 0xfa0cad36b2dbbdbf 0xc7e2fff0fc1c0fc0 0x003ff7dfdffdcfc0

def z718 : W := mkw 0x0001e39e93b00002 0xb637fe00876ef108 0xf8fffffffffff1cf 0xfebffe78fffff1cc

def z719 : W := mkw 0x4024203405212054 0x2a048810905091aa 0xf8fffc0fe3fff1ff 0xffeec878fce3f1ff

def z720 : W := mkw 0x3490000000000001 0x400cdb2b68000000 0xfffe000000000000 0xa000fe3ff8000000

def z721 : W := mkw 0xa0019a694800e903 0x493b01f945b406f0 0xffe1fffffc00fff3 0x7b3f01ffc7fc0ff0

def z722 : W := mkw 0x2490000000000002 0x0037dac948000000 0xffe2000000000003 0xe03fffdfd8000000

def z723 : W := mkw 0x0001e38e93900000 0x9404ac00076ef000 0x0001ffffffff0001 0x1c0e080007fff000

def z724 : W := mkw 0x2001e38e93900002 0x9437fec1476ef000 0x0701ffffffff0003 0x9c3fff8707fff000

def z725 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3fe1fff003fcffcc 0x72a0c1c7c703cfcc

def z726 : W := mkw 0xb4919a494800c903 0x413fdbeb6da40650 0xfffffffffc000e03 0xf83ffffffffc0e00

def z727 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0001fffffffff03f 0x9ffffe0007fff03f

def z728 : W := mkw 0x0001a20c01000000 0x0004880005649000 0x0001ffffffff0003 0x9c2ec80007fff000

def z729 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0x0001fffffc00fff3 0x1b3f018007fc0ff0

def z730 : W := mkw 0xa0019a694800e903 0x493b51f945b406f0 0xfffffffffc00fff3 0xfb3ffffffffc0ff0

def z731 : W := mkw 0x2a40555002689480 0x228050c5c0014b4c 0x3fe00000001cffcc 0x6280c1c7c001cfcc

def z732 : W := mkw 0x0001618603800002 0x9034fc00074af000 0x0001ffffffff0003 0x9c3ffe0007fff000

def z733 : W := mkw 0x2491e38e93900002 0x9437fe014f6ef000 0x00e3ffffffff0003 0x9c3ffe00dffff000

def z734 : W := mkw 0x0801145000609002 0xb23020c487030b4c 0x3fe1fff003fcffce 0xf2b0f1c7c703cfcc

def z735 : W := mkw 0x0000a20c01000000 0x0007880000649000 0x0001fc0fffff0003 0x9c2fc80004fff000

def z736 : W := mkw 0x0000208601800002 0x9037fe00024ab000 0x0001ffffffff0003 0x9c3ffe0007fff000

def z737 : W := mkw 0x0001a20c01000002 0x0033000005649000 0x0001ffffffff0003 0x1c3f000007fff000

def z738 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3ffffff003fcffce 0xf2b0ffc7ff03cfcc

def z739 : W := mkw 0x2a41555002689482 0x22b050c5c5014b4c 0x3fe1fc0003fcffce 0xf2a0c1c7c403cfcc

def z740 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xf81dfffffc00fff3 0xfb3f09f827fc0ff0

def z741 : W := mkw 0x3490000000000000 0x0004da0368000000 0xfffe000000000000 0xa011fe5ff8000000

def z742 : W := mkw 0x3491e38e93900001 0xd40825eb6f6ef000 0xffffffffffff0000 0x7c0001fffffff000

def z743 : W := mkw 0x0801554002409002 0x903070c407034a44 0x3f01fff003fcffce 0xf2b0f1c70703cfcc

def z744 : W := mkw 0x0a41555002689480 0xb280200487034b4c 0x0701fff003fcffcc 0x12a0c1870703cfcc

def z745 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xfffe000000000000 0xe02efffff8000000

def z746 : W := mkw 0x0800041000601000 0x220000048001090c 0x3fe1fc0003fcffce 0xf2a0c1c7c403cfcc

def z747 : W := mkw 0x0001a28e01800002 0x9037ac00076eb000 0x0001ffffffff0003 0x9c3ffe0007fff000

def z748 : W := mkw 0x80019a694800e903 0x493b013005b406f0 0x0001fffffc00fff3 0x5b3f01a007fc0ff0

def z749 : W := mkw 0xbed01c714868fd81 0x6b8801ffe8910ffc 0xfffe00000000fffc 0x638001fff8000ffc

def z750 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xf8fe03f01fe3f1fc 0xe7d13e78fb1e31ff

def z751 : W := mkw 0x359808012006422b 0x403fdbeb68800411 0xfffe000000000033 0xe17ffffff8000033

def z752 : W := mkw 0x3491924800008003 0x403fdbeb6d240240 0xfffffffffc00ffc3 0xfa3ffffffffc0fc0

def z753 : W := mkw 0x0801144000409002 0x003000c405010a44 0x0701fff0001cffc2 0x5230c1c70701cfc0

def z754 : W := mkw 0x0001e30c93100002 0x9437fa000766d000 0x0001fffffffc0003 0x983ff00007ffc000

def z755 : W := mkw 0x2a41554002489482 0x00b050c545014a44 0x0701fff0001cffc0 0x1220c1870701cfc0

def z756 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xffff000f03e30003 0xfc3ffffff8023000

def z757 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc001fffffc00fff0 0x5b2e01f807fc0ff0

def z758 : W := mkw 0x4b6d7df727eff6fc 0xba80241497dbffff 0x0001fffffffffffc 0x1fc0000007ffffff

def z759 : W := mkw 0x2d982c052146522a 0x003352cd48c19c15 0xc0e3fc0fe3fffe3c 0x1fd13658dce3fe3f

def z760 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0001fffffffffe03 0xde3fff8007fffe00

def z761 : W := mkw 0x4025e39e97b10056 0xb637fe00976ef10a 0x0001ffffffff000f 0x9cfffe0007fff00f

def z762 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x0701fc0fe3fffe3f 0x5feec1a704e3fe3f

def z763 : W := mkw 0x2a41555002689482 0x22b050c5c5014b4c 0x3fe1fff0001cffce 0x72b0c1c7c701cfcc

def z764 : W := mkw 0x36d1514002088483 0x40bfdbeb6d004240 0xfffe000000000003 0xe03ffffff8000000

def z765 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3fe1fff003fcffcf 0xf2b1ffc7c703cfcc

def z766 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xc7fe000000000001 0x003ffffff8000000

def z767 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3ffdfff003ffffce 0xf6f0f9c7e703ffcf

def z768 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3f1cfc0fe3ff0e3d 0xadeec9a724e3fe3f

def z769 : W := mkw 0x0000e38e93900000 0x9407fe00026ef000 0x000103ffffff0003 0x9c1ffe0003fff000

def z770 : W := mkw 0x3491e38e93900002 0x9437fe036f6ef000 0xffffffffffff0003 0xfc3ffe7ffffff000

def z771 : W := mkw 0x1909cf8bb2d6522b 0xd43b772627af6c15 0x3f1c03f01c00fe3c 0x63d137a7231c0e3f

def z772 : W := mkw 0x4025e33c97312056 0x2e37da109574d1aa 0xf8fefc00e01cf1fc 0x63eec078fce1c1ff

def z773 : W := mkw 0x0001e38e93900000 0x9404ac00076ef000 0x0001ffffffff0000 0x1c2ec00007fff000

def z774 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x3801fffffffff00f 0xfebffe0007fff00c

def z775 : W := mkw 0x0001e38e93900000 0x9407ae00076ef000 0x0001ffffffff0000 0x1c0e000007fff000

def z776 : W := mkw 0x0001e30c93100002 0x0437da000564d000 0x0000fc0ffc1c0001 0x082fc00004fdc000

def z777 : W := mkw 0x6a6555d206e994d6 0xb2b074c5d70b6b4e 0x3fffffff03ffffff 0xfff0ffe7ff03ffff

def z778 : W := mkw 0x0001c30802000002 0x9037fa0007264000 0x0001fffffffc0003 0x983ffe0007ffc000

def z779 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3f1dffffe3ffffff 0xfffec9e727e3ffff

def z780 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc001fffffffcfff3 0xdb3fc1f807ffcff0

def z781 : W := mkw 0xb4919a694800e903 0x493b51fb6db406f0 0xfffffffffc00fff3 0xfb3ff1fffffc0ff0

def z782 : W := mkw 0x0001e38e93900000 0x9407fe00076ef000 0x0001ffffffff0001 0x9c0ffe0007fff000

def z783 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0001ffffffff0003 0x1c3fc00007fff000

def z784 : W := mkw 0x2491e38e93900002 0x9437fec94f6ef000 0xffe3ffffffff0003 0xfc3fffdfdffff000

def z785 : W := mkw 0x2a41554002489482 0x00b050c545014a44 0x3f01fff003fcffce 0xf2b0c1c70703cfcc

def z786 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc01dfffffc03fff3 0x5f7f09f827fc3ff3

def z787 : W := mkw 0x800018614800e901 0x490801f8009006f0 0xc001fffffc00fff3 0x5b3f01f807fc0ff0

def z788 : W := mkw 0x0800240401401000 0x0004880400419804 0x3f1dfc0fe3fffe3f 0xffeec9a724e3fe3f

def z789 : W := mkw 0x2a4155d202e89482 0xb2b074c5c70b6b4c 0x3fe1ffff1fffffce 0xfeb0f1c7c71fffcc

def z790 : W := mkw 0x800079e7db90e901 0xdd0cfff802daf6f0 0xc000000003fffff0 0xc700fff80003fff0

def z791 : W := mkw 0x74b400b204a12057 0xfa3ffffbfa1a21aa 0x070103ff1fe3f1fc 0x1feec187031e31ff

def z792 : W := mkw 0x592c0c312467727d 0x6a080136b0910dbf 0x3f1c00000000fffc 0x63c001a720000fff

def z793 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc001fffffc000fc3 0x183f01d807fc0fc0

def z794 : W := mkw 0x1ed1555002689481 0xf28fab2eaf034b4c 0xc01ffff003fcffcd 0x128f0e383f03cfcc

def z795 : W := mkw 0x3490820800000003 0x403fdbeb68240000 0xfffe000ffc000003 0xe83ffffff8fc0000

def z796 : W := mkw 0x2a41d75802689482 0xb2b370c5c7274b4c 0x3fe1fff0e3fcffce 0xf2bef1c7c7e3cfcc

def z797 : W := mkw 0x0800144000409000 0x000000c400010a44 0x3f01fc0003fcffce 0xf2a0c1c70403cfcc

def z798 : W := mkw 0x8001f3cedb908902 0x9537fec8076ef240 0x0001ffffffff0003 0x9c3ffe0007fff000

def z799 : W := mkw 0x6a6555e206c9b4d6 0x08b054d555196ae6 0xc71efc0f1c1f0e31 0x0d61cfbf3c1dfe33

def z800 : W := mkw 0x0000e38e93900000 0x0407de00006cf000 0x0000000ffc1f0001 0x0c0fce0000fdf000

def z801 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3fe0fc0003fcffcc 0xe2a0f1c7c403cfcc

def z802 : W := mkw 0x502400b204a12055 0xfa0cad32b21a21aa 0x3f1d03ff1fe3f1ff 0xffeec9a7231e31ff

def z803 : W := mkw 0x0001c30802000002 0x0033500005244000 0x0001fffffc1c0003 0x183fc00007fdc000

def z804 : W := mkw 0x2000000000000000 0x0000500140000000 0xfffe000000000003 0xe011fe7ff8000000

def z805 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0xf8fffffffffff03f 0xfffffe78fffff03f

def z806 : W := mkw 0x1d982c0521465229 0x400c8b2628c19c15 0x3f1ffc0fe3fffe3f 0xffeecfa73ce3fe3f

def z807 : W := mkw 0x2241e39e93b80482 0xb6b7fe01c76ef108 0x00e1ffffffff0003 0x9c3ffe00c7fff000

def z808 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0xfffffff003fcffce 0xf2b0f1ffff03cfcc

def z809 : W := mkw 0x80019a694800e901 0x490b013805b406f0 0x0001fffffc00fff0 0x1b0e000007fc0ff0

def z810 : W := mkw 0x3490000000000002 0x0037dacb68000000 0xfffe000000000003 0xa03ffe5ff8000000

def z811 : W := mkw 0x6265d3fa96b9a4d6 0xbeb376d1d73e63ea 0xc0e203f01c0001c0 0x00113658db1c01c0

def z812 : W := mkw 0x3490000000000003 0x403fdb2b68000000 0xfffe000000000003 0xa03ffe3ff8000000

def z813 : W := mkw 0x19080c2120467229 0x4808013620910cb5 0xff1c00000000fffc 0x63c001ff20000fff

def z814 : W := mkw 0x0a41555002689482 0xb2b0700487034b4c 0x3f01fff003fcffce 0xf2b0f1870703cfcc

def z815 : W := mkw 0x2a4155d202e89482 0xb2b074c5c70b6b4c 0x3ffdffff1fffffff 0xfff1ffe7e71fffff

def z816 : W := mkw 0x359820042106022b 0x403fdbeb68409001 0xfffe000000030003 0xe47ffffff8003003

def z817 : W := mkw 0xbd981c616846fb29 0x490801ff68910ef5 0xfffe00000000fffc 0x63c001fff8000fff

def z818 : W := mkw 0x74b5e39e97b10056 0xb637fe03ff6ef10a 0x3fffffffffff000f 0xbcfffe07fffff00f

def z819 : W := mkw 0x90019a694800e903 0x493b01fa25b406f0 0xff1dfffffc00fff3 0x7b3f01ff27fc0ff0

def z820 : W := mkw 0x0a40659693f81480 0xb684fe04824bf90c 0x0000000003ff000c 0x8480fe000003f00c

def z821 : W := mkw 0x0800040000401000 0x0000000400010804 0x3f01fff003fcffce 0xf2b0c1c70703cfcc

def z822 : W := mkw 0x0001e38e93900002 0x0437de00056cf000 0x0001fc0fffff0003 0x9c2fce0004fff000

def z823 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0xff1ffc0fe3fffe3f 0xffefcfbf3ce3fe3f

def z824 : W := mkw 0x2a4155d202e89482 0xb2b074c5c70b6b4c 0x3fe1fff01ffcffce 0xf2b1f7c7c71fcfcc

def z825 : W := mkw 0x2a40555002689480 0xb28070c5c2034b4c 0x3fe1fc0003fcffce 0xf2a0f1c7c403cfcc

def z826 : W := mkw 0x0491e38e93900002 0x9437fe080f6ef000 0xc003ffffffff0003 0x9c3ffe181ffff000

def z827 : W := mkw 0x359828052106422b 0x403fdbeb68c09411 0xffff000fe3e3f03f 0xfffffffff8e2303f

def z828 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xf8ffffff1fe3ffff 0xfff13ff8ff1e3fff

def z829 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3f01fc0fe3fffe3e 0xffeec18704e3fe3f

def z830 : W := mkw 0x0001e38e93900000 0x94032400076ef000 0x0001ffffffff0001 0x1c0f000007fff000

def z831 : W := mkw 0x3490000000000001 0x400801eb68000000 0xfffe000000000000 0xe0003ffff8000000

def z832 : W := mkw 0xa0019a694800e903 0x493b51f945b406f0 0xc701fffffc00fff3 0x5b3fc1ff07fc0ff0

def z833 : W := mkw 0x359828052106422b 0x403fdbeb68c09411 0xfffffc0fe003fe33 0xff7ffffffce03e33

def z834 : W := mkw 0x0001f3de93b08002 0xb637fec0876ef348 0x38e1ffffffffffcf 0xfebfffc0c7ffffcc

def z835 : W := mkw 0x000192680000a002 0x083300d0053402e0 0xc001fffffc00fff3 0x5b3f01f807fc0ff0

def z836 : W := mkw 0x80019a694800e901 0x4908013005b406f0 0x0001fffffc00fff0 0x1b2e018007fc0ff0

def z837 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3fe0fff0001cffcc 0x62b0f1c7c701cfcc

def z838 : W := mkw 0x80019a694800e903 0x493b53f805b406f0 0xc001fffffc00fff3 0x5b3f37f807fc0ff0

def z839 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xf8fffffffc00fff3 0x7b3f01f8fffc0ff0

def z840 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3fe1ffff03fffffe 0xfff0f1c7c703ffff

def z841 : W := mkw 0x0000618693900000 0x9404fe00024af000 0x0001ffffffff0003 0x9c3ffe0007fff000

def z842 : W := mkw 0x33497955232ec6ab 0xf2bcf9e3e7c2d759 0x00fc03ffe00301f1 0x0d5e3860e3e031f3

def z843 : W := mkw 0x84919a694800e903 0x493b03f80db406f0 0xc003fffffc00fff3 0x5b3f07f81ffc0ff0

def z844 : W := mkw 0x3000000000000003 0x403cd9e360000000 0xfffe000000000003 0xe03ffffff8000000

def z845 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xfffe000000000000 0x603ff7fff8000000

def z846 : W := mkw 0x2a40b6de91f89480 0x26878ec5c06dbb4c 0x3fe0000ffc03ffcd 0x6e8f0fc7c0fc3fcc

def z847 : W := mkw 0xd12caaaf6d876b7d 0x490f8d3a30fcb4b3 0xc01e000ffc030031 0x0d4f0e3838fc3033

def z848 : W := mkw 0x3490000000000001 0x400fdb2b68000000 0xfffe000000000003 0xe01ffe7ff8000000

def z849 : W := mkw 0x2a41555002689482 0x22b050c5c5014b4c 0x3fe0fc00001cffce 0xe2b0f1c7c401cfcc

def z850 : W := mkw 0x0000000000000000 0x0000000000000000 0xfffe000000000003 0xe031fffff8000000

def z851 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3ffffc0fe3fffe3f 0xffeeffa7fce3fe3f

def z852 : W := mkw 0x2a41d75892789482 0xb6b372c5c7274b4c 0x3fe1fff003fcffce 0xf2b0f1c7c703cfcc

def z853 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0xffe1fff003fcffcf 0xf2b1f1ffc703cfcc

def z854 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0001ffffffff0001 0x1c1f3e0007fff000

def z855 : W := mkw 0x0001e39e93b00002 0xb637fe00876ef108 0x38fdfffffffff1ff 0xfffffe60e7fff1ff

def z856 : W := mkw 0x0000a28e91900002 0x0437de00006cb000 0x0001fc0fffff0003 0x9c3ffe0004fff000

def z857 : W := mkw 0x0001e38e93900000 0x9404ac00076ef000 0x0001ffffffff0003 0x9c3ffe0007fff000

def z858 : W := mkw 0x0000a28e91900000 0x9407ae00026eb000 0x0001ffffffff0003 0x9c3ffe0007fff000

def z859 : W := mkw 0x800159614a00e903 0xd93871f8079246f0 0xc001fff003fcfff2 0xd330f1f80703cff0

def z860 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xf801ffffffe0ffff 0xfbbf01f807fe0ffc

def z861 : W := mkw 0x2241f3ce93988482 0x94b7fec1476ef240 0x0001ffffffff0003 0x9c3ffe0007fff000

def z862 : W := mkw 0x0001a20c01000002 0x0037da0005649000 0x0001ffffffff0003 0x9c3ffe0007fff000

def z863 : W := mkw 0x99081c616846fb29 0x4908013620910ef5 0x3f1c00000000fffc 0x63c001a720000fff

def z864 : W := mkw 0x19080c8320c65229 0xd0082526228b2c15 0x3f1d03ff1fe3fe3f 0xffd13fa7231e3e3f

def z865 : W := mkw 0x2241f3de93b88482 0xb6b7fec1c76ef348 0x00e1ffffffffffc3 0xde3fffc0c7ffffc0

def z866 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3fe1ffffe3fcffcf 0xfabef1c7c7e3cfcc

def z867 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3f1dfc0fe3fffe3c 0x7feec1a724e3fe3f

def z868 : W := mkw 0xb49018414800c903 0x413fdbeb68800650 0xfffe000000000e03 0xe03ffffff8000e00

def z869 : W := mkw 0x3490000000000000 0x0000000368000000 0xfffe000000000003 0xe0113e7ff8000000

def z870 : W := mkw 0x6a6555d206e994d6 0xb2b074c5d70b6b4e 0x3fffffff1fffffcf 0xfef1ffc7ff1fffcf

def z871 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xff01fffffc00fff3 0xfb3fc1ff07fc0ff0

def z872 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xf8ffffff1ffff1ff 0xfff1fe78ff1ff1ff

def z873 : W := mkw 0x99081c616846fb29 0x490801fe20910ef5 0xc70000000000fff0 0x430001ff00000ff0

def z874 : W := mkw 0x0a40145000689480 0x2280000480010b4c 0x3f01fc0003fcffce 0xf2a0c1870403cfcc

def z875 : W := mkw 0xa4919a694800e903 0x493b01f94db406f0 0xc0e3fffffc00fff3 0x5b3f01f8dffc0ff0

def z876 : W := mkw 0x7b6c1c71246ff6fd 0x6a8801f7f0910fff 0xfffe00000000fffc 0x63c001fff8000fff

def z877 : W := mkw 0x359828052106422b 0x403fdbeb68c09411 0xfffe0000e0000003 0xe03ffffff8e00000

def z878 : W := mkw 0x2800041000601002 0xb23070c5c203090c 0x3fe1fff003fcffce 0xf2b0f1c7c703cfcc

def z879 : W := mkw 0xd92c1c716c67fb7d 0x6b0801feb0910fff 0xfffe00000000fffc 0x63c001fff8000fff

def z880 : W := mkw 0x482404b204e13054 0xba002414921b29ae 0x0001ffff1ffffffc 0x1fc00000071fffff

def z881 : W := mkw 0x0000a28e91900000 0x04078e00006cb000 0x0000fc0ffc1f0001 0x0c2fce0004fdf000

def z882 : W := mkw 0x0001c38a92900002 0x94337600072e6000 0x0001fffffffc0003 0x983ff60007ffc000

def z883 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0x0000fff0fc000fc0 0x002e018007fc0fc0

def z884 : W := mkw 0x0001e39e93b00002 0xb637fe00876ef108 0x38e1ffffffff000f 0xbcbffe00c7fff00c

def z885 : W := mkw 0x0001f3ce93908002 0x9437fec0076ef240 0x0001ffffffff0e03 0x9c3fff8007fffe00

def z886 : W := mkw 0x0001e30c93100002 0x043300000564d000 0x0001fffffc1c0003 0x183f000007fdc000

def z887 : W := mkw 0xc0259adb4ca1c957 0xf33b25e897ae275a 0x38fefc00e3e30e0c 0xa4ee3f80fce23e0f

def z888 : W := mkw 0x80019a694800e900 0x0900001005b406f0 0x0001fffffc00fff3 0x1b2e000007fc0ff0

def z889 : W := mkw 0x3490000000000002 0x0034dac368000000 0xfffe000000000003 0xe031fffff8000000

def z890 : W := mkw 0x0001e38e93900002 0x9437ae00076ef000 0x0001ffffffff0003 0x1c3f0e0007fff000

def z891 : W := mkw 0x1000000000000000 0x0004880220000000 0xfffe000000000003 0xe011fe7ff8000000

def z892 : W := mkw 0xb4919a694800e900 0x0904da136db406f0 0x3ffffffffc00fff0 0xbb00fe07fffc0ff0

def z893 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xc0ff03ff1fe3f1fd 0x1fd13e78fb1e31ff

def z894 : W := mkw 0x2241f3de93b88482 0xb6b7fec1c76ef348 0x3fe1ffffffff01c3 0xfc3fffc7c7fff1c0

def z895 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3fe0fff003fc0fcc 0xa0b0f1c7c703cfcc

def z896 : W := mkw 0xe265d3fa4ea9add6 0xbbb374d9d73e63ea 0xc0e203f01c0001c0 0x00113658db1c01c0

def z897 : W := mkw 0x80009a694800e901 0x490b01f800b406f0 0xc00103fffc00fff3 0x5b1f01f803fc0ff0

def z898 : W := mkw 0x80019a694800e903 0x493801f005b406f0 0x0001fffffc00fff3 0x5b3e01e007fc0ff0

def z899 : W := mkw 0x0000e38e93900002 0x9437fe00026ef000 0x0000000fffff0003 0x8c3ffe0000fff000

def z900 : W := mkw 0x1001e38e93900002 0x9437fe02276ef000 0x3f1dffffffff0003 0xbc3ffe0727fff000

def z901 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc000fff0fc00fff0 0x433f01f807fc0ff0

def z902 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xf8ffffffffe3f1ff 0xffff3e78fffe31ff

def z903 : W := mkw 0x3ed0659693f81480 0xb684fe07ea4bf90c 0x3ffe000003ff000c 0xa480fe07f803f00c

def z904 : W := mkw 0x2a41d75802689482 0xb2b070c5c7274b4c 0x3fe1fffffffcffce 0xfab0f1c7c7ffcfcc

def z905 : W := mkw 0x2a41555002689480 0xb28020c5c7034b4c 0x3fe1fff003fcffce 0xf2a0c1c7c703cfcc

def z906 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x0701fff003fcffce 0x92b0f1870703cfcc

def z907 : W := mkw 0x3490000000000001 0x400fdb2b68000000 0xfffe000000000003 0xe02fffbff8000000

def z908 : W := mkw 0x3490200401000003 0x403fdbeb68409000 0xfffe000fe0030003 0xec3ffffff8e03000

def z909 : W := mkw 0x2a41555002689480 0xb28070c5c7034b4c 0x3fe1fff003fcffcc 0xf280f1c7c703cfcc

def z910 : W := mkw 0xb4919a494800c903 0x413fdbeb6da40650 0xfffffff0e000ffc3 0xf23fffffffe00fc0

def z911 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3fe1ffff03ffffcf 0xfeb0f9c7c703ffcc

def z912 : W := mkw 0x0001924800008003 0x403b01e805240240 0xc001fffffc00ffc3 0x5a3f01f807fc0fc0

def z913 : W := mkw 0x3491104000008003 0x403fdbeb6d000240 0xfffe03f0000001c3 0xe03ffffffb0001c0

def z914 : W := mkw 0x2000000000000003 0x403b51e940000000 0xfffe000000000003 0xe03ffffff8000000

def z915 : W := mkw 0x0001e38e93900002 0x94332400076ef000 0x0001ffffffff0000 0x1c2e000007fff000

def z916 : W := mkw 0x359828052106422b 0x403fdbeb68c09411 0xfffffc0fe3ff0033 0xfd7ffffffce3f033

def z917 : W := mkw 0xb4919a694800e903 0x493b01fb6db406f0 0xfffffffffc00fff3 0xfb3f3ffffffc0ff0

def z918 : W := mkw 0x2801144000409002 0x003050c545010a44 0x3fe1fff003fcffce 0xf2b0f1c7c703cfcc

def z919 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc01ffffffc00fff3 0x5b3f0ff83ffc0ff0

def z920 : W := mkw 0xc0259a694c01e957 0x493b01f815b406f2 0xc01ffffffc00fff3 0x5b7f01f83ffc0ff3

def z921 : W := mkw 0x9108aaaff9966b29 0x4d0f8f3a20fcb4b1 0xc01c000ffc030031 0x0d4f0e3820fc3033

def z922 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x07e1fff0001cffc2 0x5230f1c7c701cfc0

def z923 : W := mkw 0x3490104000008003 0x403fdbeb68000240 0xfffe00000000ffc3 0xe23ffffff8000fc0

def z924 : W := mkw 0x3490000000000002 0x0037dacb68000000 0xfffe000000000002 0xe031ffdff8000000

def z925 : W := mkw 0x0000200401000000 0x0004880000409000 0x0001ffffffff0003 0x9c3fc80007fff000

def z926 : W := mkw 0x0000002000002000 0x08000010001000a0 0xf8ff03ff1fe3f1ff 0xffd13e78fb1e31ff

def z927 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xfffe000000000000 0xa03fffdff8000000

def z928 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0xc01fffffffff0003 0x9c3ffe383ffff000

def z929 : W := mkw 0x3491104000008003 0x403fdbeb6d000240 0xfffefc0000000e03 0xe03ffffffc000e00

def z930 : W := mkw 0x3490000000000000 0x0004da0368000000 0xfffe000000000001 0xa001fe3ff8000000

def z931 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x38ffffffffff0003 0xbc3ffe00fffff000

def z932 : W := mkw 0x2a40145000689482 0x22b050c5c0010b4c 0x3fe1fc0003fcffce 0xf2b0f1c7c403cfcc

def z933 : W := mkw 0x2a41554002489482 0x90b070c547034a44 0x0701fff003fcffc2 0xd230f1c70703cfc0

def z934 : W := mkw 0x1000000000000003 0x403f89ea20000000 0xfffe000000000003 0xe03ffffff8000000

def z935 : W := mkw 0x2ed1555002689482 0xb2b070cdcf034b4c 0xffe3fff003fcffce 0xf2b0f1dfdf03cfcc

def z936 : W := mkw 0x3490a20c91100003 0x443fdbeb68649000 0xfffe0000e0000003 0xe03ffffff8e00000

def z937 : W := mkw 0x80019a694800e903 0x493b013805b406f0 0xc001fffffc00fff3 0x1b3f003807fc0ff0

def z938 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3f1dfc0fe3fffe3f 0xffffffa724e3fe3f

def z939 : W := mkw 0xaa41d7584a689d82 0xb3b370cdc7274b4c 0x3fe1fff003fcffce 0xf2b0f1c7c703cfcc

def z940 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x381dffffffff0003 0xfc3ffe2027fff000

def z941 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x07e1fff003fcffcc 0x12b0f1c7c703cfcc

def z942 : W := mkw 0x0001e38e93900002 0x0437de00056cf000 0x0000fc0ffc1f0003 0x8c3ffe0004fdf000

def z943 : W := mkw 0x1491e38e93900002 0x9437fe022f6ef000 0x001fffffffff0003 0x9c3ffe003ffff000

def z944 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xffff03ff1fe3f1ff 0xfff1fffffb1e31ff

def z945 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xfffe000f00030033 0xed7ffffff8003033

def z946 : W := mkw 0x1908242421463228 0x08048816205198a5 0xff1d03ff1ffff1ff 0xffd1c87f231ff1ff

def z947 : W := mkw 0x2001e38e93900002 0x9437fec1476ef000 0xffffffffffff0003 0xfc3ffffffffff000

def z948 : W := mkw 0x0000a28e91900000 0x04078e00006cb000 0x0000000fffff0001 0x8c0fce0000fff000

def z949 : W := mkw 0x0001820800000002 0x0033000005240000 0x0001fffffffc0003 0x983fc00007ffc000

def z950 : W := mkw 0x0001e38e93900002 0x9434fc00076ef000 0x0001ffffffff0003 0x9c3ef80007fff000

def z951 : W := mkw 0x7dbc0c312467727d 0x6a0801fff8910dbf 0xfffe00000000fffc 0x63c001fff8000fff

def z952 : W := mkw 0x2a41555002689480 0xb2807005c7034b4c 0x3fe1fff003fcffce 0xf2a0f187c703cfcc

def z953 : W := mkw 0x0001e30c93100002 0x0437da000564d000 0x0000fff0fc1c0000 0x003fc00007fdc000

def z954 : W := mkw 0x6a655550066994d6 0xb2b070c5d7034b4e 0x3ffffff003fcffce 0xf2f0f1c7ff03cfcf

def z955 : W := mkw 0xb4908a0948004903 0x413fdbeb68a40410 0xfffe0000e0000003 0xe03ffffff8e00000

def z956 : W := mkw 0x94919a694800e903 0x493b01fa2db406f0 0xc01ffffffc00fff3 0x5b3f01f83ffc0ff0

def z957 : W := mkw 0x3490000000000000 0x0007da0b68000000 0xfffe000000000000 0xa001fe1ff8000000

def z958 : W := mkw 0x0001e30c03000002 0x9037f8000766d000 0x0001ffffffff0003 0x9c3ff80007fff000

def z959 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0xffffffff03ffffff 0xfff1ffffff03ffff

def z960 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xf8ffffffffe3ffff 0xffff3ff8fffe3fff

def z961 : W := mkw 0x80019a694800e901 0x490801f805b406f0 0xc001fffffc00fff3 0x5b2e01f807fc0ff0

def z962 : W := mkw 0x2ed1555002689482 0xb2b072c5cf034b4c 0x3fe3fff003fcffce 0xf2b0f7c7df03cfcc

def z963 : W := mkw 0x2a40145000689480 0x228000c5c0010b4c 0x3fe0000003fcffcc 0xe280c1c7c003cfcc

def z964 : W := mkw 0x8a401c714868fd81 0x6b8801fc80910ffc 0xc00000000000fffc 0x438001f800000ffc

def z965 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xfffffc0fe0000003 0xf83ffffffce00000

def z966 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0xffe3fff003fcffce 0xf2b1f7dfdf03cfcc

def z967 : W := mkw 0xca65dffb4ee9fdd4 0xbb80241497bf6ffe 0x0001fffffffffffc 0x1fc0000007ffffff

def z968 : W := mkw 0x2490000000000002 0x003352c948000000 0xc7e2000000000000 0x0031f7dfd8000000

def z969 : W := mkw 0x6a64659697f914d4 0xb684fe05d24bf90e 0x3ffe000003ff000c 0xa4c0fe07f803f00f

def z970 : W := mkw 0x0001e38e93900000 0x9407ae00076ef000 0x0001ffffffff0003 0x9c2fce0007fff000

def z971 : W := mkw 0x80019a694800e901 0x490b013805b406f0 0xc001fffffc00fff3 0x5b2f01b807fc0ff0

def z972 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0001fffffffff1c3 0xde3ffe4007fff1c0

def z973 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xf81dfffffc00ffff 0x7bff01f827fc0fff

def z974 : W := mkw 0x8001db694a00e903 0x493b51f805b446f0 0xc001fffffc1cfff3 0x5b3fc1f807fdcff0

def z975 : W := mkw 0x0001f3ce93908002 0x9437fe00076ef240 0x0001ffffffffffc3 0x9e3ffe0007ffffc0

def z976 : W := mkw 0xa4919a694800e903 0x493b53f94db406f0 0xf8fffffffc00fff3 0xfb3f3ff8fffc0ff0

def z977 : W := mkw 0x4025e38e97910056 0x9437fe00176ef002 0x001fffffffff0003 0x9c7ffe003ffff003

def z978 : W := mkw 0x0001e30c93100002 0x0437da000564d000 0x0001fffffc1c0003 0x983ffe0007fdc000

def z979 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xfffe000003e3000f 0xe4fffffff802300f

def z980 : W := mkw 0x3491e30c93100003 0x443fdbeb6d64d000 0xfffffffffc1c0003 0xf83ffffffffdc000

def z981 : W := mkw 0xbd99be4d6946db2b 0x413fdbef6de59e55 0x0700fc00e01c0e00 0x002ec18704e1ce00

def z982 : W := mkw 0x6a6555d206e994d6 0xb2b074c5d70b6b4e 0xfffffff003ffffcf 0xf6f1ffffff03ffcf

def z983 : W := mkw 0x4a6414f204e9b4d4 0xba802414921b2bee 0x000103ff1fe3fffc 0x1fc00000031e3fff

def z984 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc001fff0fc00ffc2 0x523f01d807fc0fc0

def z985 : W := mkw 0x3491e30c93100003 0x443fdbeb6d64d000 0xfffffc0fe3ff0003 0xfc3ffffffce3f000

def z986 : W := mkw 0x00019a490000c003 0x403b01e005a40650 0x0001fffffc00fff3 0x5b3f01e007fc0ff0

def z987 : W := mkw 0xb4919a694800e903 0x493b01fb6db406f0 0xc701fffffc00fff3 0x5b3f01ff07fc0ff0

def z988 : W := mkw 0x3490080100004003 0x403fdbeb68800410 0xfffe000fe0000033 0xe93ffffff8e00030

def z989 : W := mkw 0x3491e38e93900002 0x9437fe036f6ef000 0x0701ffffffff0003 0x9c3ffe0707fff000

def z990 : W := mkw 0x3491c30892100003 0x443fdbeb6d244000 0xfffe000000000003 0xe03ffffff8000000

def z991 : W := mkw 0x2a41145000689482 0x22b000c5c5010b4c 0x3fe1fff003fcffce 0xf2b0c1c7c703cfcc

def z992 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0xfffffc0fe3fffe3f 0xffeec9fffce3fe3f

def z993 : W := mkw 0xbb481c71686effa9 0x6b8801ffe0910ffd 0xfffc00000000fffc 0x63c001ffe0000fff

def z994 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0001ffffffff0002 0x9c3ef00007fff000

def z995 : W := mkw 0x3490000000000000 0x0004da0368000000 0xfffe000000000000 0xe000fe7ff8000000

def z996 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc001fffffc00fff0 0x1b3f01d807fc0ff0

def z997 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x381dffffffff000f 0xbcfffe0027fff00f

def z998 : W := mkw 0x2a41555002689482 0x22b050c5c5014b4c 0x0700fc00001cffcc 0x02a0c1870401cfcc

def z999 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3fe0fff0001c0fc2 0xe030f1c7c701cfc0

def z1000 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xffff000f0000f033 0xfb3ffffff8000030

def z1001 : W := mkw 0x3490000000000001 0x400853eb68000000 0xfffe000000000000 0x600037fff8000000

def z1002 : W := mkw 0x0001e38e93900002 0x0437de00056cf000 0x0001fffffc1f0003 0x1c3fce0007fdf000

def z1003 : W := mkw 0xa0019a694800e903 0x493b51f945b406f0 0xc0e1fffffc00fff3 0x5b3f31f8c7fc0ff0

def z1004 : W := mkw 0x7dbc249625e7127c 0xb204fe07fa4bb90f 0x3ffe000003ff000c 0xa4c0fe07f803f00f

def z1005 : W := mkw 0x2a40451002681480 0xb2807005c203490c 0x3fe1fff003fcffce 0xf2b0f1c7c703cfcc

def z1006 : W := mkw 0x512caaafb597627d 0x4c0f8f3230fcb4b3 0xc01e000ffc030031 0x0d4f0e3838fc3033

def z1007 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0xc0e3ffffffff0003 0x9c3ffe58dffff000

def z1008 : W := mkw 0x2000000000000000 0x000000c140000000 0xfffe000000000003 0xe0113ffff8000000

def z1009 : W := mkw 0x9108aa2d69066b29 0x490f893a20f494b1 0xc000000ffc000031 0x090f003800fc0030

def z1010 : W := mkw 0x0001e38e93900002 0x9437fec0076ef000 0x0001ffffffff0003 0xdc3fffc007fff000

def z1011 : W := mkw 0x0001e38e93900002 0x0437de00056cf000 0x0000fc0ffc1f0000 0x0c2ec00004fdf000

def z1012 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xffff03ff1c000003 0xf83ffffffb1c0000

def z1013 : W := mkw 0x2ed1555002689482 0xb2b372cdcf034b4c 0x3fe1fff003fcffce 0xf2b0f1c7c703cfcc

def z1014 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc001fffffc00fff1 0x1b2f01b807fc0ff0

def z1015 : W := mkw 0x0800041000601000 0xb20020048203090c 0x3f01fff003fcffce 0xf2a0c1870703cfcc

def z1016 : W := mkw 0x2a41d7da92f89482 0xb6b074c5c72f6b4c 0x3fe1fff01ffcffce 0xf2b0f1c7c71fcfcc

def z1017 : W := mkw 0x80019a694800e902 0x0933001005b406f0 0x0001fffffc00fff0 0x1b2e000007fc0ff0

def z1018 : W := mkw 0x1109e38eb396022a 0x9437fe02276ef001 0x001dffffffff0003 0x9c7ffe0027fff003

def z1019 : W := mkw 0x2a41555002689482 0xb2b370cdc7034b4c 0xffe1fff003fcffce 0xf2b1f1dfc703cfcc

def z1020 : W := mkw 0x3491820800000003 0x403fdbeb6d240000 0xfffe03f01c000003 0xe03ffffffb1c0000

def z1021 : W := mkw 0x3490000000000002 0x0037dacb68000000 0xfffe000000000003 0xe011fe7ff8000000

def z1022 : W := mkw 0x80019a694800e902 0x093300d005b406f0 0x0001fffffc00fff3 0x5b3f01c007fc0ff0

def z1023 : W := mkw 0x2000000000000002 0x003050c140000000 0xffe2000000000002 0xe031f7dfd8000000

def z1024 : W := mkw 0x3490000000000003 0x403b53eb68000000 0xfffe000000000003 0xe0113ffff8000000

def z1025 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x001dffffffff0033 0x9d7ffe2027fff033

def z1026 : W := mkw 0x4a6555f206e9b4d4 0xba802414971b6bee 0x0001fff01ffcffcc 0x12800000071fcfcc

def z1027 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xf8e1fffffc00fff3 0xfb3f31f8c7fc0ff0

def z1028 : W := mkw 0xb4919a694800e903 0x493b53fb6db406f0 0xfffffffffc00fff3 0x7b3f37fffffc0ff0

def z1029 : W := mkw 0x7b6c659627ef16fc 0xb284fc07f24bf90f 0x3ffe000003ff000c 0xa4c0fe07f803f00f

def z1030 : W := mkw 0x1490000000000001 0x400f8b2a28000000 0xfffe000000000003 0xe03ffffff8000000

def z1031 : W := mkw 0x0001e38e93900002 0x94337400076ef000 0x0001ffffffff0003 0x9c3ff00007fff000

def z1032 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0001ffffffff0000 0x1c3ff60007fff000

def z1033 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc001ffffffe3ffff 0x5fff01f807fe3fff

def z1034 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0000fc0fffff0001 0x8c2ffe0004fff000

def z1035 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xffff000003e0f00f 0xf2bffffff802000c

def z1036 : W := mkw 0x2a4155d292f89482 0xb6b076c5c70b6b4c 0x3fe1fff003fcffce 0xf2b0f7c7c703cfcc

def z1037 : W := mkw 0x6a6555d206e994d6 0xb2b074c5d70b6b4e 0x3fe3fff003fcffce 0xf2b0f7c7df03cfcc

def z1038 : W := mkw 0x09082c0521465229 0x4008012400c19c15 0x3f01fc0fe3fffe3f 0xffeec1a704e3fe3f

def z1039 : W := mkw 0x80019a694800e902 0x093300d805b406f0 0xc001fffffc00fff3 0x1b3f005807fc0ff0

def z1040 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xc7e2000000000003 0x403ff7ffd8000000

def z1041 : W := mkw 0x0001a20c01000002 0x0037880005649000 0x0001fffffc1c0003 0x183fc00007fdc000

def z1042 : W := mkw 0x2a41d7da92f89482 0xb6b376c5c72f6b4c 0x3fe1fffffffcffcf 0xfabff7c7c7ffcfcc

def z1043 : W := mkw 0x4a65f7fe97f9b4d4 0xbe802414977ffbee 0x0001fffffffffffc 0x1fc0000007ffffff

def z1044 : W := mkw 0x80019a694800e900 0x0903001005b406f0 0x0001fffffc00fff1 0x1b0f000007fc0ff0

def z1045 : W := mkw 0x1108281521264229 0xf20ca922a2c29519 0x38fd03ffe3e3f1ff 0xffde3860e3e231ff

def z1046 : W := mkw 0x0001e39e93b00002 0xb637fe00876ef108 0x00e1ffffffff01c3 0x9c3ffe40c7fff1c0

def z1047 : W := mkw 0x9909b66c6946bb2a 0x093788de25759ae5 0xff1c03f01fff01cc 0xa4d1c85f231ff1cf

def z1048 : W := mkw 0xaa40cf394a687d81 0xfb8b713dc2b74dbc 0xffe0000ffffc003d 0xa98ff03fc0ffc03c

def z1049 : W := mkw 0x2a4155d202e89482 0xb2b074c5c70b6b4c 0xffffffff1fffffcf 0xfeb1ffffff1fffcc

def z1050 : W := mkw 0x349118410000c003 0x403fdbeb6d800650 0xffffffffe000fff3 0xfb3fffffffe00ff0

def z1051 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0000fff0ffff0000 0x843ffe0007fff000

def z1052 : W := mkw 0x3490000000000003 0x403851eb68000000 0xfffe000000000003 0xe031fffff8000000

def z1053 : W := mkw 0x0001c38a02800002 0x90337400072e6000 0x0001ffffffff0003 0x9c3ffe0007fff000

def z1054 : W := mkw 0x0001e30c93100002 0x0437da000564d000 0x0001fffffc1c0000 0x182ec00007fdc000

def z1055 : W := mkw 0x3490200401000003 0x403fdbeb68409000 0xfffe000003ff0003 0xe43ffffff803f000

def z1056 : W := mkw 0x80019a694800e901 0x4908013005b406f0 0x0001fffffc00fff1 0x1b0e002007fc0ff0

def z1057 : W := mkw 0x0801144000409000 0x0000000405010a44 0x3f01fff003fcffce 0xf2a0c1870703cfcc

def z1058 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0001ffffffff0003 0x9c2ec80007fff000

def z1059 : W := mkw 0xa4919a694800e903 0x493b53f94db406f0 0xc001fffffc00fff3 0x5b3f01f807fc0ff0

def z1060 : W := mkw 0x4025e39e97b10056 0xb637fe00976ef10a 0xf8ffffffffff000f 0xfcfffe78fffff00f

def z1061 : W := mkw 0x80019a694800e902 0x0933001005b406f0 0xc001fffffc00fff3 0x5b3f007807fc0ff0

def z1062 : W := mkw 0x2a40145000689480 0xb28020c5c2030b4c 0x3fe1fff003fcffce 0xf2b0f1c7c703cfcc

def z1063 : W := mkw 0x2491e38e93900002 0x9437fec94f6ef000 0xf8ffffffffff0003 0xfc3ffe78fffff000

def z1064 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xfffe00000000f03f 0xe3fffffff800003f

def z1065 : W := mkw 0x2001514002008002 0x903070c147024240 0x3fe1fff003fcffc2 0xf230f1c7c703cfc0

def z1066 : W := mkw 0x26d1f3de93b88482 0xb6b7fec9cf6ef348 0xc0e3ffffffff01c3 0x9c3ffe58dffff1c0

def z1067 : W := mkw 0x3490000000000001 0x400cdbeb68000000 0xfffe000000000003 0xe02efffff8000000

def z1068 : W := mkw 0x3490080100004003 0x403fdbeb68800410 0xfffe00000000fe33 0xe33ffffff8000e30

def z1069 : W := mkw 0x3490000000000002 0x0037da0368000000 0xfffe000000000003 0xe03ffe7ff8000000

def z1070 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0000fffffc1f0001 0x0c3ffe0007fdf000

def z1071 : W := mkw 0x0000082100006001 0x48080130009004b0 0x0001fffffc00fff3 0x5b2e01a007fc0ff0

def z1072 : W := mkw 0x0000208601800000 0x00048c000048b000 0x0001fc0fffff0003 0x9c2fce0004fff000

def z1073 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0xff1dfc0fe3fffe3f 0xffffc9ff24e3fe3f

def z1074 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3fe1ffff1ffcffcf 0xfab1f1c7c71fcfcc

def z1075 : W := mkw 0x4025e39e97b10056 0xb637fe00976ef10a 0x38fffffffffff03f 0xfffffe20fffff03f

def z1076 : W := mkw 0x4025e39e97b10056 0xb637fe00976ef10a 0x38fffffffffff1cf 0xfefffe40fffff1cf

def z1077 : W := mkw 0x2a40555002689482 0xb2b070c5c2034b4c 0x3fe0000003fcffce 0xe2b0f1c7c003cfcc

def z1078 : W := mkw 0x2001e39e93b00002 0xb637fec1c76ef108 0x3fe1fffffffff1cf 0xfebfffc7c7fff1cc

def z1079 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3fe1fff003fcffcc 0xb2a0f187c703cfcc

def z1080 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3fe1ffff03fcffff 0xfbb0f1e7c703cffc

def z1081 : W := mkw 0x2a41d7da92f89482 0xb6b376c5c72f6b4c 0x3fe1ffff1fffffcf 0xfeb1ffc7c71fffcc

def z1082 : W := mkw 0x99080c2168467b29 0x4908013e20910cb5 0xff1c00000000fe3c 0x63c001bf20000e3f

def z1083 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x0701fff003fcffce 0x52b0c1c70703cfcc

def z1084 : W := mkw 0xa241db694a08ed83 0x49bb51f945b446f0 0xc001fffffc00fff3 0x5b3f01f807fc0ff0

def z1085 : W := mkw 0x482404a204c13054 0x08000414101928a6 0xff1ffc0f1ffffe3f 0xffe1cfbf3c1ffe3f

def z1086 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0001fff0fffc0002 0x903ff60007ffc000

def z1087 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xf8fe03ff1c03f1fd 0x6fd13e78fb1c31ff

def z1088 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc001fffffc00fff3 0xdb3f3ff807fc0ff0

def z1089 : W := mkw 0x3491e38e93900002 0x9437fec36f6ef000 0x3fffffffffff0003 0xfc3fffc7fffff000

def z1090 : W := mkw 0x1000000000000003 0x403fdb2220000000 0xfffe000000000003 0xe03ffffff8000000

def z1091 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x07e1fff003fc0fc2 0x9030f1c7c703cfc0

def z1092 : W := mkw 0xb491fb4ddb10c903 0x453fdbeb6de4d650 0xfffefc00e01c0e03 0xe03ffffffce1ce00

def z1093 : W := mkw 0x000118610000e003 0x483801f0059006f0 0xc001fffffc00fff3 0x5b3f01f807fc0ff0

def z1094 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3ffdfc0fe3fffe3f 0xfffef9e7e4e3fe3f

def z1095 : W := mkw 0x3490000000000002 0x0037dacb68000000 0xc7e2000000000000 0x0011f65fd8000000

def z1096 : W := mkw 0x3490000000000001 0x400fdbeb68000000 0xfffe000000000001 0xe00ffffff8000000

def z1097 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3f1cfc00e3fffe3c 0xe7eec9a724e3fe3f

def z1098 : W := mkw 0x3491820800000003 0x403fdbeb6d240000 0xfffefc00e0000003 0xe03ffffffce00000

def z1099 : W := mkw 0x0001e38e93900000 0x94002400076ef000 0x0001ffffffff0003 0x1c2e000007fff000

def z1100 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0001ffffffff0001 0x1c2fce0007fff000

def z1101 : W := mkw 0x6a6555d206e994d6 0xb2b074c5d70b6b4e 0x3fe1fff003ffffce 0xf6f0f1c7c703ffcf

def z1102 : W := mkw 0x2490000000000003 0x403b53e948000000 0xffe2000000000003 0xe03ff7ffd8000000

def z1103 : W := mkw 0x492c0cb324e7727c 0xba002414929b2dbf 0x000103ff1fe3fffc 0x1fc00000031e3fff

def z1104 : W := mkw 0x3490000000000003 0x403b53eb68000000 0xc7e2000000000000 0x001137dfd8000000

def z1105 : W := mkw 0x1d982c0521465229 0x400c892e28c19c15 0xff1ffc0fe3fffe3f 0xffeec9bf3ce3fe3f

def z1106 : W := mkw 0x2ed1d7da92f89482 0xb6b376cdcf2f6b4c 0xffe3fff01ffcffce 0xf2b1f7dfdf1fcfcc

def z1107 : W := mkw 0x0001e38e93900002 0x0437de00056cf000 0x0000fc00fc1c0000 0x002fc60004fdc000

def z1108 : W := mkw 0x592c6596b7f7127c 0xb604fe06b24bf90f 0x3ffe000003ff000c 0xa4c0fe07f803f00f

def z1109 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3ffdfff003fcfffe 0xf3f0f1e7e703cfff

def z1110 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xfffffc0003fc0003 0xf03ffffffc03c000

def z1111 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0001fffffc1c0003 0x183ff60007fdc000

def z1112 : W := mkw 0x512c28a72587627d 0x480c8d3230d8b4b3 0x001c000ffc030031 0x0d4e082020fc3033

def z1113 : W := mkw 0x592c0c212447727d 0x4808013630910cb7 0xff1e00000000fe3c 0x63c001bf38000e3f

def z1114 : W := mkw 0x0001e38e93900002 0x94332400076ef000 0x0001ffffffff0003 0x9c3f3e0007fff000

def z1115 : W := mkw 0x80019a694800e901 0x490b01f805b406f0 0xc001fffffc00fff1 0x5b0f01f807fc0ff0

def z1116 : W := mkw 0x80019a694800e903 0x493b51f805b406f0 0xc001fffffc00fff3 0xdb3ff1f807fc0ff0

def z1117 : W := mkw 0x0001924800008002 0x0033000005240240 0x0001fffffc00ffc3 0x1a3f000007fc0fc0

def z1118 : W := mkw 0x3b486596b3fe16a8 0xb684fe07e24bf90d 0x3ffc000003ff000c 0xa4c0fe07e003f00f

def z1119 : W := mkw 0x3490000000000000 0x0004dacb68000000 0xfffe000000000000 0xa000fe5ff8000000

def z1120 : W := mkw 0x2a41555002689482 0xb2b370c5c7034b4c 0x3fe1fff003fcffcf 0xf2bff1c7c703cfcc

def z1121 : W := mkw 0x3490610493100003 0x443fdbeb6840d000 0xfffe0000001c0003 0xe03ffffff801c000

def z1122 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0000fff0fc1c0003 0x803ffe0007fdc000

def z1123 : W := mkw 0x1108282521066229 0x480c893220d094b1 0xc01c000ffc030031 0x0d4f083820fc3033

def z1124 : W := mkw 0x3490080100004003 0x403fdbeb68800410 0xfffffc0fe3e3fe3f 0xfffffffffce23e3f

def z1125 : W := mkw 0x09082c0521465228 0x0000000400c19c15 0xf8fffc0fe3fffe3f 0xffd13e78fce3fe3f

def z1126 : W := mkw 0x0000a28e91900000 0x04048c00006cb000 0x0001fc0fffff0003 0x9c2ec80004fff000

def z1127 : W := mkw 0xc92dbeff6de7fb7c 0xbb00241497ffbfff 0x0001fffffffffffc 0x1fc0000007ffffff

def z1128 : W := mkw 0x0001a28e91900002 0x04378e00056cb000 0x0001ffffffff0003 0x9c3fce0007fff000

def z1129 : W := mkw 0x3490000000000001 0x400f8beb68000000 0xfffe000000000003 0xe01f3ffff8000000

def z1130 : W := mkw 0x2001e38e93900002 0x9437fec1476ef000 0x00e1ffffffff0003 0x9c3ffe40c7fff000

def z1131 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x000003ffffff0001 0x8c1ffe0003fff000

def z1132 : W := mkw 0x3490000000000003 0x403b53eb68000000 0xfffe000000000003 0x603f37fff8000000

def z1133 : W := mkw 0x89081c616846fb29 0x490801fc00910ef5 0xc00000000000fffc 0x43c001f800000fff

def z1134 : W := mkw 0x0001e38e93900002 0x9437fec8076ef000 0xc001ffffffff0003 0x9c3ffe5807fff000

def z1135 : W := mkw 0x2a41554002489482 0x00b050c545014a44 0x3fe1fff0001cffc2 0xf230f1c7c701cfc0

def z1136 : W := mkw 0x3491e38e93900002 0x9437fecb6f6ef000 0xffffffffffff0003 0xbc3ffe5ffffff000

def z1137 : W := mkw 0x800192684800a902 0x093300d8053402e0 0xc001fffffc00ffc3 0x5a3f01d807fc0fc0

def z1138 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x0700fff0001c0fc0 0x0020c1870701cfc0

def z1139 : W := mkw 0x3491a20c01000003 0x403fdbeb6d649000 0xffffffffffff0003 0xfc3ffffffffff000

def z1140 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3fe003f003fcffcc 0xe290f1c7c303cfcc

def z1141 : W := mkw 0x3490000000000003 0x403b01eb68000000 0xfffe000000000003 0xe03f3ffff8000000

def z1142 : W := mkw 0x0000082100006003 0x483b01f8009004b0 0xc001fffffc00fff3 0x5b3f01f807fc0ff0

def z1143 : W := mkw 0x3490000000000001 0x400801eb68000000 0xfffe000000000000 0x601137fff8000000

def z1144 : W := mkw 0xb4919a494800c903 0x413fdbeb6da40650 0xfffffc0fe000fe33 0xfb3ffffffce00e30

def z1145 : W := mkw 0x2000000000000002 0x0037dac140000000 0xfffe000000000003 0xe03ffffff8000000

def z1146 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xfffe000000000001 0xa01ffe7ff8000000

def z1147 : W := mkw 0x0a41555002689482 0xb2b020c487034b4c 0x3f01fff003fcffce 0xf2b0c1c70703cfcc

def z1148 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0001ffffffff0000 0x9c2efe0007fff000

def z1149 : W := mkw 0x2a41d75802689482 0xb2b370c5c7274b4c 0x3fe1fff01ffcffce 0xf2b1f1c7c71fcfcc

def z1150 : W := mkw 0x2a41554002489482 0x00b050c545014a44 0x0700fc00001cffc0 0x4220c1c70401cfc0

def z1151 : W := mkw 0x9598aa2d69066b29 0x490f8b3a28f494b1 0xc01e000ffc030031 0x0d4f0e3838fc3033

def z1152 : W := mkw 0x3490000000000001 0x400c89eb68000000 0xfffe000000000003 0xe03ffffff8000000

def z1153 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0xc001ffffffff0003 0xdc3ffe7807fff000

def z1154 : W := mkw 0x8001db69da10e903 0x4d3b53f805b446f0 0xc001fffffc00fff3 0x5b3f01f807fc0ff0

def z1155 : W := mkw 0x3491410002000003 0x403fdbeb6d004000 0xfffefc00001c0003 0xe03ffffffc01c000

def z1156 : W := mkw 0x09082c0521465228 0x0004880400c19c15 0x3f01fc0fe3fffe3f 0xffeec98704e3fe3f

def z1157 : W := mkw 0x2a40145000689480 0x228000c5c0010b4c 0x3fe0fc00001cffcc 0x62a0c1c7c401cfcc

def z1158 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x38e1ffffffff0003 0xfc3ffe40c7fff000

def z1159 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xffff03f00000f1c3 0xf23ffffffb0001c0

def z1160 : W := mkw 0x492defbfb7f7727c 0xbe00241497fffdbf 0x0001fffffffffffc 0x1fc0000007ffffff

def z1161 : W := mkw 0x3490080100004003 0x403fdbeb68800410 0xfffefc00e0000e03 0xe03ffffffce00e00

def z1162 : W := mkw 0x80019a694800e901 0x490b013805b406f0 0xc001fffffc00fff3 0x5b1f007807fc0ff0

def z1163 : W := mkw 0x34918a0900004003 0x403fdbeb6da40410 0xfffffffffc00fe33 0xfb3ffffffffc0e30

def z1164 : W := mkw 0x3491000000000003 0x403fdbeb6d000000 0xfffffff000000003 0xf03fffffff000000

def z1165 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xffe2000000000002 0xe03ff7dfd8000000

def z1166 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3ffdfff003fcffcf 0xf2b0f9e7e703cfcc

def z1167 : W := mkw 0x0a41555002689480 0xb280200487034b4c 0x3fe1fff003fcffce 0xf2b0f1c7c703cfcc

def z1168 : W := mkw 0x0000208601800000 0x9004ac00024ab000 0x0001ffffffff0003 0x9c2ec80007fff000

def z1169 : W := mkw 0x2a40555002689480 0xb28070c5c2034b4c 0x3fe103f003fcffce 0xf290f1c7c303cfcc

def z1170 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x3f01ffffffff0003 0xfc3fff8707fff000

def z1171 : W := mkw 0x402400b204a12054 0xba002410921a21aa 0xf8fe03ff1fe301fd 0xadd13e78fb1e31ff

def z1172 : W := mkw 0x592c249625e7127c 0xb204ac06b24bb90f 0x3f1c000003ff000c 0xa4c0c8072003f00f

def z1173 : W := mkw 0x2a4155d202e89482 0xb2b074c5c70b6b4c 0x3fe1fff003ffffce 0xf6b0ffc7c703ffcc

def z1174 : W := mkw 0x3490000000000001 0x400cdbeb68000000 0xfffe000000000003 0xe011fffff8000000

def z1175 : W := mkw 0x0000a28e91900000 0x04078e00006cb000 0x0001fc0fffff0001 0x1c0f0e0004fff000

def z1176 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc0e3fffffc00fff3 0x5b3f37f8dffc0ff0

def z1177 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0x0001fffffc00fff2 0x5b3e01c007fc0ff0

def z1178 : W := mkw 0x4a6445b206e934d4 0xba802414921b69ae 0x000103ff1ffff1fc 0x1fc00000031ff1ff

def z1179 : W := mkw 0x91099a696806eb2b 0x493b01fa25b406f1 0xc01dfffffc00fff3 0x5b7f01f827fc0ff3

def z1180 : W := mkw 0x1000000000000001 0x4008012220000000 0xfffe000000000003 0xe0113ffff8000000

def z1181 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xfffffc000000fe03 0xf23ffffffc000e00

def z1182 : W := mkw 0x88001c614840f901 0x490801fc00910ef4 0xff0000000000fffc 0x638001ff00000ffc

def z1183 : W := mkw 0x2490000000000002 0x003352c948000000 0xffe2000000000000 0xa011f65fd8000000

def z1184 : W := mkw 0x2a41d7da02e89482 0xb2b374c5c72f6b4c 0x3fe1ffffffffffcf 0xfebfffc7c7ffffcc

def z1185 : W := mkw 0x00018a2900006003 0x483b013005b404b0 0xc001fffffc00fff3 0x5b3f01f807fc0ff0

def z1186 : W := mkw 0x2a41965800689482 0x22b300c5c5250b4c 0x3fe1fffffc00ffcf 0x7abf01c7c7fc0fcc

def z1187 : W := mkw 0x2a41555002689482 0xb2b372c5c7034b4c 0x3fe1fff003fcffce 0xf2b1f7c7c703cfcc

def z1188 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x0701fc0fe3fffe3f 0x9feec98704e3fe3f

def z1189 : W := mkw 0x0001e30c93100002 0x0437da000564d000 0x0001ffffffff0003 0x9c3fc80007fff000

def z1190 : W := mkw 0x4024089304a14055 0xf2082520928a251a 0x38fffc0fe3e3fe3f 0xffee3fa0fce23e3f

def z1191 : W := mkw 0x80019a494800c903 0x413b01e805a40650 0x0001fffffc00ffc3 0x5a3f01c007fc0fc0

def z1192 : W := mkw 0x80019a694800e901 0x4908013005b406f0 0xc001fffffc00fff3 0x5b3f01f807fc0ff0

def z1193 : W := mkw 0x2001e38e93900002 0x9437fe01476ef000 0x3fe1ffffffff0003 0xbc3ffe07c7fff000

def z1194 : W := mkw 0x3490000000000003 0x403b53eb68000000 0xfffe000000000002 0xe031f7fff8000000

def z1195 : W := mkw 0x2490000000000002 0x003352c948000000 0xfffe000000000003 0xe031fffff8000000

def z1196 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0x0001fffffc00fff3 0x5b2e01a007fc0ff0

def z1197 : W := mkw 0x2241f3de93b88482 0xb6b7fec1c76ef348 0x38e1fffffffff1cf 0xfebffe40c7fff1cc

def z1198 : W := mkw 0x4025e39e97b10056 0xb637fe00976ef10a 0x00e3ffffffff0003 0x9c3ffe00dffff000

def z1199 : W := mkw 0x3490200401000003 0x403fdbeb68409000 0xfffffc0fe3fff03f 0xfffffffffce3f03f

def z1200 : W := mkw 0x0001f3ce93908002 0x9437fec0076ef240 0x0001ffffffff01c3 0x9c3ffe4007fff1c0

def z1201 : W := mkw 0x2a41555002689482 0x22b050c5c5014b4c 0x07e0fc00001c0fc0 0x0020c1c7c401cfc0

def z1202 : W := mkw 0x3490000000000002 0x003352cb68000000 0xfffe000000000000 0x2011365ff8000000

def z1203 : W := mkw 0x0001e39e93b00002 0xb637fe00876ef108 0x0001fffffffff1cf 0x9ebffe0007fff1cc

def z1204 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0000fff0fc1c0000 0x002ec00007fdc000

def z1205 : W := mkw 0x0001e38e93900000 0x9404fe00076ef000 0x0001ffffffff0003 0x9c2efe0007fff000

def z1206 : W := mkw 0x3490280501004003 0x403fdbeb68c09410 0xfffffc0fe3fffe33 0xff3ffffffce3fe30

def z1207 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xfffe000000000001 0x601f3ffff8000000

def z1208 : W := mkw 0x9490aaafd9906901 0x4d0f8f3a28fcb4b0 0xc01e000ffc030031 0x0d0f0e3838fc3030

def z1209 : W := mkw 0x0000e38e93900000 0x9407fe00026ef000 0x0001fc0fffff0003 0x9c2ffe0004fff000

def z1210 : W := mkw 0x08000c0100405001 0x4008012400810c14 0x3f1dfc0fe3fffe3f 0xffeec9a724e3fe3f

def z1211 : W := mkw 0x0001e38e93900002 0x94337600076ef000 0x0001ffffffff0003 0x1c3f360007fff000

def z1212 : W := mkw 0x9108aa2d69066b29 0x490c893220f494b1 0x001c000ffc030031 0x0d4e082020fc3033

def z1213 : W := mkw 0x0001e38e93900002 0x9437fe00076ef000 0x0001fffffffff033 0xdf3ffe2007fff030

def z1214 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xfffe000000000001 0xa02fffbff8000000

def z1215 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc001ffffffe3fff3 0xdf3f09f807fe3ff0

def z1216 : W := mkw 0x512c28252507627d 0x480c893230d094b3 0xc01e000fe0030031 0x0d4e083838e03033

def z1217 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc001fffffc00fff1 0x1b1f007807fc0ff0

def z1218 : W := mkw 0xa4919a694800e903 0x493b53f94db406f0 0xffe3fffffc00fff3 0xfb3ff7ffdffc0ff0

def z1219 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x071dfc0fe3fffe3d 0x1feec9a724e3fe3f

def z1220 : W := mkw 0x0000e38e93900000 0x9407ae00026ef000 0x0000000fffff0001 0x0c0f0e0000fff000

def z1221 : W := mkw 0x55bc28a72587627d 0x480f8f3a38d8b4b3 0xc01e000ffc030031 0x0d4f0e3838fc3033

def z1222 : W := mkw 0x0001c30802000002 0x9033200007264000 0x0001fffffffc0003 0x183f000007ffc000

def z1223 : W := mkw 0x0241f3de93b88482 0xb6b7fe00876ef348 0x0001ffffffff01c3 0x9c3ffe0007fff1c0

def z1224 : W := mkw 0x3490000000000003 0x403cdbeb68000000 0xfffe000000000002 0xe030fffff8000000

def z1225 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc000fff0fc000fc3 0x403f01f807fc0fc0

def z1226 : W := mkw 0x2490000000000002 0x003352c948000000 0xffe2000000000000 0x601137dfd8000000

def z1227 : W := mkw 0x3490000000000001 0x400cdb2368000000 0xfffe000000000003 0xe03ffffff8000000

def z1228 : W := mkw 0x0001e38e93900002 0x9437ac00076ef000 0x0001ffffffff0003 0x9c3fc80007fff000

def z1229 : W := mkw 0x2a41555002689482 0xb2b070c5c7034b4c 0x3f01fff003fcffce 0xf2a0c1870703cfcc

def z1230 : W := mkw 0x3490200401000003 0x403fdbeb68409000 0xfffefc00e01c0003 0xe03ffffffce1c000

def z1231 : W := mkw 0x2001f3ce93908002 0x9437fec1476ef240 0x3fe1ffffffffffc3 0xfe3fffc7c7ffffc0

def z1232 : W := mkw 0x19082c0521465229 0x400c892620c19c15 0x3f1dfffffffffe3f 0xffffc9a727fffe3f

def z1233 : W := mkw 0xaa401c614848fd81 0x498801fd40910ef4 0xc70000000000fff0 0x430001ff00000ff0

def z1234 : W := mkw 0x80019a694800e903 0x493b01f805b406f0 0xc000fffffc000ff1 0x093f01f807fc0ff0

def z1235 : W := mkw 0x2a41554002489482 0x00b050c545014a44 0x0700fff0001c0fc0 0x0030c1c70701cfc0

def z1236 : W := mkw 0x0001e38e93900000 0x9407ae00076ef000 0x0001ffffffff0003 0x9c1f3e0007fff000

def z1237 : W := mkw 0x0801451002601002 0xb23070048703490c 0x3fe1fff003fcffce 0xf2b0f1c7c703cfcc

def z1238 : W := mkw 0xea641c714c69fdd5 0x6b8801fdd0910ffe 0xfffe00000000fffc 0x63c001fff8000fff

def z1239 : W := mkw 0x3490000000000003 0x403fdbeb68000000 0xc7e2000000000003 0x803fffdfd8000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z7])],[(0,[z8,z0,z1,z3,z4,z5,z6]),(0,[z9,z0,z1,z3,z4,z5,z6]),(0,[z10,z0,z1,z3,z4,z5,z6])],[],[(0,[z0,z11,z1,z12,z3,z5,z6]),(0,[z0,z1,z3,z4,z13,z5,z6])],[(0,[z14,z1,z3,z4,z15,z5,z6]),(0,[z16,z0,z1,z3,z4,z5,z6]),(0,[z0,z17,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z18,z6]),(0,[z0,z1,z3,z4,z5,z6,z19])],[(0,[z20,z0,z1,z3,z4,z5,z6])],[(0,[z21,z0,z1,z3,z4,z5,z6]),(0,[z1,z22,z23,z3,z4,z5,z6])],[(0,[z0,z1,z24,z4,z25,z5,z6]),(0,[z0,z1,z3,z26,z5,z6,z27])]],
   [[(0,[z28,z0,z29,z1,z3,z5,z6]),(0,[z0,z30,z17,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z31,z6]),(0,[z0,z1,z3,z4,z5,z32,z6]),(0,[z33,z0,z1,z3,z4,z5,z6])],[],[(0,[z0,z1,z3,z34,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z35,z6]),(0,[z36,z0,z1,z3,z4,z5,z6])],[(0,[z37,z14,z1,z3,z4,z5,z6]),(0,[z38,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z0,z39,z1,z3,z4,z5,z6]),(0,[z0,z40,z1,z22,z4,z5,z6]),(0,[z0,z1,z41,z3,z4,z5,z6])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z42,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z43,z5,z6]),(0,[z0,z1,z3,z44,z4,z5,z6]),(0,[z45,z0,z1,z3,z4,z5,z46]),(0,[z0,z1,z3,z4,z5,z47,z6])],[(0,[z48,z0,z1,z3,z4,z5,z6]),(1,[z49,z1,z3,z50,z5,z6]),(0,[z0,z51,z52,z1,z4,z5,z6]),(0,[z0,z53,z1,z3,z4,z5,z6]),(0,[z0,z54,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z55,z4,z5,z6]),(1,[z36,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z56,z4,z5,z6]),(0,[z0,z1,z57,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z59,z6]),(0,[z0,z17,z3,z4,z26,z5,z6]),(0,[z0,z1,z12,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z60,z5,z6]),(0,[z0,z1,z3,z4,z61,z5,z6])],[(0,[z0,z1,z3,z4,z5,z62,z63]),(0,[z0,z1,z3,z4,z5,z6,z64]),(0,[z0,z1,z3,z4,z5,z65,z6]),(0,[z0,z66,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z67,z6]),(1,[z68,z0,z3,z4,z5,z63])],[(0,[z0,z1,z3,z4,z69,z5,z62])],[(0,[z0,z1,z3,z3,z4,z5,z6]),(1,[z0,z51,z4,z25,z5,z6]),(0,[z0,z1,z3,z4,z5,z70,z6])],[(0,[z0,z1,z3,z4,z5,z71,z6]),(0,[z0,z1,z3,z4,z72,z5,z6]),(0,[z73,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z74,z4,z5,z6])],[(0,[z49,z14,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z75,z4,z5,z6]),(0,[z21,z1,z3,z4,z5,z76,z6]),(0,[z68,z0,z1,z3,z4,z5,z27]),(0,[z0,z1,z3,z4,z5,z6,z77]),(0,[z0,z1,z3,z4,z5,z6,z78]),(0,[z0,z1,z3,z4,z5,z6,z79])],[(0,[z0,z1,z3,z4,z5,z80,z6]),(0,[z0,z1,z3,z4,z5,z81,z62])],[(0,[z0,z1,z3,z4,z5,z82,z6]),(0,[z0,z83,z1,z3,z4,z5,z6]),(0,[z0,z84,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z85,z6]),(0,[z0,z52,z11,z1,z4,z5,z6]),(0,[z0,z86,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z87,z6]),(1,[z0,z1,z3,z4,z5,z88]),(0,[z0,z89,z1,z4,z5,z90,z6]),(0,[z91,z0,z1,z3,z4,z5,z6]),(0,[z68,z0,z1,z3,z4,z5,z81]),(0,[z0,z92,z1,z3,z4,z5,z6]),(0,[z93,z0,z1,z3,z5,z6,z27])]],
   [[(0,[z0,z1,z3,z15,z5,z6,z27]),(0,[z0,z1,z3,z4,z5,z6,z94]),(0,[z0,z95,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z96,z6])],[(1,[z0,z1,z97,z3,z4,z5]),(0,[z0,z1,z3,z98,z4,z5,z6]),(0,[z99,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z76,z6]),(0,[z0,z100,z1,z3,z4,z5,z6]),(0,[z0,z101,z1,z3,z4,z5,z6]),(1,[z0,z29,z3,z26,z5,z6]),(0,[z102,z0,z1,z3,z4,z5,z6])],[(0,[z103,z0,z1,z3,z4,z5,z6]),(0,[z104,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z105,z5,z6]),(0,[z0,z1,z3,z4,z106,z5,z6])],[(0,[z107,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z108,z5,z6]),(0,[z0,z1,z22,z3,z4,z5,z6]),(0,[z109,z110,z1,z3,z4,z5,z6]),(0,[z111,z0,z1,z3,z4,z5,z6])],[(0,[z112,z0,z1,z113,z4,z5,z6]),(0,[z0,z1,z3,z4,z114,z5,z6]),(0,[z0,z1,z3,z115,z105,z5,z6]),(0,[z0,z1,z3,z116,z4,z5,z6]),(0,[z0,z1,z117,z3,z4,z5,z6])],[(0,[z118,z1,z3,z58,z4,z5,z6]),(1,[z0,z1,z3,z119,z5,z6]),(0,[z0,z1,z3,z4,z120,z5,z6]),(0,[z0,z1,z3,z4,z121,z5,z6]),(1,[z0,z1,z4,z5,z122,z6])],[(0,[z0,z1,z3,z4,z123,z5,z6]),(0,[z124,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z125]),(1,[z0,z1,z4,z5,z6,z126]),(0,[z0,z1,z3,z4,z5,z127,z6]),(0,[z0,z1,z3,z115,z4,z5,z128])]],
   [[(0,[z0,z1,z129,z3,z4,z5,z6]),(0,[z0,z130,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z131,z6]),(0,[z0,z1,z132,z3,z4,z5,z6]),(0,[z0,z1,z133,z3,z4,z5,z6]),(0,[z134,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z135,z24,z4,z5,z6]),(0,[z0,z1,z22,z3,z115,z5,z6])],[(0,[z136,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z137,z6]),(0,[z0,z1,z3,z4,z138,z5,z6]),(0,[z0,z1,z3,z4,z139,z5,z6]),(0,[z0,z1,z3,z50,z4,z5,z87]),(0,[z140,z0,z1,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z141,z6]),(0,[z0,z142,z1,z3,z4,z5,z6]),(0,[z143,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z144,z5,z6])],[(0,[z0,z1,z3,z4,z145,z5,z6]),(0,[z0,z1,z3,z4,z5,z146,z6]),(1,[z147,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z148,z5,z6]),(1,[z149,z1,z3,z4,z5,z6])],[(1,[z0,z1,z150,z4,z5,z6]),(0,[z0,z1,z24,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z151,z5,z6]),(0,[z0,z1,z152,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z153]),(0,[z0,z1,z3,z4,z5,z128,z154])],[(0,[z0,z155,z1,z3,z4,z5,z6]),(0,[z0,z1,z156,z3,z4,z5,z6]),(0,[z118,z49,z1,z3,z4,z5,z6]),(0,[z0,z157,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z5,z6]),(1,[z158,z1,z3,z4,z5,z6]),(1,[z28,z0,z1,z3,z159,z6])],[(0,[z160,z0,z1,z3,z4,z5,z6]),(0,[z0,z161,z1,z3,z4,z5,z6]),(0,[z0,z162,z1,z3,z4,z5,z6]),(0,[z0,z100,z1,z163,z3,z5,z6]),(0,[z164,z0,z1,z3,z165,z5,z6]),(0,[z0,z1,z3,z4,z5,z166,z6]),(0,[z0,z1,z3,z5,z167,z96,z6])],[(0,[z0,z1,z3,z115,z26,z5,z6]),(0,[z68,z0,z1,z3,z4,z69,z5]),(0,[z0,z168,z1,z3,z4,z5,z6]),(0,[z0,z1,z169,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z170,z5,z6]),(1,[z171,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z172,z5,z6]),(0,[z173,z1,z3,z4,z5,z90,z6]),(0,[z174,z175,z1,z3,z4,z5,z6]),(1,[z176,z1,z3,z4,z5,z6]),(0,[z0,z177,z1,z3,z4,z5,z6])]],
   [[(0,[z178,z1,z3,z4,z179,z5,z6]),(0,[z0,z1,z150,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z180,z5,z6]),(0,[z0,z1,z181,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z182]),(0,[z183,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z159,z6])],[(0,[z0,z1,z22,z3,z15,z5,z6]),(0,[z0,z11,z1,z3,z115,z5,z6]),(0,[z0,z1,z3,z4,z184,z5,z6]),(0,[z93,z0,z1,z3,z4,z5,z128]),(0,[z0,z1,z3,z4,z5,z6,z185])],[(0,[z0,z1,z3,z4,z186,z5,z6]),(0,[z0,z1,z3,z4,z5,z187,z6]),(0,[z0,z1,z3,z4,z5,z188,z6]),(1,[z1,z3,z4,z5,z6,z189])],[(0,[z49,z0,z1,z3,z4,z5,z6]),(0,[z0,z51,z1,z3,z4,z5,z6]),(0,[z190,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z191,z6]),(0,[z0,z1,z3,z4,z192,z5,z6]),(0,[z193,z0,z1,z3,z4,z5,z6]),(0,[z0,z194,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z167,z6]),(0,[z0,z1,z3,z4,z5,z195,z6]),(0,[z0,z1,z3,z4,z5,z6,z196]),(0,[z197,z0,z1,z3,z4,z5,z6]),(0,[z0,z198,z1,z3,z4,z5,z6])],[(0,[z199,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z22,z3,z200,z5,z6])],[(0,[z14,z1,z3,z4,z5,z76,z6]),(0,[z201,z0,z1,z3,z4,z5,z6]),(0,[z0,z202,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z203])],[(0,[z204,z0,z1,z3,z4,z5,z6]),(0,[z205,z1,z3,z4,z15,z5,z6]),(0,[z28,z0,z1,z3,z50,z5,z6]),(0,[z0,z100,z1,z4,z170,z5,z6]),(0,[z0,z1,z3,z4,z206,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z207]),(1,[z110,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z208,z4,z5,z6])],[(0,[z0,z1,z3,z165,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z209,z6]),(0,[z109,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z210,z3,z4,z5,z6]),(0,[z211,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z200,z105,z5,z6]),(0,[z36,z1,z3,z4,z69,z5,z6])]],
   [[(0,[z0,z29,z1,z3,z105,z5,z6]),(0,[z0,z1,z3,z4,z5,z212,z6]),(1,[z0,z1,z117,z4,z5,z6])],[(0,[z213,z0,z1,z214,z4,z5,z6]),(0,[z0,z1,z3,z15,z26,z5,z6]),(0,[z0,z1,z3,z4,z215,z5,z6]),(0,[z0,z1,z3,z4,z216,z5,z6]),(0,[z0,z1,z217,z3,z4,z5,z6]),(1,[z109,z0,z1,z4,z96,z6]),(0,[z0,z1,z3,z4,z5,z218,z6]),(0,[z0,z1,z3,z4,z69,z5,z6])],[(0,[z0,z1,z219,z3,z4,z5,z6]),(0,[z0,z1,z220,z3,z4,z5,z6]),(0,[z221,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z222,z4,z5,z6]),(1,[z0,z1,z4,z5,z223,z6])],[(0,[z37,z118,z1,z3,z4,z5,z6]),(0,[z164,z0,z3,z4,z5,z90,z6]),(0,[z224,z1,z3,z115,z4,z5,z6]),(0,[z0,z1,z3,z4,z69,z62,z6])],[(0,[z0,z1,z3,z4,z225,z5,z6]),(0,[z112,z1,z3,z4,z5,z226,z6]),(0,[z0,z1,z3,z4,z5,z6,z227]),(0,[z228,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z229,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z230,z5,z6]),(0,[z0,z1,z3,z4,z231,z5,z6])],[(0,[z0,z1,z214,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z232,z6]),(1,[z0,z1,z3,z4,z5,z233]),(0,[z109,z0,z1,z4,z5,z96,z6]),(0,[z234,z0,z1,z3,z4,z69,z6])],[(0,[z0,z1,z3,z4,z235,z5,z6]),(0,[z0,z1,z3,z4,z5,z236,z6]),(0,[z0,z1,z3,z4,z5,z6,z237]),(1,[z0,z1,z3,z5,z6,z238])]],
   [[(0,[z49,z0,z1,z3,z15,z5,z6]),(0,[z0,z239,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z200,z26,z5,z6]),(0,[z109,z240,z1,z3,z4,z5,z6])],[(0,[z0,z1,z241,z3,z4,z5,z6]),(0,[z49,z1,z3,z4,z5,z76,z6]),(0,[z0,z29,z1,z3,z26,z5,z6]),(0,[z234,z68,z0,z1,z3,z4,z5]),(1,[z0,z1,z3,z4,z5,z242]),(0,[z0,z1,z3,z4,z5,z243,z6])],[(0,[z0,z1,z244,z3,z4,z5,z6]),(0,[z245,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z246,z3,z4,z5,z6]),(0,[z174,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z247,z4,z5,z6])],[(0,[z0,z1,z3,z4,z248,z5,z6]),(0,[z147,z1,z135,z3,z4,z5,z6]),(0,[z249,z0,z1,z3,z4,z5,z6]),(0,[z250,z0,z1,z3,z4,z5,z6])],[(0,[z251,z0,z1,z3,z4,z5,z6]),(0,[z0,z142,z3,z4,z5,z81,z6]),(0,[z0,z1,z117,z4,z69,z5,z6])],[(0,[z0,z1,z214,z4,z5,z96,z6]),(0,[z109,z0,z51,z1,z4,z5,z6]),(0,[z109,z0,z1,z3,z4,z96,z6])],[(1,[z0,z1,z3,z252,z5,z6]),(0,[z253,z0,z1,z214,z4,z5,z6]),(0,[z254,z0,z1,z3,z4,z5,z6])],[(0,[z21,z0,z1,z3,z4,z5,z128]),(0,[z0,z51,z1,z4,z170,z5,z6]),(0,[z0,z1,z3,z4,z5,z255,z6]),(0,[z0,z1,z3,z256,z4,z5,z6]),(0,[z0,z1,z257,z3,z4,z5,z6]),(0,[z0,z1,z258,z3,z4,z5,z6])]],
   [[(0,[z201,z0,z1,z3,z58,z4,z5]),(0,[z259,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z260,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z261,z6]),(0,[z262,z0,z1,z3,z4,z5,z6])],[(0,[z263,z0,z1,z3,z4,z5,z6]),(0,[z174,z0,z1,z4,z5,z96,z6])],[(0,[z0,z1,z3,z4,z5,z6,z264]),(0,[z265,z0,z1,z3,z4,z5,z6])],[(0,[z205,z0,z1,z3,z50,z5,z6]),(0,[z266,z0,z1,z3,z4,z5,z6])],[(0,[z0,z267,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z50,z4,z5,z6]),(0,[z0,z1,z268,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z269,z6]),(0,[z0,z270,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z271,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z272]),(0,[z0,z1,z3,z105,z5,z159,z6])],[(0,[z0,z273,z1,z3,z4,z5,z6]),(0,[z0,z274,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z275]),(0,[z0,z1,z3,z4,z5,z276,z90]),(0,[z0,z52,z1,z3,z4,z5,z6]),(0,[z0,z277,z1,z3,z4,z5,z6])],[(0,[z278,z0,z1,z3,z4,z5,z6]),(0,[z213,z1,z3,z4,z5,z226,z6]),(0,[z164,z266,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z62,z128])],[(0,[z0,z1,z279,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z280,z6]),(0,[z0,z1,z281,z3,z4,z5,z6]),(1,[z0,z1,z12,z282,z5,z6]),(0,[z0,z1,z3,z4,z283,z5,z6]),(0,[z0,z284,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z285,z1,z3,z4,z5,z6]),(0,[z286,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z57,z3,z4,z5,z6])],[(0,[z287,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z22,z256,z4,z5,z6]),(0,[z0,z1,z12,z22,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z288]),(0,[z0,z1,z289,z3,z4,z5,z6]),(0,[z28,z0,z210,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z290,z5,z6]),(0,[z0,z1,z3,z4,z5,z291,z6]),(0,[z0,z1,z292,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z293,z6]),(0,[z174,z0,z1,z3,z4,z5,z294]),(0,[z0,z295,z1,z3,z4,z5,z6]),(0,[z296,z0,z1,z3,z4,z5,z6])],[(0,[z297,z0,z1,z3,z4,z5,z6]),(0,[z0,z298,z1,z3,z4,z5,z6]),(0,[z0,z299,z1,z3,z4,z5,z6]),(0,[z0,z1,z300,z3,z4,z5,z6])],[(0,[z14,z1,z241,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z81,z6,z63]),(0,[z0,z1,z3,z4,z5,z6,z242]),(0,[z0,z52,z1,z4,z5,z96,z6]),(0,[z0,z11,z1,z3,z5,z6,z27])],[(0,[z0,z1,z301,z3,z4,z5,z6]),(0,[z174,z0,z1,z3,z55,z5,z6])],[(0,[z0,z30,z22,z3,z4,z5,z6]),(0,[z0,z1,z4,z170,z5,z96,z6]),(0,[z0,z302,z1,z3,z4,z5,z6]),(0,[z28,z0,z1,z3,z4,z5,z303]),(0,[z0,z1,z3,z4,z5,z6,z27])],[(0,[z304,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z305,z3,z4,z5,z6]),(0,[z0,z1,z306,z3,z4,z5,z6]),(1,[z307,z1,z3,z4,z5,z6]),(0,[z308,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z309,z27])]],
   [[(0,[z0,z1,z12,z4,z282,z5,z6]),(0,[z310,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z311]),(1,[z1,z3,z4,z106,z5,z6])],[(0,[z0,z1,z3,z312,z4,z5,z6]),(0,[z313,z0,z1,z3,z4,z5,z6]),(0,[z0,z314,z1,z3,z4,z5,z6]),(0,[z0,z22,z3,z4,z26,z5,z6]),(0,[z0,z1,z3,z4,z315,z5,z6])],[(0,[z316,z0,z1,z3,z4,z5,z6]),(0,[z118,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z317,z6]),(0,[z0,z1,z3,z318,z4,z5,z6]),(0,[z0,z1,z3,z4,z319,z5,z6]),(1,[z224,z1,z3,z4,z5,z6]),(0,[z0,z1,z320,z3,z4,z5,z6]),(0,[z0,z321,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z322,z5,z6]),(0,[z0,z1,z3,z4,z323,z5,z6]),(0,[z45,z1,z3,z4,z15,z5,z6]),(0,[z324,z0,z1,z3,z4,z5,z6]),(0,[z325,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z326]),(0,[z28,z0,z30,z1,z3,z5,z6]),(0,[z0,z1,z327,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z328,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z45,z1,z3,z4,z5,z6,z46]),(0,[z0,z1,z3,z4,z5,z6,z329]),(0,[z0,z3,z4,z26,z5,z90,z6]),(0,[z330,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z55,z5,z6])],[(0,[z0,z331,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z332,z4,z5,z6]),(0,[z333,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z334,z5,z6]),(0,[z307,z1,z22,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z335]),(1,[z0,z210,z3,z4,z5,z6])],[(0,[z0,z1,z3,z336,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z337]),(1,[z174,z0,z1,z4,z5,z294]),(0,[z0,z1,z3,z4,z5,z338,z6])]],
   [[(1,[z205,z1,z3,z15,z5,z6]),(0,[z0,z1,z339,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z340,z6]),(0,[z0,z1,z57,z3,z4,z5,z294])],[(0,[z341,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z342,z6]),(0,[z49,z1,z3,z4,z5,z226,z6]),(0,[z0,z343,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z344,z6]),(0,[z0,z1,z3,z4,z5,z6,z345])],[(0,[z0,z1,z3,z4,z346,z5,z6]),(0,[z0,z142,z1,z3,z4,z5,z128]),(0,[z0,z1,z3,z4,z5,z347,z6])],[(0,[z348,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z349,z5,z6]),(1,[z0,z1,z3,z4,z5,z303])],[(0,[z1,z3,z58,z4,z5,z226,z6]),(0,[z0,z100,z1,z4,z282,z5,z6]),(0,[z164,z158,z1,z3,z4,z5,z6]),(1,[z0,z1,z244,z4,z5,z6]),(0,[z350,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z0,z1,z163,z3,z4,z5,z6]),(0,[z0,z100,z1,z4,z5,z309,z6]),(0,[z68,z0,z1,z3,z4,z5,z6]),(0,[z0,z351,z1,z3,z4,z5,z6]),(0,[z0,z1,z24,z3,z4,z5,z6])],[(0,[z205,z49,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z352,z6]),(0,[z1,z3,z50,z4,z15,z5,z6]),(0,[z0,z1,z353,z3,z4,z5,z6]),(1,[z0,z1,z3,z222,z5,z6]),(0,[z354,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z12,z3,z4,z5,z355]),(0,[z0,z1,z3,z4,z356,z5,z6]),(0,[z0,z1,z3,z4,z5,z357,z6]),(0,[z0,z358,z1,z3,z4,z5,z6])],[(0,[z174,z0,z1,z3,z4,z5,z309])]],
   [[(0,[z359,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z360,z6]),(0,[z0,z1,z3,z4,z5,z361,z6]),(0,[z118,z1,z3,z4,z5,z76,z6]),(0,[z362,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z22,z3,z5,z159,z6])],[(1,[z178,z241,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z363,z5,z6]),(1,[z0,z1,z3,z4,z5,z87]),(0,[z21,z0,z1,z3,z4,z5,z46])],[(0,[z112,z0,z1,z150,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z364]),(0,[z0,z100,z1,z135,z4,z5,z6]),(0,[z0,z1,z3,z4,z365,z5,z6]),(0,[z0,z366,z1,z3,z4,z5,z6])],[(0,[z49,z1,z3,z50,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z367])],[(0,[z0,z368,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z369,z5,z6]),(0,[z164,z0,z1,z3,z4,z5,z370]),(0,[z0,z1,z3,z4,z5,z6,z294]),(0,[z93,z0,z1,z3,z4,z5,z27]),(0,[z371,z0,z1,z3,z4,z5,z6])],[(0,[z253,z0,z1,z58,z4,z5,z6]),(0,[z37,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z372,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z373]),(0,[z147,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z374,z5,z6]),(0,[z0,z1,z4,z5,z96,z309,z6])],[(0,[z37,z178,z1,z3,z4,z5,z6]),(0,[z0,z375,z1,z3,z4,z5,z6]),(0,[z0,z142,z1,z3,z4,z5,z63]),(0,[z0,z1,z3,z4,z5,z6,z376])],[(0,[z377,z0,z1,z3,z4,z5,z6]),(0,[z378,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z63,z154]),(0,[z0,z11,z1,z4,z282,z5,z6])]],
   [[(0,[z379,z0,z1,z3,z4,z5,z6]),(0,[z45,z0,z1,z3,z4,z5,z27]),(0,[z380,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z381,z3,z4,z5,z6])],[(0,[z0,z1,z3,z382,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z276])],[(0,[z0,z1,z3,z4,z383,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z384]),(0,[z0,z1,z3,z385,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z126,z63]),(0,[z28,z0,z52,z1,z3,z5,z6]),(0,[z0,z1,z3,z105,z5,z6,z27])],[(0,[z253,z1,z3,z58,z4,z5,z6]),(0,[z386,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z387,z5,z6]),(0,[z0,z1,z24,z3,z4,z96,z6]),(0,[z0,z1,z3,z388,z4,z5,z6])],[(0,[z0,z1,z3,z389,z4,z5,z6]),(0,[z109,z0,z100,z1,z4,z5,z6]),(0,[z390,z0,z1,z3,z4,z5,z6]),(0,[z0,z391,z1,z3,z4,z5,z6])],[(0,[z0,z51,z1,z4,z282,z5,z6]),(1,[z1,z3,z4,z5,z6,z392]),(0,[z109,z0,z1,z24,z4,z5,z6]),(0,[z0,z1,z57,z3,z4,z5,z309]),(0,[z0,z1,z4,z69,z5,z122,z6])],[(0,[z393,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z394,z3,z4,z5,z6]),(0,[z0,z51,z1,z4,z5,z309,z6]),(1,[z0,z1,z256,z4,z5,z6]),(1,[z164,z0,z3,z4,z90,z6]),(0,[z0,z1,z3,z4,z5,z6,z303]),(1,[z1,z3,z4,z5,z243,z6])],[(0,[z0,z1,z3,z4,z395,z5,z6]),(0,[z0,z1,z3,z4,z69,z5,z154]),(0,[z0,z396,z1,z3,z4,z5,z6])]],
   [[(0,[z1,z135,z397,z3,z4,z5,z6]),(0,[z398,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z399]),(0,[z0,z100,z1,z3,z119,z5,z6]),(1,[z1,z397,z3,z4,z5,z6]),(1,[z0,z1,z3,z400,z5,z6]),(0,[z401,z0,z1,z3,z4,z5,z6]),(0,[z149,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z24,z4,z170,z5,z6]),(1,[z175,z1,z3,z4,z5,z6]),(0,[z0,z1,z402,z3,z4,z5,z6]),(0,[z0,z403,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z69,z5,z243,z6])],[(1,[z0,z1,z353,z4,z5,z6]),(0,[z0,z1,z404,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z405,z6]),(0,[z0,z1,z3,z4,z5,z6,z406])],[(0,[z0,z51,z1,z135,z4,z5,z6]),(0,[z149,z1,z12,z3,z4,z5,z6]),(0,[z407,z0,z1,z3,z4,z5,z6])],[(0,[z408,z0,z1,z3,z4,z5,z6]),(0,[z0,z409,z1,z3,z4,z5,z6]),(0,[z0,z1,z214,z24,z4,z5,z6]),(0,[z0,z1,z3,z4,z410,z5,z6]),(0,[z0,z1,z3,z411,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z412,z6]),(0,[z0,z1,z3,z4,z5,z6,z413])],[(0,[z0,z414,z1,z3,z4,z5,z6]),(0,[z0,z100,z1,z214,z4,z5,z6])],[(0,[z213,z1,z3,z4,z15,z5,z6]),(0,[z415,z0,z1,z3,z4,z5,z6]),(0,[z174,z0,z100,z1,z4,z5,z6]),(0,[z416,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z417,z6]),(0,[z0,z1,z418,z3,z4,z5,z6]),(0,[z68,z0,z1,z3,z34,z5,z6]),(0,[z28,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z419]),(0,[z164,z0,z17,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z81,z6]),(0,[z174,z0,z1,z24,z4,z5,z6])],[(0,[z0,z1,z3,z4,z420,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z421]),(0,[z0,z1,z3,z4,z5,z422,z6]),(0,[z0,z1,z3,z423,z4,z5,z6])],[(0,[z1,z214,z3,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z424,z5,z6]),(0,[z0,z1,z3,z4,z5,z425,z6]),(0,[z0,z426,z1,z3,z4,z5,z6]),(0,[z28,z0,z1,z3,z115,z5,z6])],[(0,[z0,z1,z3,z4,z5,z427,z6]),(0,[z0,z1,z428,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z429,z6]),(0,[z430,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z431,z5,z6]),(0,[z0,z1,z3,z432,z4,z5,z6])],[(0,[z178,z1,z3,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z226,z6]),(0,[z0,z29,z3,z4,z26,z5,z6]),(0,[z0,z1,z3,z4,z5,z433,z6]),(0,[z0,z434,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z435,z4,z5,z6]),(1,[z37,z1,z3,z4,z226,z6]),(0,[z0,z1,z3,z4,z119,z5,z6]),(0,[z1,z3,z4,z5,z6,z189,z294]),(0,[z0,z1,z3,z4,z5,z436,z6])],[(0,[z118,z1,z241,z3,z4,z5,z6]),(0,[z437,z0,z1,z3,z4,z5,z6]),(0,[z438,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z52,z1,z22,z3,z5,z6]),(0,[z234,z0,z142,z1,z3,z4,z5]),(0,[z439,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z440,z5,z6]),(0,[z0,z1,z58,z4,z5,z96,z6]),(0,[z0,z1,z3,z4,z5,z441,z6]),(1,[z0,z1,z318,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z442]),(0,[z0,z1,z3,z4,z5,z62,z27])],[(0,[z0,z52,z100,z1,z4,z5,z6]),(0,[z0,z1,z3,z5,z443,z90,z6]),(0,[z1,z12,z381,z3,z4,z5,z6])],[(0,[z178,z49,z1,z3,z4,z5,z6]),(0,[z45,z49,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z179,z5,z6]),(0,[z45,z0,z1,z57,z3,z4,z5]),(0,[z0,z1,z41,z3,z5,z96,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z28,z0,z1,z3,z15,z5,z6]),(1,[z234,z0,z1,z3,z4,z154])],[(0,[z213,z253,z1,z3,z4,z5,z6]),(0,[z444,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z445]),(0,[z164,z0,z1,z3,z4,z90,z6]),(0,[z446,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z447,z3,z4,z5,z6])],[(0,[z0,z1,z214,z57,z4,z5,z6]),(1,[z0,z1,z75,z4,z5,z6]),(0,[z0,z1,z22,z3,z5,z6,z27]),(0,[z0,z1,z3,z448,z4,z5,z6])],[(0,[z0,z51,z1,z214,z4,z5,z6]),(0,[z45,z0,z1,z3,z4,z5,z76]),(0,[z0,z30,z1,z22,z3,z5,z6]),(1,[z449,z0,z1,z3,z4,z5])]],
   [[(0,[z0,z1,z214,z4,z5,z6,z294]),(0,[z450,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z451]),(0,[z0,z1,z12,z3,z105,z5,z6]),(0,[z0,z1,z3,z452,z4,z5,z6]),(0,[z0,z1,z3,z4,z453,z5,z6]),(0,[z0,z1,z3,z4,z62,z6,z154])],[(0,[z0,z1,z3,z4,z5,z454,z6]),(0,[z455,z0,z1,z3,z4,z5,z6]),(0,[z307,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z456,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z457,z5,z6]),(0,[z0,z1,z3,z4,z458,z5,z6]),(1,[z0,z1,z3,z5,z443,z6]),(0,[z0,z1,z459,z3,z4,z5,z6]),(0,[z174,z0,z1,z57,z4,z5,z6]),(0,[z234,z0,z1,z3,z4,z6,z154])],[(0,[z0,z1,z3,z4,z460,z5,z6]),(0,[z45,z0,z1,z3,z222,z5,z6]),(0,[z174,z0,z51,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z461,z5,z6]),(0,[z0,z462,z1,z3,z4,z5,z6]),(0,[z0,z1,z57,z4,z5,z309,z6]),(0,[z0,z1,z3,z463,z4,z5,z6])],[(0,[z178,z112,z1,z3,z4,z5,z6]),(0,[z178,z0,z14,z3,z4,z5,z6]),(0,[z0,z464,z1,z3,z4,z5,z6]),(0,[z205,z0,z1,z3,z4,z5,z6]),(0,[z174,z0,z1,z4,z5,z6,z294])],[(0,[z0,z465,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z15,z5,z76,z6]),(0,[z0,z1,z3,z466,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z467,z6]),(1,[z240,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z468,z5,z6]),(0,[z21,z174,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z469,z6]),(0,[z0,z1,z3,z4,z5,z6,z470]),(0,[z0,z471,z1,z3,z5,z90,z6]),(0,[z0,z1,z472,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z473])],[(0,[z474,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z475,z6]),(0,[z476,z0,z1,z3,z4,z5,z6]),(0,[z0,z477,z1,z3,z4,z5,z6]),(1,[z0,z1,z163,z3,z5,z6]),(0,[z0,z30,z1,z3,z4,z5,z6]),(0,[z478,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z479])],[(0,[z0,z1,z3,z4,z480,z5,z6]),(0,[z0,z1,z3,z4,z481,z5,z6]),(0,[z0,z1,z12,z3,z26,z5,z6]),(0,[z0,z1,z3,z4,z5,z90,z6]),(0,[z0,z1,z3,z4,z5,z482,z6]),(1,[z0,z1,z3,z4,z5,z355]),(0,[z240,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z483,z6]),(0,[z164,z0,z1,z3,z4,z5,z88]),(0,[z176,z0,z1,z3,z4,z5,z6]),(1,[z0,z299,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z154])],[(0,[z0,z1,z3,z4,z5,z484,z6]),(0,[z37,z1,z3,z4,z5,z226,z6]),(0,[z485,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z486,z5,z6]),(0,[z0,z1,z3,z4,z487,z5,z6]),(0,[z28,z0,z1,z3,z4,z159,z6])],[(0,[z0,z1,z3,z4,z5,z276,z6])],[(0,[z488,z0,z1,z3,z4,z5,z6]),(0,[z178,z1,z3,z4,z15,z5,z6]),(0,[z14,z1,z3,z4,z179,z5,z6]),(0,[z489,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z490]),(0,[z491,z0,z1,z3,z4,z5,z6]),(0,[z28,z198,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z492,z6])],[(0,[z37,z0,z1,z268,z4,z5,z6]),(0,[z0,z1,z3,z4,z282,z5,z6]),(1,[z93,z0,z1,z3,z5,z27]),(0,[z493,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z238])]],
   [[(0,[z45,z1,z214,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z494]),(0,[z0,z89,z1,z3,z4,z5,z6]),(0,[z0,z52,z1,z12,z4,z5,z6]),(0,[z28,z0,z1,z12,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z309,z6])],[(0,[z205,z0,z1,z3,z15,z5,z6]),(0,[z0,z1,z495,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z226,z76,z6]),(0,[z21,z0,z1,z3,z4,z5,z76]),(0,[z1,z3,z4,z5,z6,z392,z63]),(0,[z0,z1,z3,z4,z5,z6,z63]),(0,[z0,z1,z3,z115,z282,z5,z6])],[(0,[z0,z1,z3,z4,z496,z5,z6]),(0,[z45,z14,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z497,z6]),(0,[z171,z174,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z498,z6]),(0,[z213,z0,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z108,z4,z5,z6]),(0,[z499,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z500,z3,z4,z5,z6])],[(0,[z174,z0,z1,z3,z13,z5,z6]),(0,[z28,z501,z1,z3,z4,z5,z6]),(0,[z224,z0,z1,z3,z4,z5,z6])],[(0,[z0,z100,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z115,z50,z5,z6]),(1,[z1,z381,z3,z4,z5,z6]),(0,[z109,z0,z1,z3,z4,z170,z6]),(0,[z0,z1,z3,z115,z4,z5,z27]),(0,[z0,z1,z3,z411,z5,z62,z6])],[(0,[z112,z0,z14,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z502,z6]),(0,[z0,z503,z1,z3,z4,z5,z6]),(0,[z0,z471,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z34,z5,z6]),(0,[z0,z1,z3,z4,z504,z5,z6])],[(0,[z112,z0,z241,z3,z4,z5,z6]),(0,[z45,z0,z1,z353,z4,z5,z6]),(0,[z0,z100,z135,z3,z4,z5,z6]),(0,[z0,z1,z24,z4,z282,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z505,z5,z6]),(0,[z0,z1,z24,z4,z5,z309,z6]),(0,[z506,z0,z1,z3,z4,z5,z6]),(0,[z0,z507,z1,z3,z4,z5,z6]),(0,[z234,z0,z1,z3,z4,z5,z62])],[],[(0,[z0,z30,z29,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z508]),(0,[z173,z0,z1,z3,z4,z5,z6]),(0,[z68,z0,z1,z3,z4,z5,z63]),(0,[z0,z1,z3,z4,z5,z509,z6]),(0,[z510,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z511,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z512,z6]),(0,[z0,z1,z4,z5,z223,z90,z6]),(1,[z0,z1,z3,z13,z5,z6]),(1,[z198,z1,z3,z4,z5,z6])],[(0,[z0,z513,z1,z3,z4,z5,z6]),(0,[z0,z514,z1,z3,z4,z5,z6])],[(0,[z0,z515,z1,z3,z4,z5,z6]),(0,[z516,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z517])],[(0,[z68,z0,z1,z3,z518,z5,z6]),(1,[z333,z1,z3,z4,z5,z6])],[(0,[z519,z0,z1,z3,z4,z5,z6]),(0,[z213,z49,z1,z3,z4,z5,z6]),(0,[z0,z520,z1,z3,z4,z5,z6]),(0,[z521,z0,z1,z3,z4,z5,z6]),(1,[z0,z40,z1,z4,z5,z6])]],
   [[(0,[z0,z522,z1,z3,z4,z5,z6]),(0,[z0,z523,z1,z3,z4,z5,z6])],[(0,[z0,z1,z97,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z141,z6]),(1,[z501,z1,z3,z4,z5,z6])],[(0,[z0,z524,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z525]),(1,[z0,z1,z3,z165,z5,z6]),(0,[z0,z1,z3,z4,z5,z526,z6])],[(0,[z0,z1,z3,z4,z527,z5,z6]),(0,[z528,z0,z1,z3,z4,z5,z6])],[(0,[z112,z14,z1,z3,z4,z5,z6]),(0,[z0,z158,z1,z3,z4,z5,z6]),(0,[z0,z1,z529,z3,z4,z5,z6]),(0,[z530,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z122,z6])],[(0,[z1,z3,z4,z15,z5,z226,z6]),(0,[z531,z0,z1,z3,z4,z5,z6]),(0,[z0,z168,z1,z4,z5,z6,z63]),(0,[z28,z0,z1,z3,z4,z105,z6]),(0,[z93,z0,z1,z3,z4,z5,z6]),(0,[z0,z532,z1,z3,z4,z5,z6])],[(0,[z178,z0,z1,z3,z252,z5,z6]),(0,[z0,z1,z3,z50,z5,z6,z27]),(0,[z0,z533,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z534,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z535])],[(0,[z0,z1,z3,z113,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z536,z6]),(0,[z537,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z538]),(0,[z0,z1,z3,z4,z5,z539,z6])]],
   [[(0,[z0,z540,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z541,z5,z6]),(0,[z45,z0,z1,z3,z4,z5,z6]),(0,[z93,z0,z1,z3,z115,z5,z6])],[(1,[z0,z89,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z189]),(0,[z0,z542,z1,z3,z4,z5,z6])],[(0,[z45,z0,z1,z75,z4,z5,z6]),(1,[z0,z1,z3,z72,z5,z6]),(0,[z0,z1,z3,z543,z4,z5,z6]),(0,[z0,z1,z544,z3,z4,z5,z6]),(0,[z545,z0,z1,z3,z4,z5,z6]),(0,[z546,z0,z1,z3,z4,z5,z6])],[(0,[z547,z0,z1,z3,z4,z5,z6]),(0,[z0,z548,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z549,z6]),(0,[z0,z1,z3,z4,z5,z550,z6])],[(0,[z0,z1,z3,z4,z5,z551,z6]),(0,[z0,z1,z4,z282,z5,z96,z6]),(0,[z0,z1,z3,z4,z5,z552,z6]),(0,[z0,z1,z3,z200,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z553,z6]),(1,[z0,z1,z268,z4,z5,z6]),(0,[z0,z29,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z81,z154]),(0,[z0,z554,z1,z3,z4,z5,z6]),(0,[z171,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z555])],[(0,[z0,z1,z3,z4,z5,z6,z556]),(0,[z0,z1,z3,z557,z4,z5,z6])]],
   [[(0,[z558,z0,z1,z3,z4,z5,z6]),(0,[z118,z0,z1,z3,z290,z5,z6]),(0,[z0,z51,z100,z3,z4,z5,z6]),(0,[z0,z1,z3,z559,z4,z5,z6])],[(0,[z0,z1,z560,z3,z4,z5,z6])],[(0,[z561,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z562,z3,z4,z5,z6]),(0,[z0,z563,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z564,z5,z6]),(1,[z0,z1,z463,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z565]),(0,[z0,z1,z3,z4,z5,z6,z566])],[(0,[z213,z1,z3,z4,z5,z6,z46]),(0,[z0,z567,z1,z3,z4,z5,z6]),(1,[z173,z1,z3,z4,z5,z6]),(0,[z0,z1,z568,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z569,z5,z6]),(0,[z28,z0,z1,z3,z5,z159,z6]),(0,[z0,z1,z3,z4,z5,z6,z570])],[(0,[z0,z1,z97,z3,z58,z4,z5]),(0,[z0,z1,z3,z4,z5,z571,z6]),(0,[z449,z0,z1,z3,z4,z5,z90])],[(0,[z0,z1,z3,z4,z5,z6,z572]),(0,[z0,z573,z1,z3,z4,z5,z6]),(0,[z1,z214,z3,z4,z5,z76,z6]),(0,[z0,z574,z1,z3,z4,z5,z6]),(0,[z21,z0,z1,z3,z4,z5,z27])],[(0,[z213,z14,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z50,z105,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z575]),(0,[z576,z0,z1,z3,z4,z5,z6])],[(0,[z178,z1,z3,z4,z5,z76,z6]),(0,[z0,z1,z577,z3,z4,z5,z6]),(0,[z0,z52,z1,z3,z105,z5,z6]),(0,[z0,z1,z578,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z579,z6]),(0,[z0,z1,z23,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z223,z6]),(0,[z0,z1,z580,z3,z4,z5,z6]),(0,[z0,z1,z3,z581,z4,z5,z6]),(0,[z234,z0,z1,z3,z4,z5,z6])],[(0,[z582,z0,z1,z3,z4,z5,z6]),(0,[z0,z583,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z271,z5,z90,z6]),(1,[z0,z168,z1,z4,z5,z6]),(0,[z0,z584,z1,z3,z4,z5,z6]),(0,[z0,z1,z12,z3,z282,z5,z6]),(0,[z28,z0,z1,z472,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z585,z6])],[(0,[z586,z0,z1,z3,z4,z5,z6]),(0,[z45,z118,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z587,z5,z6]),(0,[z0,z1,z588,z3,z4,z5,z6]),(0,[z0,z1,z589,z3,z4,z5,z6])],[(0,[z112,z0,z1,z3,z4,z5,z6]),(0,[z0,z30,z3,z4,z5,z90,z6]),(0,[z0,z1,z12,z3,z4,z5,z242])],[(0,[z118,z0,z1,z3,z4,z226,z6]),(0,[z0,z100,z1,z4,z25,z5,z6]),(0,[z0,z590,z1,z3,z4,z5,z6])],[(0,[z0,z1,z591,z3,z4,z5,z6])],[(0,[z592,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z593,z5,z6]),(0,[z0,z30,z1,z3,z105,z5,z6]),(0,[z0,z1,z3,z4,z594,z5,z6]),(0,[z0,z52,z1,z24,z4,z5,z6]),(0,[z595,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z50,z26,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z596]),(0,[z0,z1,z3,z4,z597,z5,z6]),(0,[z0,z1,z3,z4,z5,z27,z154])]],
   [[(0,[z0,z1,z3,z598,z4,z5,z6]),(0,[z174,z45,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z599]),(0,[z0,z52,z1,z3,z26,z5,z6]),(0,[z0,z1,z22,z3,z4,z5,z7]),(0,[z28,z0,z299,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z600,z6]),(0,[z0,z601,z1,z3,z4,z5,z6]),(0,[z118,z1,z3,z4,z179,z5,z6]),(1,[z45,z1,z3,z4,z5,z46]),(0,[z0,z1,z3,z4,z602,z5,z6]),(0,[z449,z0,z1,z3,z4,z5,z6])],[(0,[z28,z0,z1,z3,z200,z5,z6]),(0,[z0,z1,z3,z4,z5,z62,z6])],[(1,[z266,z1,z3,z4,z5,z6]),(0,[z0,z1,z603,z3,z4,z5,z6]),(1,[z0,z1,z3,z5,z167,z6]),(0,[z0,z1,z24,z3,z4,z170,z6]),(0,[z28,z0,z1,z3,z4,z5,z218]),(0,[z1,z3,z115,z4,z106,z5,z6]),(0,[z0,z1,z3,z4,z604,z5,z6])],[(0,[z253,z45,z1,z3,z4,z5,z6]),(0,[z0,z1,z58,z4,z5,z6,z294]),(0,[z0,z605,z1,z3,z4,z5,z6])],[(0,[z0,z51,z3,z4,z25,z5,z6]),(0,[z0,z1,z3,z4,z606,z5,z6]),(0,[z0,z1,z607,z3,z4,z5,z6]),(0,[z0,z17,z1,z3,z4,z90,z6]),(1,[z0,z1,z3,z518,z5,z6]),(0,[z608,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z609])],[(0,[z0,z1,z3,z4,z5,z6,z610]),(0,[z611,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z22,z3,z4,z5,z233]),(0,[z0,z1,z3,z4,z5,z6,z612]),(1,[z0,z1,z472,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z613])],[(0,[z0,z1,z3,z4,z614,z5,z6]),(0,[z0,z30,z1,z3,z26,z5,z6]),(0,[z615,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z616])]],
   [[(0,[z178,z0,z241,z3,z4,z5,z6]),(0,[z1,z3,z58,z4,z15,z5,z6])],[(0,[z0,z1,z3,z252,z4,z5,z6]),(0,[z1,z3,z58,z4,z5,z6,z46]),(0,[z0,z1,z3,z617,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z618,z6]),(0,[z0,z1,z619,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z400,z5,z6]),(0,[z0,z1,z3,z4,z5,z309,z128])],[(0,[z620,z0,z1,z3,z4,z5,z6]),(0,[z21,z1,z3,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z621]),(0,[z0,z1,z3,z4,z5,z622,z6]),(0,[z0,z1,z3,z200,z4,z159,z6])],[(0,[z0,z623,z1,z3,z4,z5,z6]),(0,[z0,z1,z22,z3,z50,z5,z6])],[(0,[z112,z118,z1,z3,z4,z5,z6]),(0,[z0,z1,z624,z3,z4,z5,z6]),(0,[z0,z1,z625,z3,z4,z5,z6]),(0,[z164,z0,z1,z3,z4,z271,z6])],[(0,[z213,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z626,z6]),(0,[z0,z51,z1,z4,z25,z5,z6])],[(0,[z0,z1,z3,z4,z5,z627,z6]),(0,[z0,z1,z3,z628,z4,z5,z6]),(0,[z0,z1,z3,z4,z629,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z630])],[(0,[z37,z0,z1,z3,z4,z226,z6]),(0,[z0,z1,z631,z3,z4,z5,z6]),(0,[z0,z135,z3,z4,z25,z5,z6]),(0,[z164,z0,z1,z244,z4,z5,z6])]],
   [[(0,[z1,z241,z3,z4,z5,z226,z6]),(0,[z0,z1,z3,z58,z4,z5,z6]),(0,[z37,z0,z1,z598,z4,z5,z6]),(0,[z21,z0,z1,z57,z3,z4,z5]),(0,[z0,z142,z1,z3,z4,z5,z27]),(0,[z632,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z218]),(0,[z633,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z62,z6,z238])],[(0,[z634,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z635,z5,z6]),(0,[z636,z0,z1,z3,z4,z5,z6]),(0,[z0,z17,z1,z3,z4,z271,z6]),(0,[z68,z0,z1,z3,z4,z5,z128])],[(0,[z0,z1,z637,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z638,z6]),(0,[z0,z1,z3,z4,z639,z5,z6])],[(0,[z118,z0,z1,z3,z4,z179,z6]),(0,[z1,z3,z4,z5,z76,z6,z46]),(0,[z0,z640,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z641,z6]),(0,[z0,z142,z1,z3,z4,z5,z81]),(1,[z0,z1,z41,z3,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z642]),(0,[z0,z1,z3,z643,z4,z5,z6]),(0,[z68,z0,z3,z4,z5,z6,z63]),(0,[z0,z1,z4,z5,z309,z6,z294]),(0,[z0,z1,z3,z4,z5,z644,z6])],[(0,[z178,z213,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z645,z6]),(0,[z0,z1,z646,z3,z4,z5,z6]),(0,[z0,z647,z1,z3,z4,z5,z6]),(0,[z648,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z649,z6])],[(0,[z178,z1,z241,z3,z4,z5,z6]),(0,[z178,z45,z1,z3,z4,z5,z6]),(1,[z0,z1,z113,z4,z5,z6]),(0,[z0,z650,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z651,z5,z6]),(0,[z0,z652,z1,z3,z4,z5,z6]),(0,[z653,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z654]),(0,[z45,z1,z3,z4,z5,z226,z6]),(0,[z0,z1,z4,z25,z5,z96,z6])]],
   [[(0,[z45,z0,z1,z3,z72,z5,z6]),(0,[z0,z1,z3,z4,z5,z355,z6])],[(0,[z0,z1,z3,z4,z440,z5,z6]),(0,[z0,z1,z3,z26,z5,z159,z6]),(0,[z0,z40,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z655,z5,z6]),(0,[z28,z0,z1,z3,z5,z6,z27]),(0,[z0,z1,z656,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z657,z5,z6])],[(0,[z253,z0,z1,z3,z4,z5,z6]),(0,[z49,z0,z1,z3,z50,z5,z6]),(0,[z0,z1,z135,z3,z4,z5,z6]),(0,[z0,z658,z1,z3,z4,z5,z6]),(0,[z333,z1,z3,z4,z5,z6,z63]),(0,[z0,z11,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z659]),(0,[z0,z1,z3,z4,z660,z5,z6])],[(0,[z661,z0,z1,z3,z4,z5,z6])],[(0,[z662,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z0,z52,z11,z1,z3,z5,z6]),(0,[z0,z1,z3,z663,z4,z5,z6])],[(0,[z0,z1,z3,z15,z105,z5,z6]),(0,[z0,z1,z3,z4,z5,z128,z6])],[(0,[z213,z118,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z664]),(0,[z0,z665,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z115,z4,z5,z6])],[(0,[z666,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z88]),(1,[z0,z471,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z667]),(0,[z0,z1,z3,z5,z128,z6,z27]),(0,[z0,z1,z3,z115,z5,z128,z6])]],
   [[(0,[z668,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z50,z4,z5,z182])],[(0,[z0,z669,z1,z3,z4,z5,z6]),(0,[z0,z1,z135,z4,z5,z96,z6]),(1,[z0,z1,z3,z4,z5,z370])],[(0,[z0,z1,z3,z4,z670,z5,z6]),(1,[z0,z1,z3,z290,z5,z6]),(0,[z118,z0,z1,z3,z108,z5,z6]),(0,[z45,z0,z1,z3,z4,z5,z128]),(0,[z0,z1,z671,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z370,z6]),(0,[z0,z1,z3,z4,z5,z443,z6]),(0,[z0,z1,z3,z4,z518,z5,z6]),(0,[z0,z142,z1,z3,z4,z69,z5]),(0,[z176,z1,z3,z4,z5,z6,z294])],[(0,[z0,z672,z1,z3,z4,z5,z6]),(0,[z14,z1,z3,z58,z4,z5,z6]),(0,[z673,z0,z1,z3,z4,z5,z6]),(0,[z0,z674,z1,z3,z4,z5,z6]),(0,[z0,z17,z3,z4,z271,z5,z6]),(0,[z68,z0,z142,z3,z4,z5,z6]),(0,[z0,z1,z3,z200,z4,z105,z6])],[(0,[z164,z0,z1,z3,z400,z5,z6])],[(0,[z1,z3,z4,z179,z5,z226,z6]),(1,[z0,z1,z3,z4,z5,z7])],[(0,[z0,z675,z1,z3,z4,z5,z6]),(0,[z37,z0,z1,z3,z4,z179,z6]),(0,[z676,z0,z1,z3,z4,z5,z6])],[(0,[z21,z213,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z294,z27])]],
   [[(0,[z677,z0,z1,z3,z4,z5,z6]),(0,[z253,z1,z3,z4,z5,z76,z6]),(0,[z21,z45,z1,z3,z4,z5,z6]),(0,[z678,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z126]),(0,[z0,z1,z3,z4,z5,z679,z6]),(0,[z28,z0,z1,z463,z4,z5,z6]),(0,[z0,z1,z680,z3,z4,z5,z6])],[(0,[z178,z0,z1,z3,z440,z5,z6]),(0,[z0,z51,z1,z58,z4,z5,z6]),(0,[z681,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z15,z5,z6]),(0,[z0,z1,z3,z4,z5,z682,z6]),(0,[z683,z0,z1,z3,z4,z5,z6]),(0,[z0,z29,z1,z22,z3,z5,z6]),(0,[z0,z1,z3,z4,z684,z5,z6]),(0,[z0,z1,z685,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z46])],[(0,[z686,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z115,z15,z5,z6])],[(0,[z178,z0,z1,z3,z4,z5,z6]),(0,[z118,z1,z3,z4,z15,z5,z6])],[(0,[z0,z14,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z687]),(0,[z0,z1,z3,z4,z5,z688,z6]),(1,[z1,z23,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z689,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z392]),(0,[z0,z1,z3,z4,z5,z690,z6]),(0,[z0,z1,z3,z4,z5,z128,z294]),(0,[z501,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z411,z5,z6])],[(0,[z1,z3,z4,z5,z141,z90,z6])],[(0,[z49,z1,z3,z58,z4,z5,z6]),(1,[z0,z1,z598,z4,z5,z6]),(0,[z0,z691,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z692,z6]),(0,[z0,z693,z1,z3,z4,z5,z6])]],
   [[(0,[z694,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z695,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z182]),(0,[z0,z1,z3,z696,z4,z5,z6]),(0,[z0,z52,z1,z3,z282,z5,z6])],[(0,[z697,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z397,z3,z4,z5,z6]),(0,[z0,z110,z1,z3,z4,z5,z6]),(0,[z0,z175,z1,z3,z4,z5,z6])],[(1,[z253,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z233,z6])],[(0,[z0,z1,z3,z4,z5,z698,z6]),(0,[z0,z1,z3,z282,z5,z6,z27])],[(0,[z0,z1,z3,z4,z699,z5,z6]),(0,[z0,z1,z700,z3,z4,z5,z6]),(0,[z164,z0,z1,z318,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z701])],[(0,[z702,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z703,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z704,z5,z6]),(0,[z0,z705,z1,z3,z4,z5,z6])],[(0,[z234,z0,z1,z3,z4,z5,z154])],[(1,[z201,z0,z1,z3,z4,z5]),(0,[z213,z1,z214,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z706,z6]),(0,[z0,z1,z3,z4,z25,z5,z6]),(0,[z164,z0,z1,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z3,z108,z5,z6]),(0,[z198,z1,z463,z4,z5,z6])],[(0,[z0,z1,z3,z707,z5,z6])],[(0,[z677,z1,z3,z4,z226,z6]),(0,[z0,z1,z3,z119,z5,z6]),(0,[z0,z1,z3,z4,z5,z708]),(0,[z1,z709,z3,z4,z5,z6]),(0,[z471,z1,z3,z5,z141,z6]),(0,[z0,z1,z3,z5,z710,z6]),(0,[z0,z1,z41,z3,z5,z6]),(0,[z0,z1,z4,z5,z122,z6])],[(0,[z0,z1,z3,z4,z5,z711]),(0,[z0,z51,z4,z43,z5,z6]),(0,[z21,z0,z1,z3,z13,z5]),(0,[z0,z1,z4,z5,z6,z126]),(0,[z0,z299,z472,z4,z5,z6])],[(0,[z1,z3,z108,z15,z5,z6]),(0,[z0,z1,z4,z5,z6,z712]),(0,[z0,z51,z404,z4,z5,z6]),(0,[z1,z381,z3,z26,z5,z6]),(0,[z713,z1,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z141,z6]),(0,[z21,z201,z1,z3,z4,z5]),(0,[z0,z30,z471,z3,z5,z6]),(0,[z158,z1,z318,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z714]),(0,[z0,z1,z715,z4,z5,z6]),(0,[z176,z1,z3,z4,z5,z27]),(0,[z0,z716,z3,z4,z5,z6])],[(0,[z178,z1,z113,z4,z5,z6]),(0,[z147,z1,z3,z4,z5,z6]),(0,[z149,z1,z3,z4,z5,z6]),(0,[z253,z201,z1,z3,z4,z5]),(0,[z1,z23,z256,z4,z5,z6]),(0,[z0,z1,z3,z4,z717,z6]),(0,[z718,z1,z3,z4,z5,z6]),(0,[z501,z1,z463,z4,z5,z6]),(0,[z0,z1,z472,z4,z5,z218])],[(0,[z1,z3,z4,z5,z719,z6]),(0,[z0,z1,z3,z720,z5,z6]),(0,[z0,z1,z3,z4,z5,z721]),(0,[z0,z1,z5,z443,z223,z6])]],
   [[(0,[z158,z1,z3,z4,z5,z6]),(0,[z0,z1,z722,z3,z5,z6]),(0,[z723,z1,z3,z4,z5,z6]),(0,[z0,z1,z24,z13,z5,z6])],[(0,[z201,z14,z1,z3,z4,z5]),(0,[z1,z724,z3,z4,z5,z6])],[(0,[z171,z1,z3,z4,z5,z6]),(0,[z0,z1,z725,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z726]),(0,[z727,z1,z3,z4,z5,z6]),(0,[z728,z1,z3,z4,z5,z6])],[(0,[z176,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z729]),(0,[z0,z1,z3,z4,z5,z730]),(0,[z0,z1,z731,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z182]),(0,[z45,z175,z1,z3,z4,z5]),(0,[z732,z1,z3,z4,z5,z6]),(0,[z611,z0,z1,z3,z5,z27]),(0,[z1,z733,z3,z4,z5,z6]),(0,[z164,z158,z3,z4,z90,z6]),(0,[z0,z734,z1,z4,z5,z6]),(0,[z149,z1,z12,z282,z5,z6]),(0,[z735,z1,z3,z4,z5,z6])],[(0,[z393,z0,z1,z4,z96,z6]),(0,[z0,z161,z3,z26,z5,z6]),(0,[z176,z1,z75,z4,z5,z6]),(0,[z736,z1,z3,z4,z5,z6]),(0,[z737,z1,z3,z4,z5,z6]),(0,[z0,z1,z318,z4,z5,z370]),(0,[z0,z299,z3,z4,z5,z218]),(0,[z0,z1,z738,z4,z5,z6])],[(0,[z0,z1,z739,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z189])],[(0,[z0,z1,z3,z4,z5,z740]),(0,[z0,z1,z3,z741,z5,z6])]],
   [[(1,[z1,z3,z742,z5,z6]),(0,[z224,z1,z3,z222,z5,z6]),(0,[z0,z1,z3,z4,z5,z370]),(0,[z173,z89,z1,z4,z5,z6])],[(0,[z0,z743,z1,z4,z5,z6]),(0,[z0,z744,z1,z4,z5,z6])],[(0,[z1,z3,z440,z5,z76,z6]),(0,[z0,z1,z3,z745,z5,z6]),(0,[z0,z746,z1,z4,z5,z6]),(0,[z1,z75,z4,z5,z6,z46]),(0,[z747,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z748]),(0,[z723,z1,z163,z3,z5,z6]),(0,[z1,z3,z4,z5,z6,z749])],[(0,[z0,z1,z3,z4,z750,z6]),(0,[z49,z1,z3,z222,z5,z6]),(0,[z0,z1,z3,z4,z5,z7]),(0,[z0,z1,z117,z4,z5,z6])],[(0,[z0,z89,z471,z1,z5,z6]),(0,[z109,z0,z1,z4,z96,z6])],[(0,[z0,z1,z3,z751,z5,z6]),(0,[z201,z0,z1,z75,z4,z5]),(0,[z201,z0,z1,z3,z752,z5]),(0,[z45,z1,z3,z4,z5,z94]),(0,[z0,z1,z4,z5,z223,z6])],[(0,[z49,z1,z3,z4,z5,z87]),(0,[z0,z753,z1,z4,z5,z6]),(0,[z754,z1,z3,z4,z5,z6]),(0,[z0,z1,z755,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z756,z5,z6]),(0,[z37,z1,z598,z4,z226,z6]),(0,[z266,z1,z3,z165,z5,z6])],[(0,[z0,z1,z3,z4,z5,z757]),(0,[z21,z1,z75,z4,z5,z6]),(0,[z0,z1,z3,z5,z758,z6]),(0,[z0,z29,z3,z759,z5,z6])],[(0,[z253,z1,z75,z4,z5,z6])],[(0,[z760,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z761,z6])],[(0,[z0,z762,z3,z4,z5,z6]),(0,[z0,z1,z3,z411,z5,z6])],[(0,[z0,z1,z763,z4,z5,z6]),(0,[z0,z1,z3,z764,z5,z6]),(0,[z0,z1,z3,z4,z5,z242]),(0,[z171,z1,z3,z55,z5,z6]),(0,[z174,z176,z1,z4,z5,z294])],[(0,[z0,z1,z598,z4,z5,z6]),(0,[z0,z1,z765,z4,z5,z6]),(0,[z0,z1,z3,z766,z5,z6]),(0,[z0,z1,z767,z4,z5,z6]),(0,[z0,z768,z3,z4,z5,z6]),(0,[z769,z1,z3,z4,z5,z6]),(0,[z1,z3,z411,z770,z5,z6])],[(0,[z0,z771,z3,z4,z5,z6]),(0,[z178,z1,z598,z4,z5,z6]),(0,[z0,z1,z3,z222,z5,z87]),(0,[z1,z3,z4,z772,z226,z6]),(0,[z45,z1,z3,z72,z5,z46]),(0,[z773,z1,z3,z4,z5,z6])]],
   [[(0,[z178,z771,z3,z4,z5,z6]),(0,[z774,z1,z3,z4,z5,z6]),(0,[z1,z23,z3,z115,z5,z6]),(0,[z775,z1,z3,z4,z5,z6]),(0,[z776,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z15,z5,z7]),(0,[z0,z1,z3,z165,z5,z88]),(0,[z0,z1,z4,z5,z777,z6]),(0,[z778,z1,z3,z4,z5,z6]),(0,[z0,z779,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z780]),(0,[z1,z2,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z781]),(0,[z1,z4,z5,z6,z126,z392]),(0,[z782,z1,z3,z4,z5,z6]),(0,[z28,z0,z1,z3,z159,z303]),(0,[z783,z1,z3,z4,z5,z6])],[(0,[z174,z0,z1,z75,z4,z5]),(0,[z1,z163,z784,z3,z5,z6]),(0,[z0,z1,z785,z4,z5,z6]),(0,[z0,z1,z12,z282,z5,z242])],[(0,[z201,z1,z3,z4,z5,z226]),(0,[z45,z1,z214,z57,z4,z5]),(0,[z0,z1,z3,z4,z5,z786])],[(0,[z0,z1,z3,z4,z5,z787]),(0,[z0,z788,z3,z4,z5,z6]),(0,[z0,z1,z789,z4,z5,z6]),(0,[z501,z1,z3,z108,z5,z6]),(0,[z1,z3,z4,z5,z790,z6]),(0,[z333,z1,z4,z5,z6,z126]),(0,[z0,z1,z3,z5,z791,z6]),(0,[z1,z3,z4,z5,z792,z6])],[(0,[z178,z631,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z793]),(0,[z164,z449,z0,z3,z4,z90]),(0,[z0,z1,z794,z4,z5,z6])],[(0,[z0,z1,z3,z795,z5,z6]),(0,[z0,z1,z796,z4,z5,z6]),(0,[z0,z797,z1,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z798]),(0,[z0,z1,z3,z4,z799,z6]),(0,[z800,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z801,z4,z5,z6]),(0,[z0,z1,z3,z5,z802,z6]),(0,[z164,z0,z3,z4,z90,z88]),(0,[z803,z1,z3,z4,z5,z6]),(0,[z0,z1,z804,z3,z5,z6])],[(0,[z805,z1,z3,z4,z5,z6]),(0,[z0,z806,z3,z4,z5,z6]),(0,[z28,z501,z1,z3,z159,z6])],[(0,[z1,z3,z4,z15,z5,z87]),(0,[z1,z807,z3,z4,z5,z6])],[(0,[z0,z1,z808,z4,z5,z6]),(0,[z0,z1,z12,z282,z5,z6]),(0,[z0,z1,z3,z4,z5,z809])],[(0,[z771,z241,z3,z4,z5,z6]),(0,[z178,z646,z3,z4,z5,z6]),(0,[z0,z1,z3,z810,z5,z6]),(0,[z0,z3,z4,z5,z811,z6]),(0,[z0,z1,z3,z742,z5,z6])],[(0,[z201,z49,z1,z3,z4,z5]),(0,[z0,z1,z3,z812,z5,z6]),(0,[z0,z1,z244,z400,z5,z6]),(0,[z813,z1,z3,z4,z5,z6])],[(0,[z0,z814,z1,z4,z5,z6]),(0,[z0,z1,z815,z4,z5,z6]),(0,[z37,z1,z3,z4,z772,z6]),(0,[z0,z1,z3,z816,z5,z6]),(0,[z1,z3,z4,z5,z6,z817]),(0,[z158,z1,z3,z165,z5,z6]),(0,[z449,z0,z1,z3,z5,z443]),(0,[z1,z3,z4,z5,z818,z6])],[(0,[z0,z1,z3,z4,z5,z819]),(0,[z0,z820,z1,z3,z4,z5]),(0,[z0,z821,z1,z4,z5,z6])]],
   [[(0,[z224,z1,z3,z50,z5,z6]),(0,[z0,z1,z353,z222,z5,z6]),(0,[z822,z1,z3,z4,z5,z6]),(0,[z0,z823,z3,z4,z5,z6]),(0,[z224,z1,z3,z4,z5,z27])],[(0,[z0,z1,z824,z4,z5,z6]),(0,[z0,z1,z825,z4,z5,z6])],[(0,[z826,z1,z3,z4,z5,z6]),(0,[z68,z0,z168,z4,z5,z63]),(0,[z0,z1,z3,z827,z5,z6]),(0,[z0,z299,z463,z4,z5,z6])],[(0,[z307,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z828,z6]),(0,[z0,z829,z3,z4,z5,z6]),(0,[z830,z1,z3,z4,z5,z6]),(0,[z36,z1,z3,z831,z5,z6])],[(0,[z36,z1,z3,z4,z5,z6]),(0,[z0,z1,z257,z3,z5,z27]),(0,[z0,z1,z3,z4,z5,z832]),(0,[z0,z1,z3,z833,z5,z6])],[(0,[z0,z1,z463,z4,z5,z218]),(0,[z834,z1,z3,z4,z5,z6])],[(0,[z835,z0,z1,z3,z4,z5]),(0,[z205,z1,z3,z742,z5,z6]),(0,[z0,z1,z3,z4,z5,z836])],[(0,[z49,z1,z3,z252,z5,z6]),(0,[z0,z1,z837,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z838]),(0,[z0,z40,z1,z4,z5,z7]),(0,[z68,z0,z3,z4,z5,z63]),(0,[z0,z1,z794,z3,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z839]),(0,[z0,z1,z840,z4,z5,z6]),(0,[z841,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z50,z5,z303]),(0,[z0,z842,z4,z25,z5,z6]),(0,[z0,z1,z3,z4,z5,z843]),(0,[z0,z1,z3,z844,z5,z6]),(0,[z164,z173,z3,z4,z90,z6]),(0,[z0,z1,z3,z34,z5,z27])],[(0,[z0,z1,z3,z845,z5,z6]),(0,[z253,z1,z846,z4,z5,z6]),(0,[z0,z210,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z847]),(0,[z0,z1,z3,z848,z5,z6])],[(0,[z0,z1,z849,z4,z5,z6]),(0,[z850,z0,z1,z3,z5,z6]),(0,[z0,z851,z3,z4,z5,z6])],[(0,[z0,z1,z852,z4,z5,z6]),(0,[z49,z1,z75,z4,z5,z6]),(0,[z0,z1,z853,z4,z5,z6])],[(0,[z854,z1,z3,z4,z5,z6]),(0,[z855,z1,z3,z4,z5,z6]),(0,[z856,z1,z3,z4,z5,z6]),(0,[z857,z1,z3,z4,z5,z6]),(0,[z68,z0,z3,z518,z5,z63])],[(0,[z858,z1,z3,z4,z5,z6]),(0,[z0,z210,z3,z115,z5,z6])],[(0,[z253,z1,z97,z58,z4,z5]),(0,[z1,z3,z4,z5,z859,z6]),(0,[z0,z1,z3,z543,z5,z27]),(0,[z0,z1,z3,z4,z5,z860]),(0,[z1,z861,z3,z4,z5,z6]),(0,[z862,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z432,z5,z27]),(0,[z1,z3,z4,z5,z6,z863])]],
   [[(0,[z864,z1,z3,z4,z5,z6]),(0,[z307,z1,z3,z15,z5,z6]),(0,[z0,z1,z244,z4,z5,z6]),(0,[z1,z865,z3,z4,z5,z6])],[(0,[z0,z1,z866,z4,z5,z6]),(0,[z201,z0,z1,z24,z4,z5]),(0,[z0,z867,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z868]),(0,[z0,z1,z3,z869,z5,z6]),(0,[z0,z1,z4,z5,z870,z6])],[(0,[z178,z241,z3,z252,z5,z6]),(0,[z0,z1,z3,z222,z5,z6]),(0,[z0,z1,z3,z4,z5,z871]),(0,[z266,z1,z3,z4,z5,z88])],[(0,[z0,z1,z3,z4,z872,z6]),(0,[z1,z637,z3,z15,z5,z6]),(0,[z0,z3,z759,z4,z5,z6]),(0,[z1,z23,z3,z5,z6,z27]),(0,[z1,z3,z4,z5,z6,z873])],[(0,[z0,z874,z1,z4,z5,z6]),(0,[z501,z1,z3,z50,z5,z6]),(0,[z0,z1,z75,z222,z5,z6])],[(0,[z0,z1,z3,z4,z5,z875]),(0,[z201,z1,z3,z4,z15,z5]),(0,[z0,z1,z3,z4,z5,z87]),(0,[z1,z3,z4,z5,z876,z6]),(0,[z0,z1,z3,z877,z5,z6]),(0,[z173,z471,z1,z3,z5,z6]),(0,[z0,z471,z210,z3,z5,z6])],[(0,[z109,z0,z1,z4,z291,z6]),(0,[z0,z1,z878,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z879])],[(0,[z0,z210,z3,z15,z5,z6]),(0,[z0,z1,z22,z3,z5,z182]),(0,[z0,z1,z3,z5,z880,z6]),(0,[z0,z1,z256,z4,z5,z233]),(0,[z881,z1,z3,z4,z5,z6]),(0,[z0,z1,z447,z282,z5,z6]),(0,[z109,z240,z1,z4,z96,z6])]],
   [[(0,[z882,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z883]),(0,[z884,z1,z3,z4,z5,z6]),(0,[z885,z1,z3,z4,z5,z6]),(0,[z886,z1,z3,z4,z5,z6]),(0,[z234,z0,z1,z3,z4,z887])],[(0,[z0,z1,z3,z252,z5,z888]),(0,[z164,z0,z3,z4,z276,z90])],[(0,[z0,z1,z150,z4,z5,z6]),(0,[z0,z1,z3,z889,z5,z6])],[(0,[z0,z1,z463,z5,z6,z27]),(0,[z28,z0,z1,z3,z159,z6]),(0,[z1,z3,z4,z770,z5,z6])],[(0,[z0,z1,z3,z4,z5,z888]),(0,[z449,z0,z89,z1,z4,z5]),(0,[z890,z1,z3,z4,z5,z6])],[(0,[z0,z284,z3,z26,z5,z6]),(0,[z0,z1,z3,z4,z5,z276])],[(0,[z28,z0,z1,z3,z191,z6]),(0,[z0,z891,z1,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z892])],[(0,[z393,z1,z3,z4,z226,z6]),(0,[z0,z1,z3,z4,z893,z6]),(0,[z0,z514,z3,z26,z5,z6]),(0,[z1,z894,z3,z4,z5,z6]),(0,[z0,z1,z895,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z896])]],
   [[(0,[z0,z1,z3,z4,z5,z897]),(0,[z0,z1,z3,z4,z5,z898]),(0,[z899,z1,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z6,z392]),(0,[z0,z3,z842,z4,z5,z6]),(0,[z900,z1,z3,z4,z5,z6]),(0,[z68,z0,z3,z34,z5,z63])],[(0,[z0,z1,z3,z4,z5,z901]),(0,[z0,z1,z3,z4,z902,z6]),(0,[z0,z1,z3,z4,z903,z5]),(0,[z0,z1,z904,z4,z5,z6]),(0,[z1,z3,z4,z5,z243,z6]),(0,[z0,z1,z318,z400,z5,z6]),(0,[z449,z173,z1,z3,z4,z5]),(0,[z28,z0,z1,z3,z209,z6]),(0,[z0,z1,z41,z463,z5,z6])],[(0,[z0,z1,z905,z4,z5,z6]),(0,[z14,z1,z75,z4,z5,z6]),(0,[z201,z118,z1,z3,z4,z5]),(0,[z0,z1,z906,z4,z5,z6]),(0,[z0,z51,z246,z4,z5,z6]),(0,[z0,z1,z3,z907,z5,z6]),(0,[z0,z1,z3,z5,z443,z276])],[(0,[z0,z1,z3,z908,z5,z6]),(0,[z0,z1,z909,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z910]),(0,[z0,z210,z3,z4,z5,z303])],[(0,[z0,z1,z911,z4,z5,z6]),(0,[z1,z397,z3,z4,z5,z6]),(0,[z110,z1,z3,z4,z5,z6]),(0,[z175,z1,z3,z4,z5,z6]),(0,[z912,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z913,z5,z6]),(0,[z0,z1,z3,z400,z5,z6]),(0,[z0,z1,z914,z3,z5,z6]),(0,[z0,z1,z3,z5,z892,z27]),(0,[z0,z1,z3,z411,z5,z128]),(0,[z915,z1,z3,z411,z5,z6])],[(0,[z0,z1,z353,z4,z5,z6]),(0,[z0,z1,z3,z916,z5,z6]),(0,[z1,z3,z290,z5,z76,z6]),(0,[z0,z1,z3,z4,z5,z917]),(0,[z0,z1,z918,z4,z5,z6]),(0,[z307,z40,z1,z4,z5,z6]),(0,[z149,z1,z3,z4,z5,z355]),(0,[z0,z1,z3,z4,z5,z919]),(0,[z545,z0,z1,z3,z5,z27])],[(0,[z178,z201,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z920]),(0,[z266,z1,z3,z4,z5,z370])]],
   [[(0,[z0,z1,z163,z282,z5,z6]),(0,[z0,z1,z22,z3,z5,z242])],[(0,[z0,z1,z4,z5,z6,z921]),(0,[z45,z1,z3,z15,z5,z27]),(0,[z0,z1,z842,z4,z5,z6]),(0,[z0,z1,z922,z4,z5,z6]),(0,[z198,z210,z3,z4,z5,z6])],[(0,[z0,z1,z3,z923,z5,z6]),(0,[z0,z1,z3,z924,z5,z6]),(0,[z925,z1,z3,z4,z5,z6])],[(0,[z926,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z927,z5,z6]),(0,[z0,z210,z12,z3,z5,z6])],[(0,[z1,z397,z4,z5,z96,z6]),(0,[z928,z1,z3,z4,z5,z6]),(0,[z110,z1,z4,z5,z96,z6]),(0,[z175,z1,z4,z5,z96,z6]),(0,[z0,z1,z3,z929,z5,z6])],[(0,[z1,z58,z4,z5,z6,z642]),(0,[z0,z1,z3,z4,z5,z233]),(0,[z0,z1,z3,z930,z5,z6]),(0,[z931,z1,z3,z4,z5,z6]),(0,[z1,z117,z4,z5,z243,z6])],[(0,[z446,z0,z1,z3,z5,z27]),(0,[z0,z1,z3,z5,z6,z238])],[(0,[z0,z1,z932,z4,z5,z6]),(0,[z0,z1,z933,z4,z5,z6]),(0,[z0,z934,z1,z3,z5,z6]),(0,[z501,z210,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z935,z4,z5,z6]),(0,[z201,z1,z214,z3,z4,z5]),(0,[z0,z1,z3,z936,z5,z6]),(0,[z0,z1,z3,z4,z5,z937]),(0,[z307,z1,z256,z4,z5,z6])],[(0,[z530,z1,z3,z15,z5,z6])],[(0,[z1,z3,z4,z5,z772,z6]),(0,[z164,z0,z3,z443,z90,z6])],[(0,[z0,z938,z3,z4,z5,z6]),(0,[z110,z51,z1,z4,z5,z6])],[(0,[z1,z3,z50,z742,z5,z6]),(0,[z0,z1,z75,z4,z5,z27]),(0,[z0,z1,z4,z5,z6,z939]),(0,[z501,z1,z3,z4,z5,z303])],[(0,[z0,z1,z3,z252,z5,z6]),(0,[z0,z1,z318,z4,z5,z6]),(0,[z168,z1,z4,z5,z6,z392])],[(0,[z940,z1,z3,z4,z5,z6]),(0,[z0,z1,z941,z4,z5,z6]),(0,[z0,z1,z244,z165,z5,z6]),(0,[z164,z0,z4,z223,z90,z6]),(0,[z942,z1,z3,z4,z5,z6])],[(0,[z176,z1,z214,z4,z5,z6]),(0,[z943,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z944,z6]),(0,[z0,z1,z3,z945,z5,z6]),(0,[z0,z946,z1,z3,z4,z5]),(0,[z1,z947,z3,z4,z5,z6]),(0,[z175,z1,z3,z55,z5,z6]),(0,[z234,z0,z1,z3,z4,z154])],[(0,[z948,z1,z3,z4,z5,z6])],[(0,[z0,z1,z75,z4,z5,z6]),(0,[z949,z1,z3,z4,z5,z6]),(0,[z950,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z951,z6]),(0,[z0,z1,z952,z4,z5,z6]),(0,[z164,z0,z3,z4,z717,z6]),(0,[z953,z1,z3,z4,z5,z6])],[(0,[z178,z1,z75,z4,z5,z6]),(0,[z234,z0,z1,z3,z4,z433]),(0,[z0,z1,z3,z5,z212,z27])],[(0,[z0,z1,z4,z5,z954,z6]),(0,[z0,z1,z3,z5,z6,z955]),(0,[z171,z1,z3,z13,z5,z6])],[(0,[z0,z1,z3,z4,z5,z956]),(0,[z0,z1,z3,z957,z5,z6]),(0,[z158,z1,z3,z4,z5,z370]),(0,[z164,z0,z244,z4,z90,z6]),(0,[z1,z4,z5,z243,z122,z6])],[(0,[z958,z1,z3,z4,z5,z6]),(0,[z0,z1,z959,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z960]),(0,[z0,z1,z3,z5,z443,z6])],[(0,[z0,z1,z3,z4,z5,z961]),(0,[z0,z1,z962,z4,z5,z6]),(0,[z0,z1,z963,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z964])]],
   [[(0,[z0,z1,z3,z965,z5,z6]),(0,[z1,z771,z3,z4,z5,z6]),(0,[z0,z1,z3,z411,z5,z218])],[(0,[z240,z1,z3,z4,z5,z6]),(0,[z201,z0,z1,z4,z5,z294]),(0,[z0,z1,z966,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z967]),(0,[z0,z1,z968,z3,z5,z6])],[(0,[z0,z1,z3,z4,z5,z969]),(0,[z49,z1,z3,z98,z5,z6])],[(0,[z386,z0,z1,z3,z4,z154])],[(0,[z1,z3,z58,z440,z5,z6]),(0,[z970,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z971]),(0,[z972,z1,z3,z4,z5,z6]),(0,[z28,z1,z3,z106,z5,z6])],[(0,[z0,z1,z3,z4,z5,z973]),(0,[z0,z1,z3,z4,z5,z974]),(0,[z975,z1,z3,z4,z5,z6])],[(0,[z1,z3,z742,z15,z5,z6]),(0,[z1,z3,z4,z106,z5,z6]),(0,[z0,z1,z3,z34,z5,z233]),(0,[z775,z1,z41,z3,z5,z6])]],
   [[(0,[z0,z1,z3,z5,z233,z27]),(0,[z0,z1,z3,z4,z5,z976]),(0,[z1,z3,z4,z5,z977,z6])],[(0,[z224,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z527,z226,z6]),(0,[z1,z381,z3,z4,z5,z242])],[(0,[z21,z1,z57,z58,z4,z5]),(0,[z174,z1,z4,z5,z189,z294]),(0,[z978,z1,z3,z4,z5,z6])],[(0,[z325,z1,z58,z4,z5,z6]),(0,[z118,z1,z75,z4,z5,z6]),(0,[z0,z1,z3,z979,z5,z6]),(0,[z0,z89,z1,z4,z5,z276]),(0,[z0,z1,z3,z55,z5,z6]),(0,[z0,z1,z12,z282,z5,z355]),(0,[z93,z0,z1,z3,z5,z27]),(0,[z36,z1,z3,z980,z5,z6])],[(0,[z694,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z981]),(0,[z0,z1,z4,z5,z982,z6])],[(0,[z1,z846,z58,z4,z5,z6]),(0,[z0,z1,z3,z5,z983,z6]),(0,[z0,z1,z3,z4,z5,z984]),(0,[z250,z0,z3,z4,z90,z6])],[(0,[z1,z3,z72,z5,z226,z6]),(0,[z0,z1,z3,z985,z5,z6]),(0,[z68,z3,z4,z5,z392,z63]),(0,[z174,z0,z1,z4,z5,z294]),(0,[z0,z210,z3,z5,z159,z6])],[(0,[z986,z0,z1,z3,z4,z5]),(0,[z205,z1,z3,z15,z5,z6]),(0,[z0,z1,z3,z4,z5,z987]),(0,[z174,z0,z1,z4,z5,z373]),(0,[z0,z1,z3,z988,z5,z6]),(0,[z1,z3,z4,z989,z5,z6])]],
   [[(0,[z14,z1,z3,z72,z5,z6]),(0,[z287,z1,z58,z4,z5,z6]),(0,[z1,z3,z4,z5,z790,z46]),(0,[z0,z40,z1,z4,z5,z233])],[(0,[z0,z1,z3,z990,z5,z6]),(0,[z0,z1,z991,z4,z5,z6]),(0,[z45,z0,z1,z3,z13,z5]),(0,[z28,z0,z1,z3,z791,z6])],[(0,[z0,z992,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z993]),(0,[z0,z1,z3,z34,z5,z6]),(0,[z164,z0,z3,z400,z90,z6]),(0,[z994,z1,z3,z4,z5,z6]),(0,[z0,z1,z41,z3,z5,z809]),(0,[z0,z1,z3,z4,z5,z303])],[(0,[z0,z1,z3,z995,z5,z6]),(0,[z0,z3,z759,z26,z5,z6]),(0,[z109,z0,z1,z4,z799,z6])],[(0,[z0,z1,z3,z4,z5,z996]),(0,[z997,z1,z3,z4,z5,z6]),(0,[z0,z1,z794,z12,z5,z6]),(0,[z0,z210,z472,z4,z5,z6])],[(0,[z178,z241,z3,z440,z5,z6]),(0,[z0,z1,z998,z4,z5,z6]),(0,[z0,z1,z353,z72,z5,z6]),(0,[z0,z1,z999,z4,z5,z6]),(0,[z1,z23,z3,z4,z5,z7]),(0,[z164,z266,z3,z4,z90,z6]),(0,[z0,z1,z3,z1000,z5,z6]),(0,[z164,z3,z4,z141,z90,z6]),(0,[z333,z1,z3,z1001,z5,z6]),(0,[z1002,z1,z3,z4,z5,z6])],[(0,[z224,z1,z3,z15,z5,z6]),(0,[z0,z1,z3,z105,z5,z182]),(0,[z0,z1,z3,z4,z5,z1003]),(0,[z0,z1,z3,z4,z5,z1004]),(0,[z0,z1,z1005,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z887])],[(0,[z198,z1,z3,z4,z5,z6]),(0,[z40,z1,z23,z4,z5,z6]),(0,[z176,z1,z3,z4,z5,z128])]],
   [[(0,[z178,z241,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z1006,z6])],[(0,[z0,z1,z3,z752,z5,z6]),(0,[z1007,z1,z3,z4,z5,z6])],[(0,[z333,z1,z3,z4,z5,z6]),(0,[z0,z1,z846,z4,z5,z6]),(0,[z0,z1,z1008,z3,z5,z6]),(0,[z0,z1,z4,z5,z6,z1009]),(0,[z1010,z1,z3,z4,z5,z6])],[(0,[z0,z1,z318,z165,z5,z6]),(0,[z89,z1,z4,z5,z141,z6]),(0,[z1011,z1,z3,z4,z5,z6]),(0,[z0,z1,z13,z5,z96,z6]),(0,[z198,z1,z3,z115,z5,z6])],[(0,[z0,z1,z3,z1012,z5,z6]),(0,[z0,z1,z1013,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1014]),(0,[z0,z1015,z1,z4,z5,z6])],[(0,[z0,z1,z1016,z4,z5,z6]),(0,[z501,z1,z3,z4,z5,z6]),(0,[z0,z52,z1,z256,z5,z6]),(0,[z0,z210,z3,z200,z5,z6])],[(0,[z0,z1,z3,z108,z5,z1017]),(0,[z1018,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z165,z5,z6]),(0,[z0,z1,z1019,z4,z5,z6]),(0,[z0,z210,z3,z4,z5,z218])],[(0,[z0,z1,z3,z1020,z5,z6]),(0,[z0,z1,z3,z15,z5,z303]),(0,[z0,z1,z3,z26,z5,z182]),(0,[z0,z1,z3,z1021,z5,z6]),(0,[z174,z176,z1,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z4,z5,z1022]),(0,[z173,z1,z4,z5,z223,z6]),(0,[z0,z299,z3,z4,z5,z303])],[(0,[z213,z1,z3,z440,z5,z6]),(0,[z371,z1,z3,z15,z5,z6]),(0,[z174,z0,z1,z55,z5,z294])],[(0,[z45,z1,z3,z440,z5,z6]),(0,[z110,z100,z1,z4,z5,z6]),(0,[z175,z100,z1,z4,z5,z6]),(0,[z250,z0,z1,z3,z159,z6]),(0,[z164,z0,z318,z4,z90,z6]),(0,[z0,z3,z400,z5,z90,z6]),(0,[z0,z1,z1023,z3,z5,z6])],[(0,[z0,z1,z3,z1024,z5,z6]),(0,[z1025,z1,z3,z4,z5,z6]),(0,[z1,z397,z24,z4,z5,z6]),(0,[z110,z1,z24,z4,z5,z6])],[(0,[z1,z214,z75,z4,z5,z6]),(0,[z45,z1,z3,z4,z5,z490]),(0,[z0,z1,z3,z5,z1026,z6]),(0,[z0,z1,z3,z4,z5,z1027]),(0,[z174,z175,z1,z4,z5,z294])],[(0,[z0,z1,z3,z252,z5,z1028]),(0,[z49,z1,z3,z50,z5,z182]),(0,[z0,z1,z3,z5,z87,z27]),(0,[z0,z1,z256,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1029]),(0,[z0,z1030,z1,z3,z5,z6]),(0,[z164,z0,z3,z4,z90,z6]),(0,[z1031,z1,z3,z4,z5,z6])],[(0,[z0,z89,z1,z4,z5,z6]),(0,[z28,z0,z299,z3,z159,z6])],[(0,[z253,z201,z1,z58,z4,z5]),(0,[z0,z1,z3,z72,z5,z6]),(0,[z1032,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1033]),(0,[z0,z1,z3,z105,z5,z242]),(0,[z1034,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z13,z5,z294])]],
   [[(0,[z178,z1,z3,z72,z5,z6]),(0,[z0,z1,z3,z1035,z5,z6])],[(0,[z0,z1,z1036,z4,z5,z6]),(0,[z0,z1,z75,z72,z5,z6]),(0,[z0,z1,z3,z4,z5,z790]),(0,[z0,z1,z256,z115,z5,z6]),(0,[z0,z1,z4,z5,z1037,z6]),(0,[z0,z1038,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1039]),(0,[z1,z3,z58,z290,z5,z6]),(0,[z501,z1,z3,z15,z5,z6])],[(0,[z1,z220,z3,z15,z5,z6]),(0,[z1,z3,z222,z15,z5,z6]),(0,[z1,z598,z4,z5,z226,z6]),(0,[z158,z1,z3,z4,z5,z88]),(0,[z0,z1,z3,z1040,z5,z6]),(0,[z1041,z1,z3,z4,z5,z6]),(0,[z0,z1,z1042,z4,z5,z6]),(0,[z28,z0,z1,z463,z159,z6]),(0,[z0,z1,z3,z4,z5,z892])],[(0,[z0,z1,z3,z5,z1043,z6]),(0,[z0,z89,z1,z5,z443,z6]),(0,[z1,z41,z947,z3,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1044]),(0,[z1,z75,z4,z5,z226,z6]),(0,[z0,z1045,z1,z4,z5,z6]),(0,[z1046,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z1047,z63]),(0,[z174,z0,z1,z13,z5,z294]),(0,[z0,z1,z3,z4,z5,z1048])],[(0,[z178,z305,z3,z4,z5,z6]),(0,[z263,z1,z3,z15,z5,z6]),(0,[z0,z1,z1049,z4,z5,z6]),(0,[z0,z1,z3,z1050,z5,z6]),(0,[z1051,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z1052,z5,z6]),(0,[z449,z0,z1,z4,z5,z223]),(0,[z1053,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z1048,z294]),(0,[z28,z0,z1,z3,z159,z218]),(0,[z1054,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z1055,z5,z6]),(0,[z0,z1,z3,z4,z5,z1056]),(0,[z0,z1,z3,z26,z5,z242]),(0,[z0,z1057,z1,z4,z5,z6])],[(0,[z1058,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1059]),(0,[z0,z3,z4,z5,z6,z1047]),(0,[z198,z1,z3,z4,z5,z303]),(0,[z1,z3,z4,z5,z1060,z6])],[(0,[z0,z1,z3,z4,z5,z1061])],[(0,[z174,z0,z1,z4,z5,z1048]),(0,[z510,z0,z1,z3,z4,z154])],[(0,[z37,z1,z3,z4,z427,z6]),(0,[z0,z1,z1062,z4,z5,z6]),(0,[z1,z1063,z3,z4,z5,z6]),(0,[z0,z1,z41,z282,z5,z6]),(0,[z0,z1,z447,z4,z5,z294]),(0,[z0,z210,z3,z5,z6,z27]),(0,[z0,z1,z3,z4,z887,z154])],[(0,[z178,z495,z3,z4,z5,z6]),(0,[z0,z1,z3,z1064,z5,z6]),(0,[z37,z1,z3,z4,z226,z6]),(0,[z0,z168,z1,z4,z5,z6]),(0,[z0,z53,z4,z25,z5,z6]),(0,[z0,z1,z163,z256,z5,z6]),(0,[z0,z1,z41,z3,z5,z730]),(0,[z175,z1,z57,z4,z5,z6])],[(0,[z0,z1,z3,z4,z772,z6]),(0,[z175,z51,z1,z4,z5,z6]),(0,[z0,z1,z3,z1001,z5,z6])],[(0,[z0,z1,z1065,z4,z5,z6]),(0,[z1,z1066,z3,z4,z5,z6]),(0,[z175,z1,z4,z5,z6,z294])]],
   [[(0,[z0,z1,z3,z440,z5,z6]),(0,[z118,z1,z3,z72,z5,z6])],[(0,[z0,z1,z3,z1067,z5,z6]),(0,[z0,z1,z3,z1068,z5,z6]),(0,[z0,z1,z3,z1069,z5,z6]),(0,[z1070,z1,z3,z4,z5,z6]),(0,[z1071,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1047]),(0,[z1072,z1,z3,z4,z5,z6]),(0,[z0,z1,z402,z3,z5,z27]),(0,[z28,z198,z1,z3,z159,z6]),(0,[z0,z1073,z3,z4,z5,z6]),(0,[z0,z1,z3,z831,z5,z6])],[(0,[z14,z1,z113,z4,z5,z6]),(0,[z0,z1,z1074,z4,z5,z6]),(0,[z0,z1,z163,z3,z5,z1056]),(0,[z1,z3,z4,z5,z1075,z6]),(0,[z0,z52,z1,z463,z5,z6]),(0,[z1,z3,z4,z5,z1076,z6]),(0,[z28,z0,z1,z472,z159,z6])],[],[(0,[z0,z1,z1077,z4,z5,z6]),(0,[z1,z1078,z3,z4,z5,z6])],[(0,[z449,z0,z1,z3,z4,z5]),(0,[z0,z1,z1079,z4,z5,z6])],[(0,[z1,z22,z3,z106,z5,z6]),(0,[z0,z1,z1080,z4,z5,z6]),(0,[z0,z1,z1081,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1082]),(0,[z0,z1,z1083,z4,z5,z6]),(0,[z0,z1,z3,z5,z218,z27])]],
   [[(0,[z0,z1,z57,z75,z4,z5]),(0,[z0,z1,z3,z4,z5,z1084]),(0,[z0,z471,z1,z3,z5,z276]),(0,[z28,z1,z381,z3,z5,z6])],[(0,[z0,z1,z4,z5,z1085,z6]),(0,[z1086,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z518,z5,z6])],[(0,[z0,z1,z3,z4,z1087,z6]),(0,[z0,z1,z3,z4,z5,z1088]),(0,[z0,z1,z472,z4,z5,z6]),(0,[z1,z3,z4,z1089,z5,z6]),(0,[z224,z1,z3,z4,z5,z128])],[(0,[z0,z1090,z1,z3,z5,z6]),(0,[z0,z210,z463,z4,z5,z6])],[(0,[z0,z1,z1091,z4,z5,z6]),(0,[z0,z3,z4,z5,z717,z6])],[(0,[z45,z1,z3,z4,z5,z556]),(0,[z0,z1,z3,z5,z6,z1092]),(0,[z1093,z0,z1,z3,z4,z5]),(0,[z0,z1094,z3,z4,z5,z6]),(0,[z0,z1,z3,z1095,z5,z6])],[(0,[z0,z1,z3,z1096,z5,z6]),(0,[z0,z1097,z3,z4,z5,z6]),(0,[z0,z1,z3,z1098,z5,z6]),(0,[z0,z1,z163,z3,z5,z6]),(0,[z0,z29,z210,z3,z5,z6]),(0,[z1099,z1,z3,z4,z5,z6]),(0,[z1100,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z1101,z6]),(0,[z478,z0,z1,z3,z5,z27])],[(0,[z1,z846,z3,z4,z5,z6]),(0,[z0,z1,z1102,z3,z5,z6]),(0,[z68,z0,z685,z3,z4,z5]),(0,[z175,z1,z3,z13,z5,z6])]],
   [[(0,[z0,z1,z3,z5,z1103,z6]),(0,[z0,z1,z3,z4,z5,z355]),(0,[z0,z1,z463,z4,z5,z303])],[(0,[z0,z1,z3,z1104,z5,z6]),(0,[z0,z299,z3,z4,z5,z6]),(0,[z0,z554,z3,z26,z5,z6]),(0,[z0,z3,z4,z717,z90,z6])],[(0,[z0,z1105,z3,z4,z5,z6]),(0,[z0,z1,z1106,z4,z5,z6]),(0,[z1107,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1108]),(0,[z0,z1,z1109,z4,z5,z6]),(0,[z0,z1,z12,z256,z5,z6]),(0,[z164,z0,z3,z165,z90,z6]),(0,[z149,z1,z3,z4,z5,z242]),(0,[z0,z1,z3,z4,z791,z6])],[(0,[z0,z1,z3,z1110,z5,z6]),(0,[z1,z381,z22,z3,z5,z6]),(0,[z1111,z1,z3,z4,z5,z6]),(0,[z0,z11,z1,z3,z5,z242]),(0,[z0,z1,z3,z4,z5,z218])],[(0,[z0,z1,z4,z5,z1112,z6])],[(0,[z1,z3,z332,z15,z5,z6]),(0,[z0,z1,z3,z222,z5,z128]),(0,[z0,z30,z210,z3,z5,z6])],[(0,[z1,z3,z4,z5,z1113,z6]),(0,[z1114,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z1115])],[(0,[z0,z1,z3,z4,z5,z1116]),(0,[z1,z3,z4,z742,z5,z6]),(0,[z1,z12,z381,z282,z5,z6]),(0,[z1117,z0,z1,z3,z4,z5])],[(0,[z0,z1,z113,z4,z5,z6]),(0,[z0,z1,z4,z356,z96,z6]),(0,[z171,z174,z1,z4,z5,z294])],[(0,[z0,z1,z3,z4,z1118,z5]),(0,[z0,z1,z3,z1119,z5,z6]),(0,[z0,z1,z1120,z4,z5,z6]),(0,[z0,z1,z3,z1121,z5,z6]),(0,[z0,z1,z3,z759,z5,z6]),(0,[z1122,z1,z3,z4,z5,z6]),(0,[z109,z0,z1,z41,z96,z6]),(0,[z0,z1123,z1,z4,z5,z6])],[(0,[z14,z1,z598,z4,z5,z6]),(0,[z1,z381,z3,z4,z5,z6]),(0,[z99,z1,z3,z4,z226,z6]),(0,[z0,z100,z1,z13,z5,z6]),(0,[z0,z1,z3,z1124,z5,z6])],[(0,[z0,z1125,z1,z3,z5,z6]),(0,[z1126,z1,z3,z4,z5,z6]),(0,[z28,z0,z210,z3,z159,z6])],[(0,[z45,z1,z3,z4,z5,z790]),(0,[z0,z1,z3,z5,z6,z1127]),(0,[z68,z0,z4,z5,z126,z63])],[(0,[z100,z1,z397,z4,z5,z6]),(0,[z1128,z1,z3,z4,z5,z6]),(0,[z173,z1,z3,z4,z5,z276]),(0,[z333,z168,z1,z4,z5,z6])]],
   [[],[(0,[z0,z1,z3,z1129,z5,z6])],[(0,[z522,z1,z58,z4,z5,z6]),(0,[z45,z1,z3,z222,z5,z46]),(0,[z1,z1130,z3,z4,z5,z6]),(0,[z266,z1,z244,z4,z5,z6]),(0,[z0,z1,z3,z13,z5,z6])],[(0,[z1,z113,z4,z5,z226,z6]),(0,[z673,z1,z58,z4,z5,z6]),(0,[z104,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z50,z5,z7]),(0,[z1131,z1,z3,z4,z5,z6]),(0,[z0,z471,z1,z3,z5,z6])],[(0,[z45,z1,z3,z4,z5,z610]),(0,[z0,z1,z3,z1132,z5,z6]),(0,[z0,z1,z472,z4,z5,z303])],[(0,[z45,z1,z3,z4,z5,z616]),(0,[z1,z3,z4,z5,z6,z1133]),(0,[z1134,z1,z3,z4,z5,z6]),(0,[z0,z1,z1135,z4,z5,z6])],[(0,[z1,z75,z4,z15,z5,z6]),(0,[z0,z1,z3,z290,z5,z6]),(0,[z49,z1,z3,z50,z5,z87]),(0,[z0,z40,z1,z4,z5,z6]),(0,[z1,z23,z3,z4,z5,z233]),(0,[z0,z17,z3,z400,z5,z6]),(0,[z1,z3,z4,z1136,z5,z6]),(0,[z36,z1,z4,z5,z122,z6])],[(0,[z0,z1,z3,z4,z5,z1137]),(0,[z0,z1,z1138,z4,z5,z6]),(0,[z0,z1,z3,z1139,z5,z6]),(0,[z0,z1,z3,z4,z6,z887])]],
   [[(0,[z0,z1,z1140,z4,z5,z6]),(0,[z444,z0,z1,z3,z5,z27]),(0,[z0,z1,z3,z1141,z5,z6]),(0,[z0,z471,z3,z26,z5,z6]),(0,[z1099,z1,z3,z34,z5,z6]),(0,[z0,z1,z3,z282,z5,z242])],[(0,[z176,z1,z58,z4,z5,z6]),(0,[z21,z175,z1,z3,z4,z5]),(0,[z1142,z0,z1,z3,z4,z5]),(0,[z1,z381,z3,z4,z5,z355]),(0,[z198,z1,z472,z4,z5,z6])],[(0,[z49,z1,z3,z108,z5,z6]),(0,[z28,z0,z1,z3,z5,z182]),(0,[z0,z1,z3,z1143,z5,z6]),(0,[z0,z1,z3,z5,z6,z1144])],[(0,[z118,z1,z113,z4,z5,z6]),(0,[z0,z1,z1145,z3,z5,z6]),(0,[z0,z1,z3,z1146,z5,z6]),(0,[z1,z784,z3,z4,z5,z6]),(0,[z0,z1147,z1,z4,z5,z6]),(0,[z0,z1,z244,z4,z5,z88]),(0,[z1148,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z411,z5,z27])],[(0,[z0,z1,z1149,z4,z5,z6]),(0,[z0,z1,z1150,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1151]),(0,[z164,z0,z471,z3,z90,z6]),(0,[z1,z4,z5,z223,z141,z6])],[(0,[z0,z1,z3,z1152,z5,z6]),(0,[z45,z1,z132,z3,z4,z5]),(0,[z449,z0,z471,z1,z3,z5]),(0,[z68,z333,z3,z4,z5,z63]),(0,[z0,z52,z210,z3,z5,z6]),(0,[z1153,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1154]),(0,[z0,z1,z3,z1155,z5,z6]),(0,[z143,z1,z58,z4,z5,z6]),(0,[z0,z1156,z3,z4,z5,z6]),(0,[z0,z705,z3,z26,z5,z6]),(0,[z0,z1,z1157,z4,z5,z6]),(0,[z1158,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z1159,z5,z6]),(0,[z175,z1,z24,z4,z5,z6])],[(0,[z0,z1,z3,z5,z1160,z6]),(0,[z201,z0,z1,z57,z4,z5]),(0,[z37,z1,z268,z4,z226,z6]),(0,[z0,z1,z3,z1161,z5,z6]),(0,[z0,z1,z3,z4,z5,z1162]),(0,[z501,z1,z472,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z1163,z5,z6]),(0,[z0,z1,z3,z1164,z5,z6]),(0,[z201,z0,z100,z1,z4,z5]),(0,[z201,z0,z1,z3,z720,z5]),(0,[z51,z1,z397,z4,z5,z6]),(0,[z0,z51,z1,z13,z5,z6]),(0,[z0,z1,z3,z1165,z5,z6]),(0,[z0,z1,z1166,z4,z5,z6]),(0,[z0,z1167,z1,z4,z5,z6]),(0,[z198,z299,z3,z4,z5,z6]),(0,[z1168,z1,z3,z4,z5,z6])],[(0,[z1,z23,z3,z4,z5,z6]),(0,[z0,z1,z1169,z4,z5,z6]),(0,[z1170,z1,z3,z4,z5,z6]),(0,[z0,z471,z1,z5,z223,z6]),(0,[z0,z1,z794,z282,z5,z6]),(0,[z0,z1,z12,z463,z5,z6])],[(0,[z45,z1,z3,z4,z5,z642]),(0,[z0,z1,z3,z4,z1171,z6]),(0,[z0,z52,z1,z163,z5,z6]),(0,[z0,z1,z3,z4,z5,z1172])],[(0,[z0,z1,z3,z4,z5,z1028]),(0,[z0,z1,z1173,z4,z5,z6]),(0,[z0,z1,z3,z1174,z5,z6]),(0,[z1175,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1176]),(0,[z0,z1,z3,z4,z5,z1177]),(0,[z0,z1,z3,z5,z1178,z6]),(0,[z198,z1,z3,z4,z5,z218])],[(0,[z0,z1,z3,z4,z5,z1179]),(0,[z0,z1180,z1,z3,z5,z6])],[(0,[z0,z1,z268,z4,z5,z6]),(0,[z201,z1,z3,z4,z5,z46]),(0,[z45,z1,z3,z4,z5,z654]),(0,[z104,z45,z1,z3,z4,z5]),(0,[z0,z1,z3,z1181,z5,z6]),(0,[z1,z3,z4,z5,z6,z1182]),(0,[z0,z1,z4,z5,z799,z6]),(0,[z176,z1,z57,z3,z4,z5]),(0,[z0,z1,z1183,z3,z5,z6]),(0,[z0,z1,z1184,z4,z5,z6])],[(0,[z1185,z0,z1,z3,z4,z5]),(0,[z253,z1,z58,z4,z5,z6]),(0,[z1,z3,z1186,z4,z5,z6]),(0,[z45,z1,z353,z4,z5,z46]),(0,[z501,z299,z3,z4,z5,z6])],[(0,[z307,z1,z3,z4,z5,z7]),(0,[z266,z1,z3,z400,z5,z6]),(0,[z0,z1,z4,z5,z6,z1048])]],
   [[(0,[z0,z1,z1187,z4,z5,z6]),(0,[z0,z1188,z3,z4,z5,z6]),(0,[z158,z1,z244,z4,z5,z6]),(0,[z1189,z1,z3,z4,z5,z6]),(0,[z36,z1,z117,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1190]),(0,[z0,z1,z463,z4,z5,z6]),(0,[z501,z1,z3,z4,z5,z218])],[(0,[z173,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1191]),(0,[z0,z1,z3,z4,z5,z1192]),(0,[z1,z1193,z3,z4,z5,z6])],[(0,[z0,z1,z3,z1194,z5,z6]),(0,[z201,z0,z1,z3,z4,z5]),(0,[z0,z1,z1195,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z1196]),(0,[z1,z1197,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1198,z6]),(0,[z28,z0,z1,z3,z5,z242])],[(0,[z915,z1,z3,z4,z5,z6])],[(0,[z438,z241,z3,z4,z5,z6]),(0,[z0,z1,z3,z1199,z5,z6]),(0,[z1200,z1,z3,z4,z5,z6]),(0,[z307,z1,z3,z4,z5,z233]),(0,[z0,z1,z463,z115,z5,z6])],[(0,[z0,z1,z1201,z4,z5,z6]),(0,[z0,z1,z75,z4,z5,z128]),(0,[z0,z1,z3,z1202,z5,z6]),(0,[z449,z1,z3,z4,z5,z141]),(0,[z0,z1,z4,z799,z96,z6])],[(0,[z377,z1,z58,z4,z5,z6]),(0,[z201,z0,z51,z1,z4,z5]),(0,[z1203,z1,z3,z4,z5,z6])]],
   [[(0,[z1204,z1,z3,z4,z5,z6]),(0,[z1205,z1,z3,z4,z5,z6]),(0,[z0,z1,z244,z4,z5,z370]),(0,[z0,z1,z3,z400,z5,z88]),(0,[z173,z1,z3,z5,z443,z6])],[(0,[z0,z1,z3,z1206,z5,z6]),(0,[z68,z0,z3,z4,z5,z473])],[(0,[z0,z1,z3,z1207,z5,z6]),(0,[z0,z1,z4,z5,z6,z1208]),(0,[z307,z1,z3,z50,z5,z6]),(0,[z1209,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z141,z276]),(0,[z0,z1210,z3,z4,z5,z6])],[(0,[z1211,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1212])],[(0,[z118,z1,z598,z4,z5,z6]),(0,[z1213,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z1214,z5,z6])],[(0,[z307,z1,z3,z252,z5,z6]),(0,[z0,z1,z3,z4,z5,z1215])],[(0,[z416,z1,z3,z15,z5,z6]),(0,[z0,z1,z3,z108,z5,z917]),(0,[z0,z1,z4,z5,z1216,z6]),(0,[z0,z1,z3,z4,z5,z1217]),(0,[z0,z1,z3,z4,z5,z1218]),(0,[z0,z1219,z3,z4,z5,z6]),(0,[z1220,z1,z3,z4,z5,z6])],[(0,[z0,z3,z26,z5,z191,z6]),(0,[z0,z1,z4,z5,z1221,z6]),(0,[z266,z1,z318,z4,z5,z6]),(0,[z245,z0,z1,z4,z96,z6]),(0,[z1222,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z13,z5,z309])]],
   [[(0,[z45,z1,z3,z4,z5,z46]),(0,[z0,z51,z289,z4,z5,z6]),(0,[z174,z0,z1,z4,z5,z630])],[(0,[z49,z1,z3,z50,z5,z6]),(0,[z0,z210,z3,z50,z5,z6]),(0,[z68,z0,z3,z4,z5,z1047]),(0,[z333,z1,z3,z1139,z5,z6]),(0,[z198,z1,z3,z5,z6,z27])],[(0,[z266,z1,z3,z4,z5,z6]),(0,[z45,z1,z75,z4,z5,z46]),(0,[z0,z1,z3,z5,z167,z6]),(0,[z0,z1,z3,z980,z5,z6])],[(0,[z1223,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z165,z5,z370]),(0,[z164,z0,z89,z4,z90,z6])],[(0,[z0,z1,z3,z1224,z5,z6]),(0,[z0,z1,z3,z4,z5,z1225]),(0,[z1,z3,z34,z1136,z5,z6])],[(0,[z0,z1,z1226,z3,z5,z6]),(0,[z158,z1,z3,z400,z5,z6]),(0,[z0,z1,z3,z1227,z5,z6]),(0,[z1,z3,z106,z105,z5,z6])],[(0,[z1,z624,z58,z4,z5,z6]),(0,[z1,z58,z4,z5,z412,z6]),(0,[z0,z1,z3,z4,z5,z1017]),(0,[z0,z51,z4,z25,z5,z6]),(0,[z1228,z1,z3,z4,z5,z6]),(0,[z1,z3,z5,z443,z141,z6])],[(0,[z1,z3,z252,z15,z5,z6]),(0,[z254,z0,z1,z4,z96,z6]),(0,[z0,z1,z1229,z4,z5,z6]),(0,[z93,z0,z1,z3,z5,z892])]],
   [[(0,[z0,z1,z3,z1230,z5,z6]),(0,[z28,z0,z1,z3,z626,z6]),(0,[z0,z1,z318,z4,z5,z88]),(0,[z0,z52,z1,z41,z5,z6]),(0,[z1,z1231,z3,z4,z5,z6])],[(0,[z201,z175,z1,z3,z4,z5]),(0,[z0,z1,z3,z222,z5,z27]),(0,[z0,z1,z163,z3,z5,z1218])],[(0,[z213,z1,z3,z290,z5,z6]),(0,[z0,z1232,z3,z4,z5,z6]),(0,[z0,z51,z842,z4,z5,z6]),(0,[z164,z0,z3,z4,z90,z370]),(0,[z1,z3,z4,z5,z6,z1233])],[(0,[z45,z1,z3,z290,z5,z6]),(0,[z0,z1,z3,z4,z5,z1234]),(0,[z0,z1,z3,z4,z5,z88]),(0,[z0,z1,z4,z5,z223,z276]),(0,[z0,z1,z1235,z4,z5,z6]),(0,[z1,z381,z3,z105,z5,z6]),(0,[z1236,z1,z3,z4,z5,z6])],[(0,[z0,z1237,z1,z4,z5,z6]),(0,[z201,z0,z1,z4,z5,z96]),(0,[z109,z110,z1,z4,z96,z6]),(0,[z0,z1,z3,z791,z159,z6])],[(0,[z0,z1,z3,z400,z5,z370]),(0,[z109,z0,z1,z167,z96,z6]),(0,[z1,z3,z4,z5,z6,z1238])],[(0,[z0,z1,z97,z3,z4,z5]),(0,[z49,z1,z3,z742,z5,z6]),(0,[z0,z29,z3,z26,z5,z6]),(0,[z1,z3,z106,z26,z5,z6]),(0,[z0,z1,z256,z4,z5,z7]),(0,[z0,z1,z3,z34,z5,z128])],[(0,[z0,z1,z3,z1239,z5,z6]),(0,[z0,z1,z256,z5,z6,z27]),(0,[z33,z0,z3,z4,z5,z63]),(0,[z28,z0,z1,z3,z644,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 460).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 920).take 236) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1156)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [460, 460, 236] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 135).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 135).take 121).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [135, 121] = true :=
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

end PEqualNP.Outside.L_meta_36737

theorem PEqualNP.Outside.L_meta_36737 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4006144136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4006144136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36737.solve