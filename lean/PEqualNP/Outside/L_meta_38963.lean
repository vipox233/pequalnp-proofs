import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38963

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
  Nat.testBit (4276809448 * 2 ^ 32 + 4241018056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0xe80113231bc48d22#64 ++ 0xf40089918de24691#64 ++ 0xf5833f673fc49d27#64 ++ 0xfac19fb39fe24e93#64 : BitVec 256),
   (0x100448084401304d#64 ++ 0x0802240422009826#64 ++ 0xef0cc898c607ffff#64 ++ 0xf786644c6303ffff#64 : BitVec 256),
   (0xa030b0e0a8d8c630#64 ++ 0x50185870546c6318#64 ++ 0xdff0f0e0f9f8e639#64 ++ 0x6ff878707cfc731c#64 : BitVec 256),
   (0xc05b00f5016e0780#64 ++ 0x602d807a80b703c0#64 ++ 0xbeff00ff01ff07c1#64 ++ 0xdf7f807f80ff83e0#64 : BitVec 256),
   (0x00effd0001b7f801#64 ++ 0x8077fe8000dbfc00#64 ++ 0x7effff0001fff801#64 ++ 0x3f7fff8000fffc00#64 : BitVec 256),
   (0x017eeedef6000000#64 ++ 0x00bf776f7b000000#64 ++ 0xfd7ffffffe000000#64 ++ 0xfebfffffff000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [8, 1]⟩, ⟨.and, [7, 3]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [11, 4]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x10f3370001f80000 0x08799b8000fc0000

def z1 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xfd7ffffffe000000 0xfebfffffff000000

def z2 : W := mkw 0x100448084401304d 0x0802240422009826 0xef0cc898c607ffff 0xf786644c6303ffff

def z3 : W := mkw 0xa01000e0a8480630 0x5008007054240318 0x810000e0f8000638 0x408000707c00031c

def z4 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xdff0f0e0f9f8e639 0x6ff878707cfc731c

def z5 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xbeff00ff01ff07c1 0xdf7f807f80ff83e0

def z6 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xf5833f673fc49d27 0xfac19fb39fe24e93

def z7 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x7effff0001fff801 0x3f7fff8000fffc00

def z8 : W := mkw 0xc04b0035016e0780 0x6025801a80b703c0 0x228f001f01ff07c1 0x9147800f80ff83e0

def z9 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x5ef3f70001f8e001 0x2f79fb8000fc7000

def z10 : W := mkw 0x280013021a808822 0x940009810d404411 0xe5003f003e049d27 0xf2801f801f024e93

def z11 : W := mkw 0x40effd1501b7f981 0xa077fe8a80dbfcc0 0x7effff1f01fff9c1 0xbf7fff8f80fffce0

def z12 : W := mkw 0x0000020212000000 0x0000010109000000 0xf5033f673e000000 0xfa819fb39f000000

def z13 : W := mkw 0x011002def6000000 0x0088016f7b000000 0x810000fffe000000 0xc080007fff000000

def z14 : W := mkw 0xa000102008d8c630 0x50000810046c6318 0x0280000001f8e639 0x0140000000fc731c

def z15 : W := mkw 0xa17efefefed8c630 0x50bf7f7f7f6c6318 0xfffffffffff8e639 0xfffffffffffc731c

def z16 : W := mkw 0xb034f8e8ecd9f67d 0x581a7c74766cfb3e 0xfffcf8f8ffffffff 0xfffe7c7c7fffffff

def z17 : W := mkw 0xe07bb0f5a9fec7b0 0x703dd87ad4ff63d8 0x10f3306739f80000 0x087998339cfc0000

def z18 : W := mkw 0xe81002f71a4807a2 0x7408017b8d2403d1 0x810000ff3e0007e6 0xc080007f9f0003f3

def z19 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0x897cc0fffe000000 0xc4be607fff000000

def z20 : W := mkw 0x0020b0000090c000 0x0010580000486000 0x5ef0f00001f8e001 0x2f78780000fc7000

def z21 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xff7ffffffe07ffff 0xffbfffffff03ffff

def z22 : W := mkw 0x10cf4d084527384d 0x8867a68422939c26 0xef0fcf98c607ffff 0xf787e7cc6303ffff

def z23 : W := mkw 0x017feedef7260000 0x00bff76f7b930000 0xffffffffffff0001 0xffffffffffff8000

def z24 : W := mkw 0x00a4ec0000117001 0x005276000008b800 0x0000c00000006000 0x0000600000003000

def z25 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0xffffff98c7ffffff 0xffffffcc63ffffff

def z26 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0x1083376739c00000 0x08419bb39ce00000

def z27 : W := mkw 0x004b000001260000 0x0025800000930000 0x10f3000001f80000 0x0879800000fc0000

def z28 : W := mkw 0xe07bb0f5a9fec7b0 0x703dd87ad4ff63d8 0xfffff0fff9ffe7f9 0xfffff87ffcfff3fc

def z29 : W := mkw 0xe881112109f7fd23 0xf440889084fbfe91 0x0280000001fffd27 0x0140000000fffe93

def z30 : W := mkw 0x004f480001273001 0x0027a40000939800 0x7effc80001fff801 0x3f7fe40000fffc00

def z31 : W := mkw 0x417feedff7260180 0x20bff76ffb9300c0 0xfd7ffffffe0701c0 0xfebfffffff0380e0

def z32 : W := mkw 0x005a02d612000000 0x002d016b09000000 0xfd7f3fff3e000000 0xfebf9fff9f000000

def z33 : W := mkw 0x00cf4d0001273801 0x8067a68000939c00 0x200f0f0000071800 0x1007878000038c00

def z34 : W := mkw 0x0000020212000000 0x0000010109000000 0x810000673e000000 0xc08000339f000000

def z35 : W := mkw 0x0000000000000000 0x0000000000000000 0xae0c0098000707c1 0xd706004c000383e0

def z36 : W := mkw 0x100448084401304d 0x0802240422009826 0x4100c800c600f83e 0x2080640063007c1f

def z37 : W := mkw 0x006eec0000000000 0x0037760000000000 0x7c7fff0000000000 0x3e3fff8000000000

def z38 : W := mkw 0xc01000f500480780 0x6008007a802403c0 0x800000ff000007c0 0xc000007f800003e0

def z39 : W := mkw 0x0000000000000000 0x0000000000000000 0xe500080006049d27 0xf280040003024e93

def z40 : W := mkw 0xa01000e0a8480630 0x5008007054240318 0xcf00c0e0f800e639 0x678060707c00731c

def z41 : W := mkw 0x4801030313040902 0xa400818189820481 0xf5033f673e041906 0xfa819fb39f020c83

def z42 : W := mkw 0xa000102008c08420 0x5000081004604210 0xd580306039c08421 0x6ac018301ce04210

def z43 : W := mkw 0xe831b3e3bbdccf32 0xf418d9f1ddee6799 0xfff3ffe7fffcff3f 0xfff9fff3fffe7f9f

def z44 : W := mkw 0x114e4e1e5601304d 0x08a7270f2b009826 0x200f0f1f060719c6 0x9007878f83038ce3

def z45 : W := mkw 0x105e48dc442b32cd 0x082f246e22159966 0x0a7cc098c03b62d8 0x053e604c601db16c

def z46 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x1af0f0e0f9f86218 0x0d7878707cfc310c

def z47 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z48 : W := mkw 0x100448084401304d 0x0802240422009826 0xae0cc098c00767d9 0xd706604c6003b3ec

def z49 : W := mkw 0x017eecdce4000000 0x00bf766e72000000 0x087cc098c0000000 0x043e604c60000000

def z50 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0x0080000001c49d27 0x0040000000e24e93

def z51 : W := mkw 0x005a00d4002a0280 0x002d006a00150140 0x0a7c0098003b02c0 0x053e004c001d8160

def z52 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x10f3006701f80000 0x0879803380fc0000

def z53 : W := mkw 0x404b001501260180 0x2025800a809300c0 0x3eff001f01ff01c1 0x9f7f800f80ff80e0

def z54 : W := mkw 0x0001110001848800 0x8000888000c24400 0x74833f0001c49801 0x3a419f8000e24c00

def z55 : W := mkw 0x00eeec0000337001 0x007776000019b800 0x0a7cc000003b6000 0x053e6000001db000

def z56 : W := mkw 0x100448084401304d 0x0802240422009826 0x200c0818060719c6 0x9006040c03038ce3

def z57 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xfd7ffffffe0719c6 0xfebfffffff038ce3

def z58 : W := mkw 0xa17eeefefe480630 0x50bf777f7f240318 0xfd7ffffffe000638 0xfebfffffff00031c

def z59 : W := mkw 0x00a4fd000091f801 0x80527e800048fc00 0x4000ff000000f800 0x20007f8000007c00

def z60 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x10f0306039f80000 0x087818301cfc0000

def z61 : W := mkw 0xc17fecfde56e0780 0x60bff67ef2b703c0 0xbeffc0ffc1ff07c1 0xdf7fe07fe0ff83e0

def z62 : W := mkw 0xd05f48fd456f37cd 0x682fa47ea2b79be6 0xffffc8ffc7ffffff 0xffffe47fe3ffffff

def z63 : W := mkw 0x004a001400220080 0x0025000a00110040 0x000c0018000300c0 0x0006000c00018060

def z64 : W := mkw 0xe831b1e1a9dccf32 0xf418d8f0d4ee6799 0xdff0f0e0f9fcff3f 0x6ff878707cfe7f9f

def z65 : W := mkw 0x497fefdff7040902 0xa4bff7effb820481 0xfd7ffffffe041906 0xfebfffffff020c83

def z66 : W := mkw 0x017eeedef6013001 0x00bf776f7b009800 0xff7ffffffe07f801 0xffbfffffff03fc00

def z67 : W := mkw 0xc001002101440500 0x6000801080a20280 0xb483006701c40501 0xda41803380e20280

def z68 : W := mkw 0xa07ab0f4a8d8c630 0x503d587a546c6318 0xfffff0fff9f8e639 0xfffff87ffcfc731c

def z69 : W := mkw 0x801000e000480600 0x4008007000240300 0x9ef000e001f80601 0x4f78007000fc0300

def z70 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0x7effff98c1fffad9 0x3f7fffcc60fffd6c

def z71 : W := mkw 0x4801030313040902 0xa400818189820481 0x20030f0706041906 0x9001878383020c83

def z72 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0x1073376738000000 0x08399bb39c000000

def z73 : W := mkw 0xe8efff231bf7fd23 0xf477ff918dfbfe91 0xffffff673ffffd27 0xffffffb39ffffe93

def z74 : W := mkw 0xa0fffde0a9fffe31 0xd07ffef054ffff18 0x7effff6039fff801 0x3f7fffb01cfffc00

def z75 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0x818000673fc49d27 0xc0c000339fe24e93

def z76 : W := mkw 0x100000000001304d 0x0800000000009826 0x020000000007ffff 0x010000000003ffff

def z77 : W := mkw 0xe85b13f71bee8fa2 0xf42d89fb8df747d1 0x10f3376739f80000 0x08799bb39cfc0000

def z78 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xff7ffffffe0362d8 0xffbfffffff01b16c

def z79 : W := mkw 0xc0010021016e0780 0x6000801080b703c0 0xae8c009801ff07c1 0xd746004c00ff83e0

def z80 : W := mkw 0x0030a2c2b2000000 0x0018516159000000 0xfd73ffe7fe000000 0xfeb9fff3ff000000

def z81 : W := mkw 0x0004480844000000 0x0002240422000000 0x4100c800c6000000 0x2080640063000000

def z82 : W := mkw 0xe85b13f71bee8fa2 0xf42d89fb8df747d1 0xbeff37ff39ff07c1 0xdf7f9bff9cff83e0

def z83 : W := mkw 0x004b000001260000 0x0025800000930000 0xbeff009801ff07c1 0xdf7f804c00ff83e0

def z84 : W := mkw 0x4801010101040902 0xa400808080820481 0x0000000000041906 0x0000000000020c83

def z85 : W := mkw 0xc01000f500480780 0x6008007a802403c0 0x0000006700000000 0x0000003380000000

def z86 : W := mkw 0x005a00d4002a0280 0x002d006a00150140 0xbe7f00ff003b02c0 0xdf3f807f801d8160

def z87 : W := mkw 0xe831b3e3bbdccf32 0xf418d9f1ddee6799 0x10f3376739f80000 0x08799bb39cfc0000

def z88 : W := mkw 0x8030a0e0a0584610 0x40185070502c2308 0x9ef0c0e0c1f86619 0x4f78607060fc330c

def z89 : W := mkw 0x0081110001b7f801 0x8040888000dbfc00 0x0280000001fff801 0x0140000000fffc00

def z90 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xfff0f8e0fffcff3f 0xfff87c707ffe7f9f

def z91 : W := mkw 0x004b000001260000 0x0025800000930000 0x3eff000001ff0001 0x1f7f800000ff8000

def z92 : W := mkw 0xc0fffdf501ffff81 0xe07ffefa80ffffc0 0xfeffffff01ffffc1 0xff7fffff80ffffe0

def z93 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xff7ffffffe00e639 0xffbfffffff00731c

def z94 : W := mkw 0x11144adef601304d 0x088a256f7b009826 0xef0cc8fffe07ffff 0xf786647fff03ffff

def z95 : W := mkw 0x2030b0c0a898c230 0x10185860544c6118 0x4b70f080f838e238 0x25b878407c1c711c

def z96 : W := mkw 0xe830b2e3bad8c732 0x74185971dd6c6399 0xdff0f0e7fff8e73f 0xeff87873fffc739f

def z97 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0x7fffff00c7fff83f 0x3fffff8063fffc1f

def z98 : W := mkw 0x100448084401304d 0x0802240422009826 0x2a0cc898c6077bde 0x9506644c6303bdef

def z99 : W := mkw 0x01ffffdef7b7f801 0x80ffffef7bdbfc00 0xfffffffffffff801 0xfffffffffffffc00

def z100 : W := mkw 0x100000084400004c 0x0800000422000026 0x81000098c60007fe 0xc080004c630003ff

def z101 : W := mkw 0x014a061612000000 0x00a5030b09000000 0x0003070700000000 0x0001838380000000

def z102 : W := mkw 0xc0db11f501ffff81 0xe06d88fa80ffffc0 0xbeff00ff01ffffc1 0xdf7f807f80ffffe0

def z103 : W := mkw 0x00a1b10001b7f801 0x8050d88000dbfc00 0x5ef0f00001fff801 0x2f78780000fffc00

def z104 : W := mkw 0x0004480000013001 0x0002240000009800 0x6e0cc8000007f801 0x370664000003fc00

def z105 : W := mkw 0x0004480844000000 0x0002240422000000 0xed0cc898c6000000 0xf686644c63000000

def z106 : W := mkw 0xb17efefefed9f67d 0x58bf7f7f7f6cfb3e 0xffffffffffffffff 0xffffffffffffffff

def z107 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xfd7ffffffe00f83e 0xfebfffffff007c1f

def z108 : W := mkw 0xd0fffdfd45ffffcd 0xe87ffefea2ffffe6 0xffffffffc7ffffff 0xffffffffe3ffffff

def z109 : W := mkw 0xc17feefff76e0780 0x60bff77ffbb703c0 0xffffffffffff07c1 0xffffffffffff83e0

def z110 : W := mkw 0xa0fffde0a9fffe31 0xd07ffef054ffff18 0xffffffe0f9fffe39 0x7ffffff07cffff1c

def z111 : W := mkw 0xe80002231a400522 0x740001118d200291 0x810000673e000526 0xc08000339f000293

def z112 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0x30833f673fc41906 0x98419fb39fe20c83

def z113 : W := mkw 0xa030b2e2bad8c630 0x501859715d6c6318 0xfff3ffe7fff8e639 0xfff9fff3fffc731c

def z114 : W := mkw 0x0000000000000000 0x0000000000000000 0xcf00c080c000e639 0x678060406000731c

def z115 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x30ff007f01ff01c0 0x987f803f80ff80e0

def z116 : W := mkw 0x0000000000000000 0x0000000000000000 0xa400000000040501 0xd200000000020280

def z117 : W := mkw 0x3024f808ec91f07d 0x18127c047648f83e 0xef0cf898fe07ffff 0xf7867c4c7f03ffff

def z118 : W := mkw 0xe801112109dccf32 0xf400889084ee6799 0x0280000001fcff3f 0x0140000000fe7f9f

def z119 : W := mkw 0x100448084401304d 0x0802240422009826 0x0a0cc098c00362d8 0x0506604c6001b16c

def z120 : W := mkw 0x00effd0001b6c800 0x8077fe8000db6400 0x7cffff0001f80000 0x3e7fff8000fc0000

def z121 : W := mkw 0x0020b0000090c000 0x0010580000486000 0xdff0f080c1f8e639 0x6ff8784060fc731c

def z122 : W := mkw 0x004b110001a68800 0x8025888000d34400 0x7eff3f0001ff9801 0x3f7f9f8000ffcc00

def z123 : W := mkw 0x8030a0e0a0480600 0x4018507050240300 0xdff0f0e0f9f80601 0x6ff878707cfc0300

def z124 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x3eff370001ff0001 0x1f7f9b8000ff8000

def z125 : W := mkw 0x2020b000a890c030 0x1010580054486018 0xcf00f080f800e639 0x678078407c00731c

def z126 : W := mkw 0x100448084401304d 0x0802240422009826 0xcf00c880c600fe3f 0x6780644063007f1f

def z127 : W := mkw 0xe85b13f71bee8fa2 0xf42d89fb8df747d1 0xffff3fff3fff9fe7 0xffff9fff9fffcff3

def z128 : W := mkw 0x2020b000a890c030 0x1010580054486018 0x4100f000f800e038 0x208078007c00701c

def z129 : W := mkw 0x404b001501260180 0x2025800a809300c0 0x200f001f000701c0 0x9007800f800380e0

def z130 : W := mkw 0xa17efefefec08420 0x50bf7f7f7f604210 0xfdffffffffc08421 0xfeffffffffe04210

def z131 : W := mkw 0xd00548294545354d 0x6802a414a2a29aa6 0xff8fc8ffc7c7ffff 0xffc7e47fe3e3ffff

def z132 : W := mkw 0x00a5fd000195f801 0x8052fe8000cafc00 0x7483ff0001c4f801 0x3a41ff8000e27c00

def z133 : W := mkw 0xf801132b5fc48d6e 0xfc008995afe246b7 0xf5833fffffc49fff 0xfac19fffffe24fff

def z134 : W := mkw 0x100448084401304d 0x0802240422009826 0xae0c089806071fc7 0xd706044c03038fe3

def z135 : W := mkw 0xe831b3e3bbc48d22 0xf418d9f1dde24691 0xfdf3ffe7ffc49d27 0xfef9fff3ffe24e93

def z136 : W := mkw 0x0004480844000000 0x0002240422000000 0xef0cc898c60707c1 0xf786644c630383e0

def z137 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xfffcf0f8f9ffe7f9 0xfffe787c7cfff3fc

def z138 : W := mkw 0x0000000000000000 0x0000000000000000 0x4e00c0000000e001 0x2700600000007000

def z139 : W := mkw 0xe8a5ff231bd5fd23 0xf452ff918deafe91 0xf583ff673fc4fd27 0xfac1ffb39fe27e93

def z140 : W := mkw 0x00cb050001260800 0x8065828000930400 0x0003070000000000 0x0001838000000000

def z141 : W := mkw 0xb01448e8ec49367d 0x580a247476249b3e 0xef0cc8f8fe07ffff 0xf786647c7f03ffff

def z142 : W := mkw 0x006bb00001b6c000 0x0035d80000db6000 0x7efff00001ffe001 0x3f7ff80000fff000

def z143 : W := mkw 0x000010000090c000 0x0000080000486000 0x0280000001f8e001 0x0140000000fc7000

def z144 : W := mkw 0xd0054829456f37cd 0x6802a414a2b79be6 0xef8cc898c7ffffff 0xf7c6644c63ffffff

def z145 : W := mkw 0xf8055b2b5fc5bd6f 0xfc02ad95afe2deb7 0xff8fffffffc7ffff 0xffc7ffffffe3ffff

def z146 : W := mkw 0xc000002100480780 0x60000010802403c0 0x00000000000007c0 0x00000000000003e0

def z147 : W := mkw 0xe97fffffffdccf32 0xf4bfffffffee6799 0xfffffffffffcff3f 0xfffffffffffe7f9f

def z148 : W := mkw 0x006eec0844000000 0x0037760422000000 0xfd7fff98c6000000 0xfebfffcc63000000

def z149 : W := mkw 0x4800020312000102 0x2400010189000081 0x0000000706000106 0x8000000383000083

def z150 : W := mkw 0xf80559294dc5bd6f 0xfc02ac94a6e2deb7 0xef8cc898c7c7ffff 0xf7c6644c63e3ffff

def z151 : W := mkw 0x217efedefe90c030 0x10bf7f6f7f486018 0xfd7ffffffe00e038 0xfebfffffff00701c

def z152 : W := mkw 0x017aa6def6000000 0x00bd536f7b000000 0x917337fffe000000 0xc8b99bffff000000

def z153 : W := mkw 0xe85b13f71bc48d22 0xf42d89fb8de24691 0xfdff3fff3fc49d27 0xfeff9fff9fe24e93

def z154 : W := mkw 0xc11002fff6480780 0x6088017ffb2403c0 0x810000fffe0007c0 0xc080007fff0003e0

def z155 : W := mkw 0x00a4fd000091f801 0x80527e800048fc00 0x5ef0ff0001f8f801 0x2f787f8000fc7c00

def z156 : W := mkw 0xf801112109c5bd6f 0xfc00889084e2deb7 0x0280000001c7ffff 0x0140000000e3ffff

def z157 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xd5f0306039f88421 0x6af818301cfc4210

def z158 : W := mkw 0xc801032313440d02 0xe400819189a20681 0xb4830f6707c41d07 0xda4187b383e20e83

def z159 : W := mkw 0x005a00d400000000 0x002d006a00000000 0x087c009800000000 0x043e004c00000000

def z160 : W := mkw 0x58054b0b5705394f 0xac02a585ab829ca7 0xef0fcf9fc607ffff 0xf787e7cfe303ffff

def z161 : W := mkw 0xa11002fefe480630 0x5088017f7f240318 0x810000fffe000638 0xc080007fff00031c

def z162 : W := mkw 0x680113031b848922 0xb40089818dc24491 0x61033f073e049926 0xb0819f839f024c93

def z163 : W := mkw 0x0020a000a0104010 0x0010500050082008 0x0000c000c0006018 0x000060006000300c

def z164 : W := mkw 0xe9fffffffff7fd23 0xf4fffffffffbfe91 0xfffffffffffffd27 0xfffffffffffffe93

def z165 : W := mkw 0xc17feefff76e0780 0x60bff77ffbb703c0 0xfdfffffffff80000 0xfefffffffffc0000

def z166 : W := mkw 0xe01000f5a84807b0 0x7008007ad42403d8 0x810000fff80007f8 0xc080007ffc0003fc

def z167 : W := mkw 0xe8ebb7231bf6cd22 0xf475db918dfb6691 0xf5f33f673ffc9d27 0xfaf99fb39ffe4e93

def z168 : W := mkw 0x00eefd000091f801 0x80777e800048fc00 0x7c7fff000000f800 0x3e3fff8000007c00

def z169 : W := mkw 0x100448084401304d 0x0802240422009826 0x6f0cc800c607f83f 0x378664006303fc1f

def z170 : W := mkw 0xe8effd2109f7fd23 0xf477fe9084fbfe91 0x7effff0001fffd27 0x3f7fff8000fffe93

def z171 : W := mkw 0x01feeedef6337001 0x00ff776f7b19b800 0xff7ffffffe3b6000 0xffbfffffff1db000

def z172 : W := mkw 0x1034e8c8e401304d 0x081a746472009826 0xff7cf8f8fe07ffff 0xffbe7c7c7f03ffff

def z173 : W := mkw 0x20effd00a9b7f831 0x9077fe8054dbfc18 0x7fffff00f9fff839 0x3fffff807cfffc1c

def z174 : W := mkw 0xc04b003501660580 0x6025801a80b302c0 0xb48f007f01c705c1 0xda47803f80e382e0

def z175 : W := mkw 0x0000000000000000 0x0000000000000000 0xe500080006000000 0xf280040003000000

def z176 : W := mkw 0x00feecd4003b7281 0x007f766a001db940 0x0a7cc098003b62c0 0x053e604c001db160

def z177 : W := mkw 0xa0effd2009fffe31 0xd077fe9004ffff18 0x7effff0001fffe39 0x3f7fff8000ffff1c

def z178 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0x0080000001c00000 0x0040000000e00000

def z179 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x0af0c080c1f8e639 0x0578604060fc731c

def z180 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0xfeffff9801ffffc1 0xff7fffcc00ffffe0

def z181 : W := mkw 0x01feecdce4337001 0x00ff766e7219b800 0x0a7cc098c03b6000 0x053e604c601db000

def z182 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0xffffff0007fffd27 0xffffff8003fffe93

def z183 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0xf5733f673e000000 0xfab99fb39f000000

def z184 : W := mkw 0xe8fffff71bffffa3 0xf47ffffb8dffffd1 0xffffffff3fffffe7 0xffffffff9ffffff3

def z185 : W := mkw 0x011002def6000000 0x0088016f7b000000 0xf5033ffffe000000 0xfa819fffff000000

def z186 : W := mkw 0x01ffffd6b3b7f801 0x80ffffeb59dbfc00 0x7effff6739fff801 0x3f7fffb39cfffc00

def z187 : W := mkw 0x0020a000a0000000 0x0010500050000000 0x4100f000f8000000 0x208078007c000000

def z188 : W := mkw 0xe97fffffffc48d22 0xf4bfffffffe24691 0xfdffffffffc49d27 0xfeffffffffe24e93

def z189 : W := mkw 0xe001102109c48520 0x7000881084e24290 0xf583306739c48521 0xfac198339ce24290

def z190 : W := mkw 0x015e4edef6000000 0x00af276f7b000000 0xa10f0ffffe000000 0xd08787ffff000000

def z191 : W := mkw 0x0000020212000000 0x0000010109000000 0xf5033f673e049d27 0xfa819fb39f024e93

def z192 : W := mkw 0x0000000000000000 0x0000000000000000 0x4100c000c000e038 0x208060006000701c

def z193 : W := mkw 0xd05b00fd456e07cc 0x682d807ea2b703e6 0xbfff00ffc7ff07ff 0xdfff807fe3ff83ff

def z194 : W := mkw 0xc0010021016e0780 0x6000801080b703c0 0xb683006701ff07c1 0xdb41803380ff83e0

def z195 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xd583376739c08421 0x6ac19bb39ce04210

def z196 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x1afff70001fb6000 0x0d7ffb8000fdb000

def z197 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x1aff00ff01fb02c0 0x0d7f807f80fd8160

def z198 : W := mkw 0xe80002231a400522 0x740001118d200291 0x0000006738000000 0x000000339c000000

def z199 : W := mkw 0x0000020212000000 0x0000010109000000 0x1003376738000000 0x08019bb39c000000

def z200 : W := mkw 0xe030b0f5a8d8c7b0 0x7018587ad46c63d8 0xdff0f0fff9f8e7f9 0xeff8787ffcfc73fc

def z201 : W := mkw 0x00cb110001b7f801 0x8065888000dbfc00 0x3eff000001fff801 0x1f7f800000fffc00

def z202 : W := mkw 0x4801030313040902 0xa400818189820481 0xe5030f0706049d27 0xf281878383024e93

def z203 : W := mkw 0xa000102008c08420 0x5000081004604210 0x0080000001c08421 0x0040000000e04210

def z204 : W := mkw 0x0030a0c0a0184210 0x00185060500c2108 0x0a70c080c0386218 0x05386040601c310c

def z205 : W := mkw 0x014e4e1e56000000 0x00a7270f2b000000 0xf50f3f7f3e000000 0xfa879fbf9f000000

def z206 : W := mkw 0x297effdefe808822 0x94bf7fef7f404411 0xfd7ffffffe009826 0xfebfffffff004c13

def z207 : W := mkw 0x10eeec084433704d 0x087776042219b826 0xef7cc898c63fffff 0xf7be644c631fffff

def z208 : W := mkw 0xc05b02f7136e0780 0x602d817b89b703c0 0xffff3fff3fff07c1 0xffff9fff9fff83e0

def z209 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0xdd73f7e7f8000000 0x6eb9fbf3fc000000

def z210 : W := mkw 0xe8efff231bf7fd23 0xf477ff918dfbfe91 0x7effff6739fff801 0x3f7fffb39cfffc00

def z211 : W := mkw 0x100448084401304d 0x0802240422009826 0x4b0cc898c603fafe 0x2586644c6301fd7f

def z212 : W := mkw 0x0004480000000000 0x0002240000000000 0x6c0cc80000000000 0x3606640000000000

def z213 : W := mkw 0xf8044a2b5e41356f 0x7c022515af209ab7 0xef0cc8fffe07ffff 0xf786647fff03ffff

def z214 : W := mkw 0x0030a0c0a0000000 0x0018506050000000 0xdd70f0e0f8000000 0x6eb878707c000000

def z215 : W := mkw 0x0000000000000000 0x0000000000000000 0x2e0c000000070001 0x1706000000038000

def z216 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xff7ffffffe0707c1 0xffbfffffff0383e0

def z217 : W := mkw 0xa030a0e0a8584630 0x50185070542c2318 0x8b70c0e0f8386638 0x45b860707c1c331c

def z218 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000049d27 0x0000000000024e93

def z219 : W := mkw 0xe87bb3f7bbfecfb2 0xf43dd9fbddff67d9 0xffffffffffffffff 0xffffffffffffffff

def z220 : W := mkw 0x0000000000000000 0x0000000000000000 0xef0cc098c007e7f9 0xf786604c6003f3fc

def z221 : W := mkw 0x100448000001304d 0x0802240000009826 0x6e0cc8000007ffff 0x370664000003ffff

def z222 : W := mkw 0x014e4e1e56000000 0x00a7270f2b000000 0xed0fcf9fc6000000 0xf687e7cfe3000000

def z223 : W := mkw 0x100000084400004c 0x0800000422000026 0x00000098c00002d8 0x0000004c6000016c

def z224 : W := mkw 0xd05b00f5016f37cd 0x682d807a80b79be6 0xbeff00ff01ffffff 0xdf7f807f80ffffff

def z225 : W := mkw 0x001000c000000000 0x0008006000000000 0x9c7000e000000000 0x4e38007000000000

def z226 : W := mkw 0x504f481d452731cd 0x2827a40ea29398e6 0x200f081f060719c6 0x9007840f83038ce3

def z227 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x0afc009801ff07c1 0x057e004c00ff83e0

def z228 : W := mkw 0x801000e000480600 0x4008007000240300 0x800000e000000600 0x4000007000000300

def z229 : W := mkw 0x00ebb50001b7f801 0x8075da8000dbfc00 0x12f3370001fff801 0x09799b8000fffc00

def z230 : W := mkw 0xe800002108400522 0x7400001084200291 0x0000000000000526 0x0000000000000293

def z231 : W := mkw 0x1081110001b7f84d 0x8840888000dbfc26 0x0280000001ffffff 0x0140000000ffffff

def z232 : W := mkw 0x100000084400004c 0x0800000422000026 0xcf00c098c600e7ff 0xe780604c630073ff

def z233 : W := mkw 0xf800022b5e40056e 0x7c000115af2002b7 0x810000fffe0007fe 0xc080007fff0003ff

def z234 : W := mkw 0xc081112101ffff81 0xe040889080ffffc0 0x0280000001ffffc1 0x0140000000ffffe0

def z235 : W := mkw 0x005a00d400000000 0x002d006a00000000 0x1073006700000000 0x0839803380000000

def z236 : W := mkw 0x006efc000090c000 0x00377e0000486000 0x7effff0001f8e001 0x3f7fff8000fc7000

def z237 : W := mkw 0x0124ee0af6000000 0x009277057b000000 0xf503ff67fe000000 0xfa81ffb3ff000000

def z238 : W := mkw 0xa830b3e2bad8ce32 0xd41859f15d6c6719 0xdff0ffe0fff8fe3f 0x6ff87ff07ffc7f1f

def z239 : W := mkw 0x100000000001304d 0x0800000000009826 0x000000000000f83e 0x0000000000007c1f

def z240 : W := mkw 0x0124ec08e4000000 0x0092760472000000 0x0000c000c0000000 0x0000600060000000

def z241 : W := mkw 0xe031b0e1a9dcc730 0x7018d870d4ee6398 0xfff3f0e7f9fce739 0xfff9f873fcfe739c

def z242 : W := mkw 0xc07fecf5016e0780 0x603ff67a80b703c0 0xfeffffff01ff07c1 0xff7fffff80ff83e0

def z243 : W := mkw 0x01cf4f1e57273801 0x80e7a78f2b939c00 0x200f0f1f06071800 0x9007878f83038c00

def z244 : W := mkw 0x0004480844000000 0x0002240422000000 0x200c081806000000 0x9006040c03000000

def z245 : W := mkw 0x017efedef690c000 0x00bf7f6f7b486000 0xfffffffffff8e001 0xfffffffffffc7000

def z246 : W := mkw 0x00eeec0000337001 0x007776000019b800 0x7e7fff00003b6000 0x3f3fff80001db000

def z247 : W := mkw 0xe86fff231bc48d22 0xf437ff918de24691 0xfdffff673fc49d27 0xfeffffb39fe24e93

def z248 : W := mkw 0xa00012221ac08420 0x500009110d604210 0xf5833f673fc08421 0xfac19fb39fe04210

def z249 : W := mkw 0xc17ba6f7b36e0780 0x60bdd37bd9b703c0 0x10f3376739f80000 0x08799bb39cfc0000

def z250 : W := mkw 0xe81113e31bcc8f22 0xf40889f18de64791 0xfff33fe73ffc9f27 0xfff99ff39ffe4f93

def z251 : W := mkw 0x007aa0d4a0000000 0x003d506a50000000 0xfd7ff0fff8000000 0xfebff87ffc000000

def z252 : W := mkw 0x0000000000000000 0x0000000000000000 0x8e00008000000601 0x4700004000000300

def z253 : W := mkw 0x0020b0000090c000 0x0010580000486000 0x10f0300001f80000 0x0878180000fc0000

def z254 : W := mkw 0xa000102008d8c630 0x50000810046c6318 0x0080000001f80000 0x0040000000fc0000

def z255 : W := mkw 0x100448084401304d 0x0802240422009826 0x4300c800c607ffff 0x218064006303ffff

def z256 : W := mkw 0x0030a0c0a0000000 0x0018506050000000 0x0870c080c0000000 0x0438604060000000

def z257 : W := mkw 0xa030a0e0a8480630 0x5018507054240318 0xdd70f0e0f8000638 0x6eb878707c00031c

def z258 : W := mkw 0x40cf4d1501273981 0xa067a68a80939cc0 0x200f0f1f000719c0 0x9007878f80038ce0

def z259 : W := mkw 0x014e4e1e56000000 0x00a7270f2b000000 0x200f0f1f06000000 0x9007878f83000000

def z260 : W := mkw 0x016eee1ef6000000 0x00b7770f7b000000 0x610fff1ffe000000 0xb087ff8fff000000

def z261 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x12f3006701ff07c1 0x0979803380ff83e0

def z262 : W := mkw 0x00a5fd0001b7f801 0x8052fe8000dbfc00 0x4280ff0001fff801 0x21407f8000fffc00

def z263 : W := mkw 0xa17ab6f6bad8c630 0x50bd5b7b5d6c6318 0x10f3376739f80000 0x08799bb39cfc0000

def z264 : W := mkw 0x00cf4d0001273801 0x8067a68000939c00 0x3eff0f0001ff1801 0x1f7f878000ff8c00

def z265 : W := mkw 0x00eefc0000b3f001 0x00777e000059f800 0x5efcf00001fbe001 0x2f7e780000fdf000

def z266 : W := mkw 0x805a00f4006a0680 0x402d007a00350340 0x9efc00f801fb06c1 0x4f7e007c00fd8360

def z267 : W := mkw 0x0020a00000104000 0x0010500000082000 0x0a70c00000386000 0x05386000001c3000

def z268 : W := mkw 0xb00458284cc1b46d 0x58022c142660da36 0xff8cf8f8ffc7ffff 0xffc67c7c7fe3ffff

def z269 : W := mkw 0xf80113231bc5bd6f 0xfc0089918de2deb7 0xf7833f673fc7ffff 0xfbc19fb39fe3ffff

def z270 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x12f0306039f8e639 0x097818301cfc731c

def z271 : W := mkw 0x100448084401304d 0x0802240422009826 0x0a0cc098c007ffff 0x0506604c6003ffff

def z272 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0x7effff1807fff9c7 0xbf7fff8c03fffce3

def z273 : W := mkw 0x0001110001848800 0x8000888000c24400 0xf5833f0007c49d27 0xfac19f8003e24e93

def z274 : W := mkw 0x00effd0845b7f801 0x8077fe8422dbfc00 0xffffff98c7fff801 0xffffffcc63fffc00

def z275 : W := mkw 0x0030a0c0a0184210 0x00185060500c2108 0x0070000000380000 0x00380000001c0000

def z276 : W := mkw 0x005e48dc44000000 0x002f246e22000000 0xfd7fc8ffc6000000 0xfebfe47fe3000000

def z277 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x51f0f060f9f8e038 0x28f878307cfc701c

def z278 : W := mkw 0x100448084401304d 0x0802240422009826 0xcf0cc098c003e6f9 0x6786604c6001f37c

def z279 : W := mkw 0x0081010001273801 0x8040808000939c00 0x0000000000071800 0x0000000000038c00

def z280 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x5ef0f06039f8e001 0x2f7878301cfc7000

def z281 : W := mkw 0x015a02def6000000 0x00ad016f7b000000 0xbd7f00fffe000000 0xdebf807fff000000

def z282 : W := mkw 0x817eeefef6480600 0x40bf777f7b240300 0xfffffffffff80601 0xfffffffffffc0300

def z283 : W := mkw 0xa130b2fefed8c630 0x5098597f7f6c6318 0xdff0f0fffff8e639 0xeff8787ffffc731c

def z284 : W := mkw 0x10effd0001b7f84d 0x8877fe8000dbfc26 0x7effff0001ffffff 0x3f7fff8000ffffff

def z285 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x50f3ff0001f8f800 0x2879ff8000fc7c00

def z286 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000080006041906 0x9000040003020c83

def z287 : W := mkw 0xe821b323bbd4cd32 0xf410d991ddea6699 0xf583ff67ffc4fd3f 0xfac1ffb3ffe27e9f

def z288 : W := mkw 0xc000002100400500 0x6000001080200280 0x8000006700000500 0xc000003380000280

def z289 : W := mkw 0x0000000000000000 0x0000000000000000 0x74033f0000000000 0x3a019f8000000000

def z290 : W := mkw 0x0134eedef6000000 0x009a776f7b000000 0xc100fffffe000000 0xe0807fffff000000

def z291 : W := mkw 0x006fec0001260000 0x0037f60000930000 0x7effff0001ff0001 0x3f7fff8000ff8000

def z292 : W := mkw 0x0000000000000000 0x0000000000000000 0x81000080c0000638 0x408000406000031c

def z293 : W := mkw 0x0004480000013001 0x0002240000009800 0xef0cc880c007fe39 0x778664406003ff1c

def z294 : W := mkw 0x00eefd0000b3f801 0x80777e800059fc00 0x4a7cff00003bf800 0x253e7f80001dfc00

def z295 : W := mkw 0xc04b002101660500 0x6025801080b30280 0xbeff006701ff0501 0xdf7f803380ff8280

def z296 : W := mkw 0x005a00d400000000 0x002d006a00000000 0xbc7f00ff00000000 0xde3f807f80000000

def z297 : W := mkw 0xe97bb7f7bbc48d22 0xf4bddbfbdde24691 0xf5f33f673fc49d27 0xfaf99fb39fe24e93

def z298 : W := mkw 0xe85b11f509ee8fa2 0xf42d88fa84f747d1 0xbeff00ff01ff9fe7 0xdf7f807f80ffcff3

def z299 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0x51833f673fc09826 0x28c19fb39fe04c13

def z300 : W := mkw 0x00fffdc0a1bffa11 0x807ffee050dffd08 0x7effff80c1fffa19 0x3f7fffc060fffd0c

def z301 : W := mkw 0xa020b020a8d0c430 0x5010581054686218 0xd580f060f9c0e439 0x6ac078307ce0721c

def z302 : W := mkw 0x016eee0af6000000 0x00b777057b000000 0x7d7fff00fe000000 0x3ebfff807f000000

def z303 : W := mkw 0x001000d400000000 0x0008006a00000000 0x800000ff00000000 0xc000007f80000000

def z304 : W := mkw 0xa01000e0a8480630 0x5008007054240318 0x0000006038000000 0x000000301c000000

def z305 : W := mkw 0x017eecdce4000000 0x00bf766e72000000 0x7c7fff98c0000000 0x3e3fffcc60000000

def z306 : W := mkw 0x004b000001260000 0x0025800000930000 0x200f000000070000 0x1007800000038000

def z307 : W := mkw 0x0000100000808000 0x0000080000404000 0x5480300001c08001 0x2a40180000e04000

def z308 : W := mkw 0x280013021a808822 0x940009810d404411 0x41003f003e009826 0x20801f801f004c13

def z309 : W := mkw 0x117eecdce401304d 0x08bf766e72009826 0xef7cc898c607ffff 0xf7be644c6303ffff

def z310 : W := mkw 0xe801112109ee8fa2 0xf400889084f747d1 0x0280000001ff9fe7 0x0140000000ffcff3

def z311 : W := mkw 0x10a4fd084491f84d 0x88527e842248fc26 0xef0cff98c607ffff 0xf7867fcc6303ffff

def z312 : W := mkw 0xc001002101440500 0x6000801080a20280 0xf583086707c49d27 0xfac1843383e24e93

def z313 : W := mkw 0x100448084401304d 0x0802240422009826 0x0000c000c0006018 0x000060006000300c

def z314 : W := mkw 0x007eecc0a0000000 0x003f766050000000 0xfd7fffe0f8000000 0x7ebffff07c000000

def z315 : W := mkw 0x2020b000a890c030 0x1010580054486018 0x5ff0f000f9f8e039 0x2ff878007cfc701c

def z316 : W := mkw 0x00044a0a56000000 0x000225052b000000 0xfd0ffffffe000000 0xfe87ffffff000000

def z317 : W := mkw 0x017eeed6b2000000 0x00bf776b59000000 0x7c7fff6738000000 0x3e3fffb39c000000

def z318 : W := mkw 0x0000020212000000 0x0000010109000000 0x20030f0706000000 0x9001878383000000

def z319 : W := mkw 0x10eeec084433704d 0x087776042219b826 0x0a7cc098c03b62d8 0x053e604c601db16c

def z320 : W := mkw 0x0800030212000802 0x8400018109000401 0x00000f0006001806 0x0000078003000c03

def z321 : W := mkw 0x48efff0313b7f903 0xa477ff8189dbfc81 0x7effff0707fff907 0xbf7fff8383fffc83

def z322 : W := mkw 0x4001000101260180 0x20008000809300c0 0x00000000000701c0 0x00000000000380e0

def z323 : W := mkw 0x00efec0001377001 0x0077f600009bb800 0x3effc00001ff6001 0x1f7fe00000ffb000

def z324 : W := mkw 0x117eeedef600004c 0x08bf776f7b000026 0xfd7ffffffe0007fe 0xfebfffffff0003ff

def z325 : W := mkw 0x017fffdef7848800 0x80bfffef7bc24400 0xfdffffffffc49801 0xfeffffffffe24c00

def z326 : W := mkw 0x105e48dc4401304d 0x082f246e22009826 0xff7fc8ffc607ffff 0xffbfe47fe303ffff

def z327 : W := mkw 0x00cf4d0001273801 0x8067a68000939c00 0x6e0fcf000007f801 0x3707e7800003fc00

def z328 : W := mkw 0x0134eecaf6000000 0x009a77657b000000 0xdd70ffe0fe000000 0x6eb87ff07f000000

def z329 : W := mkw 0xe8ebb7231bf6cd22 0xf475db918dfb6691 0x10f3376739f80000 0x08799bb39cfc0000

def z330 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0xbc7f37ff38000000 0xde3f9bff9c000000

def z331 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0xffffff80c1fffe39 0x7fffffc060ffff1c

def z332 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xfd7ffffffe049d27 0xfebfffffff024e93

def z333 : W := mkw 0x00cf5d0001b7f801 0x8067ae8000dbfc00 0x228f0f0001fff801 0x1147878000fffc00

def z334 : W := mkw 0x1124ee0af601304d 0x089277057b009826 0xef0cff98fe07ffff 0xf7867fcc7f03ffff

def z335 : W := mkw 0x0000110000808800 0x8000088000404400 0x40003f0000009800 0x20001f8000004c00

def z336 : W := mkw 0xc0010021016e0780 0x6000801080b703c0 0x0280000001ff07c1 0x0140000000ff83e0

def z337 : W := mkw 0xd0010021016f37cd 0x6800801080b79be6 0x0280000001ffffff 0x0140000000ffffff

def z338 : W := mkw 0x404b001501260180 0x2025800a809300c0 0x0003000700000000 0x0001800380000000

def z339 : W := mkw 0x0021b1000194c800 0x8010d88000ca6400 0x7ef3ff0001fcf801 0x3f79ff8000fe7c00

def z340 : W := mkw 0xa034f8e0a8d9f631 0x501a7c70546cfb18 0xfffcf8e0f9fffe39 0x7ffe7c707cffff1c

def z341 : W := mkw 0x100448084401304d 0x0802240422009826 0xe500c800c604fd3f 0xf280640063027e9f

def z342 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x30ff3f0001ff1800 0x187f9f8000ff8c00

def z343 : W := mkw 0x005a00d400000000 0x002d006a00000000 0xbe7f00ff000707c1 0xdf3f807f800383e0

def z344 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xb4f3006701fc0501 0xda79803380fe0280

def z345 : W := mkw 0x0030a0c0a0000000 0x0018506050000000 0xdf70f0e0f800e639 0x6fb878707c00731c

def z346 : W := mkw 0xc01100e1016e0780 0x6008807080b703c0 0x9ef000e001ff07c1 0x4f78007000ff83e0

def z347 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x74f33f0001fc9801 0x3a799f8000fe4c00

def z348 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0x307f3f7f3e000000 0x983f9fbf9f000000

def z349 : W := mkw 0x0124ee0af6000000 0x009277057b000000 0x4100ff00fe000000 0x20807f807f000000

def z350 : W := mkw 0x005a00d4002a0280 0x002d006a00150140 0x0070000000380000 0x00380000001c0000

def z351 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0x497cff98fe000000 0x24be7fcc7f000000

def z352 : W := mkw 0xe8055b2b5fc48d22 0xf402ad95afe24691 0xfd8fffffffc49d27 0xfec7ffffffe24e93

def z353 : W := mkw 0xa081112009fffe31 0xd040889004ffff18 0x0280000001fffe39 0x0140000000ffff1c

def z354 : W := mkw 0x100000084400004c 0x0800000422000026 0xe5000898c6049fff 0xf280044c63024fff

def z355 : W := mkw 0x100000000001304d 0x0800000000009826 0x02000000000362d8 0x010000000001b16c

def z356 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xffff08ff07ff9fe7 0xffff847f83ffcff3

def z357 : W := mkw 0xc0ffecf5017f7781 0x607ff67a80bfbbc0 0xbeffc0ff01ff67c1 0xdf7fe07f80ffb3e0

def z358 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0xe580080007c49d27 0xf2c0040003e24e93

def z359 : W := mkw 0x015e4ede56000000 0x00af276f2b000000 0xbc7f0fff06000000 0xde3f87ff83000000

def z360 : W := mkw 0xc01100f5016e0780 0x6008807a80b703c0 0x828000ff01ff07c1 0xc140007f80ff83e0

def z361 : W := mkw 0x0001000001040000 0x0000800000820000 0x3483000001c40001 0x1a41800000e20000

def z362 : W := mkw 0x117eecdce401304d 0x08bf766e72009826 0x0a7cc098c00362d8 0x053e604c6001b16c

def z363 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0x1083376739c49d27 0x08419bb39ce24e93

def z364 : W := mkw 0x0000000000000000 0x0000000000000000 0x02000000000707c1 0x01000000000383e0

def z365 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0x20830f0707c49d27 0x9041878383e24e93

def z366 : W := mkw 0xd05f48fd456f37cd 0x682fa47ea2b79be6 0xbeffc0ffc1ff67d9 0xdf7fe07fe0ffb3ec

def z367 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x0afcc00001fff801 0x057e600000fffc00

def z368 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xff83ffe7ffc4ff3f 0xffc1fff3ffe27f9f

def z369 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xbcff00ff01f80000 0xde7f807f80fc0000

def z370 : W := mkw 0x100448084401304d 0x0802240422009826 0x0000080006001806 0x0000040003000c03

def z371 : W := mkw 0x017eeedef62a0280 0x00bf776f7b150140 0xff7ffffffe3b02c0 0xffbfffffff1d8160

def z372 : W := mkw 0x001000d400080280 0x0008006a00040140 0x00000098000002c0 0x0000004c00000160

def z373 : W := mkw 0x0000000000000000 0x0000000000000000 0xcd00c080c0000000 0x6680604060000000

def z374 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0x187ff7fff8000000 0x0c3ffbfffc000000

def z375 : W := mkw 0x0001130213848800 0x8000898109c24400 0xf5833f673fc49801 0xfac19fb39fe24c00

def z376 : W := mkw 0xe05b10f509ee87a0 0x702d887a84f743d0 0xffff30ff39ff87e1 0xffff987f9cffc3f0

def z377 : W := mkw 0xe97eeefffe400522 0x74bf777fff200291 0xfd7ffffffe000526 0xfebfffffff000293

def z378 : W := mkw 0xc17eeefff6480780 0x60bf777ffb2403c0 0xfd7ffffffe0007c0 0xfebfffffff0003e0

def z379 : W := mkw 0xa17ab6f6bad8c630 0x50bd5b7b5d6c6318 0xdff3f7e7f9f8e639 0x6ff9fbf3fcfc731c

def z380 : W := mkw 0xa034f8e8ecd8c630 0x501a7c74766c6318 0xfffcf8f8fff8e639 0xfffe7c7c7ffc731c

def z381 : W := mkw 0x100000000001304d 0x0800000000009826 0xe70008000607ffff 0xf38004000303ffff

def z382 : W := mkw 0x0030a0c0a0184210 0x00185060500c2108 0xdf70f0e0f8386218 0x6fb878707c1c310c

def z383 : W := mkw 0xf07ff8fdedfff7fd 0x783ffc7ef6fffbfe 0xfffff8ffffffffff 0xfffffc7fffffffff

def z384 : W := mkw 0x0130a2def6000000 0x0098516f7b000000 0xdd70f0fffe000000 0xeeb8787fff000000

def z385 : W := mkw 0xd05f48fd456f37cd 0x682fa47ea2b79be6 0xbeff08ff07ff1fc7 0xdf7f847f83ff8fe3

def z386 : W := mkw 0x1085590845b7f84d 0x8842ac8422dbfc26 0xef8cc898c7ffffff 0xf7c6644c63ffffff

def z387 : W := mkw 0xe80113231bdccf32 0xf40089918dee6799 0xf7833f673ffcff3f 0xfbc19fb39ffe7f9f

def z388 : W := mkw 0xb0fffde8edfffe7d 0xd87ffef476ffff3e 0xfffffff8ffffffff 0xfffffffc7fffffff

def z389 : W := mkw 0xa000102008c08420 0x5000081004604210 0x1080306039c00000 0x084018301ce00000

def z390 : W := mkw 0x005a00d4002a0280 0x002d006a00150140 0xae7c0098003f07c1 0xd73e004c001f83e0

def z391 : W := mkw 0xc17feefff7440500 0x60bff77ffba20280 0xfdffffffffc40501 0xfeffffffffe20280

def z392 : W := mkw 0xe80002231a400522 0x740001118d200291 0xf5033f673e000526 0xfa819fb39f000293

def z393 : W := mkw 0x80fffde001fffe01 0xc07ffef000ffff00 0xfeffffe001fffe01 0x7f7ffff000ffff00

def z394 : W := mkw 0xb000102008d9f67d 0x58000810046cfb3e 0x0280000001ffffff 0x0140000000ffffff

def z395 : W := mkw 0xe97bb7f7bbc48d22 0xf4bddbfbdde24691 0x10f3376739c00000 0x08799bb39ce00000

def z396 : W := mkw 0x100448084401304d 0x0802240422009826 0xed0cc898c600f83e 0xf686644c63007c1f

def z397 : W := mkw 0x200010000890c030 0x1000080004486018 0x000000000000e038 0x000000000000701c

def z398 : W := mkw 0xa020b020a8d8c630 0x50105810546c6318 0x4380f000f9f8e639 0x21c078007cfc731c

def z399 : W := mkw 0x801000e000480600 0x4008007000240300 0x10f0006001f80000 0x0878003000fc0000

def z400 : W := mkw 0xe84b13231be68d22 0xf42589918df34691 0xffff3f673fff9d27 0xffff9fb39fffce93

def z401 : W := mkw 0x0000000000000000 0x0000000000000000 0xb403006700000000 0xda01803380000000

def z402 : W := mkw 0xe88113231bf7fd23 0xf44089918dfbfe91 0xf7833f673ffffd27 0xfbc19fb39ffffe93

def z403 : W := mkw 0x0004480844013001 0x0002240422009800 0xef0cc898c607f801 0xf786644c6303fc00

def z404 : W := mkw 0x0000000844000000 0x0000000422000000 0x81000098c6000000 0xc080004c63000000

def z405 : W := mkw 0x0000000000000000 0x0000000000000000 0xac0c009800000000 0xd606004c00000000

def z406 : W := mkw 0x100000000001304d 0x0800000000009826 0xcf00c080c007ffff 0x678060406003ffff

def z407 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0xd580306039c49d27 0x6ac018301ce24e93

def z408 : W := mkw 0xa80013221ac08c22 0xd40009910d604611 0xd5803f603fc09c27 0x6ac01fb01fe04e13

def z409 : W := mkw 0x0001110001848800 0x8000888000c24400 0x0080000001c49801 0x0040000000e24c00

def z410 : W := mkw 0x01144adef6000000 0x008a256f7b000000 0xed0cc8fffe000000 0xf686647fff000000

def z411 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xff8f3fff3fc79fe7 0xffc79fff9fe3cff3

def z412 : W := mkw 0x011002d6b2000000 0x0088016b59000000 0x0000006738000000 0x000000339c000000

def z413 : W := mkw 0x100000084400004c 0x0800000422000026 0xaf0c0098c60707ff 0xd786004c630383ff

def z414 : W := mkw 0x805b00e0016e0600 0x402d807000b70300 0xbeff00e001ff0601 0x5f7f807000ff8300

def z415 : W := mkw 0xc001002101440500 0x6000801080a20280 0x0080000001c40501 0x0040000000e20280

def z416 : W := mkw 0xe81002e3ba480732 0x74080171dd240399 0x810000e7fe00073e 0xc0800073ff00039f

def z417 : W := mkw 0xa0b4fde0a8d9fe31 0xd05a7ef0546cff18 0xdff0ffe0f9f8fe39 0x6ff87ff07cfc7f1c

def z418 : W := mkw 0x017eeedef6184210 0x00bf776f7b0c2108 0xff7ffffffe386218 0xffbfffffff1c310c

def z419 : W := mkw 0x00ce4c0000233001 0x0067260000119800 0x000c000000030000 0x0006000000018000

def z420 : W := mkw 0x0000020212000000 0x0000010109000000 0x41003f003e000000 0x20801f801f000000

def z421 : W := mkw 0x007aa0d4a03a4290 0x003d506a501d2148 0x0a7cc098c03b62d8 0x053e604c601db16c

def z422 : W := mkw 0x2000100008808020 0x1000080004404010 0x4100300038008020 0x208018001c004010

def z423 : W := mkw 0x0020a00000000000 0x0010500000000000 0x5c70f00000000000 0x2e38780000000000

def z424 : W := mkw 0xe8ffffe3bbffff33 0xf47ffff1ddffff99 0xffffffe7ffffff3f 0xfffffff3ffffff9f

def z425 : W := mkw 0xa001112009c48c20 0xd000889004e24610 0xf5833f6039c49c21 0x7ac19fb01ce24e10

def z426 : W := mkw 0xc0010021016e0780 0x6000801080b703c0 0x0080000001f80000 0x0040000000fc0000

def z427 : W := mkw 0xc001112101c48d00 0xe000889080e24680 0xf4833f6701c49d01 0xfa419fb380e24e80

def z428 : W := mkw 0xa020b02008d0c420 0x5010581004686210 0xdff0f06039f8e421 0x6ff878301cfc7210

def z429 : W := mkw 0xc001002101440500 0x6000801080a20280 0xbe8f00ff01c707c1 0xdf47807f80e383e0

def z430 : W := mkw 0x016eee1e56000000 0x00b7770f2b000000 0x7c7fff1f06000000 0xbe3fff8f83000000

def z431 : W := mkw 0x280113021b848822 0x940089810dc24411 0x75833f003fc49827 0x3ac19f801fe24c13

def z432 : W := mkw 0x11ffffdef7b7f84d 0x88ffffef7bdbfc26 0xffffffffffffffff 0xffffffffffffffff

def z433 : W := mkw 0x0000000000000000 0x0000000000000000 0xc500000000008421 0x6280000000004210

def z434 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0x5173ff67fe000000 0x28b9ffb3ff000000

def z435 : W := mkw 0x2800110008808822 0x9400088004404411 0x0000000000009826 0x0000000000004c13

def z436 : W := mkw 0xe91113ffffc48d22 0xf48889ffffe24691 0xf5833fffffc49d27 0xfac19fffffe24e93

def z437 : W := mkw 0xa000102008d8c630 0x50000810046c6318 0xd780306039f8e639 0x6bc018301cfc731c

def z438 : W := mkw 0xa020b02008d8c630 0x50105810046c6318 0x5ef0f00001f8e639 0x2f78780000fc731c

def z439 : W := mkw 0x10044a0a5601304d 0x080225052b009826 0xff0ffffffe07ffff 0xff87ffffff03ffff

def z440 : W := mkw 0x38045b0a5e81b86f 0x9c022d852f40dc37 0x4100ff00fe00f83e 0x20807f807f007c1f

def z441 : W := mkw 0x00efed0001377801 0x8077f680009bbc00 0x2a7fcf00003f7800 0x153fe780001fbc00

def z442 : W := mkw 0xc0effd2101ffff81 0xe077fe9080ffffc0 0x7effff0001ffffc1 0x3f7fff8000ffffe0

def z443 : W := mkw 0x111002def600004c 0x0888016f7b000026 0x810000fffe0007fe 0xc080007fff0003ff

def z444 : W := mkw 0xc85b03f7136e0f82 0xe42d81fb89b707c1 0xbeff0fff07ff1fc7 0xdf7f87ff83ff8fe3

def z445 : W := mkw 0xc15b02fff76e0780 0x60ad817ffbb703c0 0xbfff00ffffff07c1 0xdfff807fffff83e0

def z446 : W := mkw 0x0024ec0000000000 0x0012760000000000 0x4000ff0000000000 0x20007f8000000000

def z447 : W := mkw 0xc0fbb5f501fecf80 0xe07ddafa80ff67c0 0xbeff37ff01ff07c1 0xdf7f9bff80ff83e0

def z448 : W := mkw 0x414f4e1f57260180 0x20a7a70fab9300c0 0x200f0f1f060701c0 0x9007878f830380e0

def z449 : W := mkw 0xe97fffffffc48d22 0xf4bfffffffe24691 0xfdffffffffc00000 0xfeffffffffe00000

def z450 : W := mkw 0xc01000f500480780 0x6008007a802403c0 0x9ef000ff01f807c1 0xcf78007f80fc03e0

def z451 : W := mkw 0xe81113f71bcc8fa2 0xf40889fb8de647d1 0xf5833fff3fc49fe7 0xfac19fff9fe24ff3

def z452 : W := mkw 0x100000084400004c 0x0800000422000026 0x00000018060001c6 0x8000000c030000e3

def z453 : W := mkw 0x10cf4d084527384d 0x8867a68422939c26 0x200f0f18060719c6 0x9007878c03038ce3

def z454 : W := mkw 0xe05b10f509fec7b0 0x702d887a84ff63d8 0xbeff00ff01ffe7f9 0xdf7f807f80fff3fc

def z455 : W := mkw 0xe05b00f5a96e07b0 0x702d807ad4b703d8 0xbfff00fff9ff07f9 0xdfff807ffcff83fc

def z456 : W := mkw 0x00fffdd401bffa81 0x807ffeea00dffd40 0x7effff9801fffac1 0x3f7fffcc00fffd60

def z457 : W := mkw 0xe97fffffffee8fa2 0xf4bffffffff747d1 0xffffffffffff9fe7 0xffffffffffffcff3

def z458 : W := mkw 0xa01010e0a8d8c630 0x50080870546c6318 0x838000e0f9f8e639 0x41c000707cfc731c

def z459 : W := mkw 0x20a4fd00a891f831 0x90527e805448fc18 0x4100ff00f800f838 0x20807f807c007c1c

def z460 : W := mkw 0xe80113231bee8fa2 0xf40089918df747d1 0xf7833f673fff9fe7 0xfbc19fb39fffcff3

def z461 : W := mkw 0xa07efce0a8d8c630 0x503f7e70546c6318 0xffffffe0f9f8e639 0x7ffffff07cfc731c

def z462 : W := mkw 0xe831b3e3bbdccf32 0xf418d9f1ddee6799 0xdff3f7e7f9f8e639 0x6ff9fbf3fcfc731c

def z463 : W := mkw 0x100448084401304d 0x0802240422009826 0xc100c898c600fffe 0xe080644c63007fff

def z464 : W := mkw 0x494f4f1f57040902 0xa4a7a78fab820481 0x200f0f1f06041906 0x9007878f83020c83

def z465 : W := mkw 0x017eecdce4000000 0x00bf766e72000000 0xdd7cf0f8f8000000 0x6ebe787c7c000000

def z466 : W := mkw 0xe8055b231bc5bd23 0xf402ad918de2de91 0xff8fff673fc7fd27 0xffc7ffb39fe3fe93

def z467 : W := mkw 0x114e4e1e5601304d 0x08a7270f2b009826 0xef0fcf9fc607ffff 0xf787e7cfe303ffff

def z468 : W := mkw 0xf8efff2b5ff7fd6f 0xfc77ff95affbfeb7 0xffffffffffffffff 0xffffffffffffffff

def z469 : W := mkw 0xc01100f5014c0780 0x6008807a80a603c0 0xb48300ff01c407c1 0xda41807f80e203e0

def z470 : W := mkw 0x0001000001260000 0x0000800000930000 0x0280000001ff0001 0x0140000000ff8000

def z471 : W := mkw 0x00cf5d0001a7b801 0x8067ae8000d3dc00 0x748f3f0001c79801 0x3a479f8000e3cc00

def z472 : W := mkw 0x0001010001040800 0x8000808000820400 0x20030f0000041800 0x1001878000020c00

def z473 : W := mkw 0x0000000000000000 0x0000000000000000 0x4100080006009826 0x2080040003004c13

def z474 : W := mkw 0x004a000000000000 0x0025000000000000 0x3c7f000000000000 0x1e3f800000000000

def z475 : W := mkw 0x00efff0213b7f801 0x8077ff8109dbfc00 0xffffff673ffff801 0xffffffb39ffffc00

def z476 : W := mkw 0xf8055b2b5fc5bd6f 0xfc02ad95afe2deb7 0xf583ff67ffc4fd3f 0xfac1ffb3ffe27e9f

def z477 : W := mkw 0x0100020af6000000 0x008001057b000000 0x01000000fe000000 0x008000007f000000

def z478 : W := mkw 0x011000dce4000000 0x0088006e72000000 0x00000098c0000000 0x0000004c60000000

def z479 : W := mkw 0x00a0b5000090c800 0x80505a8000486400 0x0000370000000000 0x00001b8000000000

def z480 : W := mkw 0x00efed0001273801 0x8077f68000939c00 0x7c7fff0000071800 0x3e3fff8000038c00

def z481 : W := mkw 0x28a4ff021a91f823 0x94527f810d48fc11 0x4100ff003e00f826 0x20807f801f007c13

def z482 : W := mkw 0x105e48dc442b32cd 0x082f246e22159966 0xef7cc898c63fffff 0xf7be644c631fffff

def z483 : W := mkw 0x48cf4f0313273903 0xa467a78189939c81 0x200f0f0706071906 0x9007878383038c83

def z484 : W := mkw 0x1034e8c8e419725d 0x081a7464720cb92e 0x0a7cc098c03b62d8 0x053e604c601db16c

def z485 : W := mkw 0x100448084401304d 0x0802240422009826 0x000c0018000300c0 0x0006000c00018060

def z486 : W := mkw 0x0081110001b6c800 0x8040888000db6400 0x0080000001f80000 0x0040000000fc0000

def z487 : W := mkw 0x100448084401304d 0x0802240422009826 0xef0cc898c60362d8 0xf786644c6301b16c

def z488 : W := mkw 0x100448084401304d 0x0802240422009826 0x610cc818c607f9fe 0xb086640c6303fcff

def z489 : W := mkw 0xa01010e0a8c88630 0x5008087054644318 0xd58030e0f9c08639 0x6ac018707ce0431c

def z490 : W := mkw 0xa17efefefed8c630 0x50bf7f7f7f6c6318 0xfdfffffffff80000 0xfefffffffffc0000

def z491 : W := mkw 0x017eecdce42a0280 0x00bf766e72150140 0x0a7cc098c03b02c0 0x053e604c601d8160

def z492 : W := mkw 0x0000000000000000 0x0000000000000000 0x200c0018000701c0 0x9006000c000380e0

def z493 : W := mkw 0x0000000000013001 0x0000000000009800 0x020000000007f801 0x010000000003fc00

def z494 : W := mkw 0xa0fefce0a8fbf631 0x507f7e70547dfb18 0xdffcf0e0f9fbe639 0x6ffe78707cfdf31c

def z495 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0x74833f6739c49801 0x3a419fb39ce24c00

def z496 : W := mkw 0x8000002000480600 0x4000001000240300 0x0280000001f80601 0x0140000000fc0300

def z497 : W := mkw 0x8000002000400400 0x4000001000200200 0x9480006001c00401 0x4a40003000e00200

def z498 : W := mkw 0xc01000f500480780 0x6008007a802403c0 0xae0c00ff000707c1 0xd706007f800383e0

def z499 : W := mkw 0x2020b000a890c030 0x1010580054486018 0x0000300038000000 0x000018001c000000

def z500 : W := mkw 0x10a4fd084491f84d 0x88527e842248fc26 0x4100ff00c600f83e 0x20807f8063007c1f

def z501 : W := mkw 0x017aa4d4a0000000 0x00bd526a50000000 0x0070000000000000 0x0038000000000000

def z502 : W := mkw 0x006eee0212000000 0x0037770109000000 0xfd7fff673e000000 0xfebfffb39f000000

def z503 : W := mkw 0xe925ff2bffc48d22 0xf492ff95ffe24691 0xf583ff67ffc49d27 0xfac1ffb3ffe24e93

def z504 : W := mkw 0xe91002fffe400522 0x7488017fff200291 0x810000fffe000526 0xc080007fff000293

def z505 : W := mkw 0x0024f8000091f001 0x00127c000048f800 0x7efcf80001fff801 0x3f7e7c0000fffc00

def z506 : W := mkw 0x100000084400004c 0x0800000422000026 0x01000000c600003e 0x008000006300001f

def z507 : W := mkw 0xf85f5bff5fefbfef 0xfc2fadffaff7dff7 0xffffffffffffffff 0xffffffffffffffff

def z508 : W := mkw 0x106eec084401304d 0x0837760422009826 0xff7fff98c607ffff 0xffbfffcc6303ffff

def z509 : W := mkw 0x100448084401304d 0x0802240422009826 0x8b0cc098c60367fe 0xc586604c6301b3ff

def z510 : W := mkw 0x280013021a808822 0x940009810d404411 0x0000370038000000 0x00001b801c000000

def z511 : W := mkw 0x100448084401304d 0x0802240422009826 0xe50c081806079de7 0xf286040c0303cef3

def z512 : W := mkw 0x0085590001b7f801 0x8042ac8000dbfc00 0x6e8cc80001fff801 0x3746640000fffc00

def z513 : W := mkw 0xf835fbebffddff7f 0xfc1afdf5ffeeffbf 0xffffffffffffffff 0xffffffffffffffff

def z514 : W := mkw 0x3024f808ec91f07d 0x18127c047648f83e 0x4100f800fe00f83e 0x20807c007f007c1f

def z515 : W := mkw 0xe94f5f3f5fc48d22 0xf4a7af9fafe24691 0xf58f3f7f3fc49d27 0xfac79fbf9fe24e93

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000098000007c0 0xc000004c000003e0

def z517 : W := mkw 0xe07bb0f5a9fec7b0 0x703dd87ad4ff63d8 0xbeff30ff39ff07c1 0xdf7f987f9cff83e0

def z518 : W := mkw 0x58054b0b5705394f 0xac02a585ab829ca7 0x200f0f1f060719c6 0x9007878f83038ce3

def z519 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0x74833f0001c49d27 0x3a419f8000e24e93

def z520 : W := mkw 0xc0df4df5016f3f81 0xe06fa6fa80b79fc0 0xbeff0fff01ff1fc1 0xdf7f87ff80ff8fe0

def z521 : W := mkw 0x004a001400000000 0x0025000a00000000 0x200f001f00000000 0x9007800f80000000

def z522 : W := mkw 0xc1fffffff7ffff81 0xe0fffffffbffffc0 0xffffffffffffffc1 0xffffffffffffffe0

def z523 : W := mkw 0x484b031713260982 0xa425818b899304c1 0x200f0f1f060719c6 0x9007878f83038ce3

def z524 : W := mkw 0x280013021a808822 0x940009810d404411 0xf5033f673e009826 0xfa819fb39f004c13

def z525 : W := mkw 0x0001110001848800 0x8000888000c24400 0x1083370001c00000 0x08419b8000e00000

def z526 : W := mkw 0xe001102109fec7b0 0x7000881084ff63d8 0x0280000001ffe7f9 0x0140000000fff3fc

def z527 : W := mkw 0x01044e0a56000000 0x008227052b000000 0x00000f0006000000 0x0000078003000000

def z528 : W := mkw 0xe0fffdf5a9ffffb1 0xf07ffefad4ffffd8 0xfffffffff9fffff9 0xfffffffffcfffffc

def z529 : W := mkw 0x0120a602b2000000 0x0090530159000000 0x0000370038000000 0x00001b801c000000

def z530 : W := mkw 0xc0effd2101f7fd01 0xe077fe9080fbfe80 0xfeffff6701fffd01 0xff7fffb380fffe80

def z531 : W := mkw 0x0004480000013001 0x0002240000009800 0x200c080000071800 0x1006040000038c00

def z532 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0x918337673fc00526 0xc8c19bb39fe00293

def z533 : W := mkw 0x100000000000004c 0x0800000000000026 0x00000000000007fe 0x00000000000003ff

def z534 : W := mkw 0xc05b00f501440500 0x602d807a80a20280 0xbcff00ff01c40501 0xde7f807f80e20280

def z535 : W := mkw 0x0020b0000090c000 0x0010580000486000 0x4000f0000000e000 0x2000780000007000

def z536 : W := mkw 0x00fffdc0a1b7f801 0x807ffee050dbfc00 0xffffffe0f9fff801 0x7ffffff07cfffc00

def z537 : W := mkw 0x017eecdce4184210 0x00bf766e720c2108 0x0a7cc098c0386218 0x053e604c601c310c

def z538 : W := mkw 0x405b00d501260180 0x202d806a809300c0 0xbc7f00ff000701c0 0xde3f807f800380e0

def z539 : W := mkw 0x405b00d5012e0380 0x202d806a809701c0 0x2a7f009f003f03c0 0x953f804f801f81e0

def z540 : W := mkw 0xc001022313440500 0x6000811189a20280 0xf5833f673fc40501 0xfac19fb39fe20280

def z541 : W := mkw 0xc01100e1014c0700 0x6008807080a60380 0xbef300e701fc0701 0xdf79807380fe0380

def z542 : W := mkw 0x20000000a8000030 0x1000000054000018 0x01000000f8000038 0x008000007c00001c

def z543 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xffffc0ffc1ffe7f9 0xffffe07fe0fff3fc

def z544 : W := mkw 0xa030b0e0a8c08420 0x5018587054604210 0xddf0f0e0f9c08421 0x6ef878707ce04210

def z545 : W := mkw 0x00844d0000013801 0x8042268000009c00 0x00000f0000001800 0x0000078000000c00

def z546 : W := mkw 0x104f48084527304d 0x0827a40422939826 0xffffc898c7ffffff 0xffffe44c63ffffff

def z547 : W := mkw 0xd17feefff76f37cd 0x68bff77ffbb79be6 0xffffffffffffffff 0xffffffffffffffff

def z548 : W := mkw 0xa0b1b1e0a9fffe31 0xd058d8f054ffff18 0xdff0f0e0f9fffe39 0x6ff878707cffff1c

def z549 : W := mkw 0x0000000000000000 0x0000000000000000 0xd500306038000000 0x6a8018301c000000

def z550 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x90f300ff01f807c0 0xc879807f80fc03e0

def z551 : W := mkw 0xe84b13371be68da2 0xf425899b8df346d1 0xf58f3f7f3fc79de7 0xfac79fbf9fe3cef3

def z552 : W := mkw 0x00eaa40000324000 0x0075520000192000 0x0070000000380000 0x00380000001c0000

def z553 : W := mkw 0x004a000000220000 0x0025000000110000 0x0a7c0000003b0000 0x053e0000001d8000

def z554 : W := mkw 0xe821b3231bd4cd22 0xf410d9918dea6691 0xfff3ff673ffcfd27 0xfff9ffb39ffe7e93

def z555 : W := mkw 0x005b00d4012e0280 0x002d806a00970140 0x3eff009801ff02c1 0x1f7f804c00ff8160

def z556 : W := mkw 0x0030b0c0a090c000 0x0018586050486000 0xdff0f0e0f9f8e001 0x6ff878707cfc7000

def z557 : W := mkw 0x0004480000013001 0x0002240000009800 0x4000c8000000f800 0x2000640000007c00

def z558 : W := mkw 0xe80103231b440d22 0xf40081918da20691 0xa1030f673e041d26 0xd08187b39f020e93

def z559 : W := mkw 0xa000002008400420 0x5000001004200210 0x8100006038000420 0x408000301c000210

def z560 : W := mkw 0x504f481d452731cd 0x2827a40ea29398e6 0xef0fc89fc607ffff 0xf787e44fe303ffff

def z561 : W := mkw 0x014e4c1c44000000 0x00a7260e22000000 0x000c001800000000 0x0006000c00000000

def z562 : W := mkw 0x007eecd400000000 0x003f766a00000000 0xfc7fffff00000000 0xfe3fffff80000000

def z563 : W := mkw 0xa01010e008d8c630 0x50080870046c6318 0x9ef000e001f8e639 0x4f78007000fc731c

def z564 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0x41803f003fc49d27 0x20c01f801fe24e93

def z565 : W := mkw 0x0100021e56000000 0x0080010f2b000000 0x0000001f06000000 0x8000000f83000000

def z566 : W := mkw 0x0000000000000000 0x0000000000000000 0xef0c089806079fe7 0xf786044c0303cff3

def z567 : W := mkw 0x004e4c0000000000 0x0027260000000000 0x200f0f0000000000 0x1007878000000000

def z568 : W := mkw 0x280002021a000022 0x140001010d000011 0x010000003e000026 0x008000001f000013

def z569 : W := mkw 0x017eecdce4000000 0x00bf766e72000000 0xed7cc898c6000000 0xf6be644c63000000

def z570 : W := mkw 0x0030b0c0a098c210 0x00185860504c6108 0x5ef0f080c1f8e219 0x2f78784060fc710c

def z571 : W := mkw 0xa0fbb5e0a9fece30 0xd07ddaf054ff6718 0x10f3376039f80000 0x08799bb01cfc0000

def z572 : W := mkw 0xe80102231b440522 0x740081118da20291 0xb58300673fc40527 0xdac180339fe20293

def z573 : W := mkw 0x100000000001304d 0x0800000000009826 0x00000000000719c6 0x0000000000038ce3

def z574 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a0c0098000302c0 0x0506004c00018160

def z575 : W := mkw 0xa07ab0f4a8fac6b0 0x503d587a547d6358 0xdffcf0f8f9fbe6f9 0x6ffe787c7cfdf37c

def z576 : W := mkw 0x1124ee0af601304d 0x089277057b009826 0x4100ff00fe00f83e 0x20807f807f007c1f

def z577 : W := mkw 0xa000002008480630 0x5000001004240318 0x0000000000000638 0x000000000000031c

def z578 : W := mkw 0x005b00d401260000 0x002d806a00930000 0xbeff00ff01ff0001 0xdf7f807f80ff8000

def z579 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x91f030e0f9f80638 0x48f818707cfc031c

def z580 : W := mkw 0x100448084401304d 0x0802240422009826 0x6e0cc898c007fad9 0x3706644c6003fd6c

def z581 : W := mkw 0xa000102008d8c630 0x50000810046c6318 0xcf80c080c1f8e639 0x67c0604060fc731c

def z582 : W := mkw 0x100448084401304d 0x0802240422009826 0x220c08180607ffff 0x9106040c0303ffff

def z583 : W := mkw 0xa01010e008c88620 0x5008087004644310 0xdff030e039f88621 0x6ff818701cfc4310

def z584 : W := mkw 0x01fbb7d6b3b6c800 0x80fddbeb59db6400 0x10f3376739f80000 0x08799bb39cfc0000

def z585 : W := mkw 0x0004480000013001 0x0002240000009800 0xee0cc8980007ffc1 0xf706644c0003ffe0

def z586 : W := mkw 0xc05f48fd456e0780 0x602fa47ea2b703c0 0xffffc8ffc7ff07c1 0xffffe47fe3ff83e0

def z587 : W := mkw 0xc05a00f5006a0780 0x602d007a803503c0 0x8a7c00ff003b07c0 0xc53e007f801d83e0

def z588 : W := mkw 0x006eec0000013001 0x0037760000009800 0x7e7fff000007f801 0x3f3fff800003fc00

def z589 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xddf0f0e0f9f80000 0x6ef878707cfc0000

def z590 : W := mkw 0x100448084401304d 0x0802240422009826 0xa10c0898c6071ffe 0xd086044c63038fff

def z591 : W := mkw 0x01ffefdef7273801 0x80fff7ef7b939c00 0xfd7ffffffe071800 0xfebfffffff038c00

def z592 : W := mkw 0xe80012231ac08522 0x740009118d604291 0xd58030673fc08527 0xeac018339fe04293

def z593 : W := mkw 0x4801030313040902 0xa400818189820481 0x0003070700000000 0x0001838380000000

def z594 : W := mkw 0xb034f8e8ecd9f67d 0x581a7c74766cfb3e 0xdffcf0f8f9fbe6f9 0x6ffe787c7cfdf37c

def z595 : W := mkw 0x006eec0000000000 0x0037760000000000 0x087cc00000000000 0x043e600000000000

def z596 : W := mkw 0x006aa40000000000 0x0035520000000000 0x1073370000000000 0x08399b8000000000

def z597 : W := mkw 0x0030a0c0a0000000 0x0018506050000000 0x1070306038000000 0x083818301c000000

def z598 : W := mkw 0xa031b1e0a9dcce30 0xd018d8f054ee6718 0xfff3ffe0f9fcfe39 0x7ff9fff07cfe7f1c

def z599 : W := mkw 0xb034f8e8ecd9f67d 0x581a7c74766cfb3e 0xdff0f8e0fff8fe3f 0x6ff87c707ffc7f1f

def z600 : W := mkw 0xc07ba0f5a17e4790 0x603dd07ad0bf23c8 0xbeffc0ffc1ff67d9 0xdf7fe07fe0ffb3ec

def z601 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xa00f00ff000707c0 0xd007807f800383e0

def z602 : W := mkw 0xd01000fd444807cc 0x6808007ea22403e6 0x810000ffc60007fe 0xc080007fe30003ff

def z603 : W := mkw 0xa0effd2009f7fc21 0xd077fe9004fbfe10 0xffffff6039fffc21 0x7fffffb01cfffe10

def z604 : W := mkw 0x00a4fd000091f801 0x80527e800048fc00 0x6e0cff000007f801 0x37067f800003fc00

def z605 : W := mkw 0x0000000000000000 0x0000000000000000 0x8100000006000526 0xc080000003000293

def z606 : W := mkw 0x0004480000013001 0x0002240000009800 0xef0cc8000607fd27 0xf78664000303fe93

def z607 : W := mkw 0x0124ee0af6000000 0x009277057b000000 0xed0cff98fe000000 0xf6867fcc7f000000

def z608 : W := mkw 0xb01000e8ec48067c 0x580800747624033e 0x810000f8fe0007fe 0xc080007c7f0003ff

def z609 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0x287fcf9fc6000000 0x943fe7cfe3000000

def z610 : W := mkw 0x901448e84449364d 0x480a247422249b26 0xfffcc8f8c7ffffff 0xfffe647c63ffffff

def z611 : W := mkw 0xc07bb0f501fec780 0x603dd87a80ff63c0 0xfefff0ff01ffe7c1 0xff7ff87f80fff3e0

def z612 : W := mkw 0xc07ba0f5a16e0780 0x603dd07ad0b703c0 0xfffff0fff9ff07c1 0xfffff87ffcff83e0

def z613 : W := mkw 0x00feecc0a03b7211 0x007f7660501db908 0x0a7cc080c03b6218 0x053e6040601db10c

def z614 : W := mkw 0xc05f48f5016f3781 0x602fa47a80b79bc0 0xfeffc8ff01ffffc1 0xff7fe47f80ffffe0

def z615 : W := mkw 0x4000001500000180 0x2000000a800000c0 0x0000001f000001c0 0x8000000f800000e0

def z616 : W := mkw 0xe80002231a400522 0x740001118d200291 0xe50008673e049d27 0xf28004339f024e93

def z617 : W := mkw 0x0000000000184210 0x00000000000c2108 0x0200000000386218 0x01000000001c310c

def z618 : W := mkw 0xe81113e3bbcc8f32 0xf40889f1dde64799 0xf5833fe7ffc49f3f 0xfac19ff3ffe24f9f

def z619 : W := mkw 0xc001002101440500 0x6000801080a20280 0x1083006701c00000 0x0841803380e00000

def z620 : W := mkw 0x01ffffdef7b6c800 0x80ffffef7bdb6400 0xfdfffffffff80000 0xfefffffffffc0000

def z621 : W := mkw 0x0080000000337001 0x004000000019b800 0x02000000003b6000 0x01000000001db000

def z622 : W := mkw 0x404b001501260180 0x2025800a809300c0 0xae0f009f000707c1 0xd707804f800383e0

def z623 : W := mkw 0x0034e8c8e4000000 0x001a746472000000 0xfd7cf8f8fe000000 0xfebe7c7c7f000000

def z624 : W := mkw 0x100559084585b84d 0x8802ac8422c2dc26 0xff8fff98c7c7ffff 0xffc7ffcc63e3ffff

def z625 : W := mkw 0xf97fffffffc5bd6f 0xfcbfffffffe2deb7 0xffffffffffc7ffff 0xffffffffffe3ffff

def z626 : W := mkw 0x00fffdd401b7f801 0x807ffeea00dbfc00 0xfeffffff01fff801 0xff7fffff80fffc00

def z627 : W := mkw 0xa01000e0a8480630 0x5008007054240318 0x9ff000e0f9f80639 0x4ff800707cfc031c

def z628 : W := mkw 0xa17efcfcecd8c630 0x50bf7e7e766c6318 0xdffcf0f8f9f8e639 0x6ffe787c7cfc731c

def z629 : W := mkw 0x006ffd0001848800 0x8037fe8000c24400 0x7cffff0001c49801 0x3e7fff8000e24c00

def z630 : W := mkw 0x008011000091f801 0x804008800048fc00 0x000000000000f800 0x0000000000007c00

def z631 : W := mkw 0xd01448fd444937cd 0x680a247ea2249be6 0xef0cc8ffc607ffff 0xf786647fe303ffff

def z632 : W := mkw 0x0004480844000000 0x0002240422000000 0xef0cc898c600e639 0xf786644c6300731c

def z633 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xf5833f673fc00000 0xfac19fb39fe00000

def z634 : W := mkw 0x100448084400004c 0x0802240422000026 0xed0cc898c60007fe 0xf686644c630003ff

def z635 : W := mkw 0x4801130313848902 0xa400898189c24481 0x74833f0707c49907 0xba419f8383e24c83

def z636 : W := mkw 0xb00458284cd9f67d 0x58022c14266cfb3e 0xef8cc898c7ffffff 0xf7c6644c63ffffff

def z637 : W := mkw 0xe80013231ac08d22 0xf40009918d604691 0xc1003f673e009d26 0xe0801fb39f004e93

def z638 : W := mkw 0xa0fbb5e0a9fece30 0xd07ddaf054ff6718 0xdff3f7e0f9f8e639 0x6ff9fbf07cfc731c

def z639 : W := mkw 0x000559000185b801 0x8002ac8000c2dc00 0x7e8fff0001c7f801 0x3f47ff8000e3fc00

def z640 : W := mkw 0xb030b0e0a8d9f67d 0x58185870546cfb3e 0xdff0f0e0f9ffffff 0x6ff878707cffffff

def z641 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x9ef030e039f80601 0x4f7818701cfc0300

def z642 : W := mkw 0xa134feeafed8c630 0x509a7f757f6c6318 0xdff0ffe0fff8e639 0x6ff87ff07ffc731c

def z643 : W := mkw 0x01efff0af7b7f801 0x80f7ff857bdbfc00 0x7fffff00fffff801 0x3fffff807ffffc00

def z644 : W := mkw 0xc0fbb5f501fecf80 0xe07ddafa80ff67c0 0x10f3376701f80000 0x08799bb380fc0000

def z645 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x600fff000007f800 0x3007ff800003fc00

def z646 : W := mkw 0x0030a0c0a0184210 0x00185060500c2108 0xcf70c080c038e639 0x67b86040601c731c

def z647 : W := mkw 0x801000e000480600 0x4008007000240300 0xbefc00f801ff07c1 0xdf7e007c00ff83e0

def z648 : W := mkw 0x001000c0a0000000 0x0008006050000000 0x810000e0f8000000 0x408000707c000000

def z649 : W := mkw 0xa07bb0e0a9fec630 0x503dd87054ff6318 0xfffff0e0f9ffe639 0x7ffff8707cfff31c

def z650 : W := mkw 0x0081110001b7f801 0x8040888000dbfc00 0x76833f0001fff801 0x3b419f8000fffc00

def z651 : W := mkw 0x0000000000000000 0x0000000000000000 0x1ef0000001f80001 0x0f78000000fc0000

def z652 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x9ef300e701f80601 0x4f79807380fc0300

def z653 : W := mkw 0xe07bb0f5a9fec7b0 0x703dd87ad4ff63d8 0xdff3f0e7f9f8e639 0x6ff9f873fcfc731c

def z654 : W := mkw 0xc05a00f500480780 0x602d007a802403c0 0xbc7f00ff000007c0 0xde3f807f800003e0

def z655 : W := mkw 0x2124fe0afe90c030 0x10927f057f486018 0x4100ff00fe00e038 0x20807f807f00701c

def z656 : W := mkw 0x0000000000000000 0x0000000000000000 0xef00c880c604ff3f 0xf780644063027f9f

def z657 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a00c080c0006218 0x050060406000310c

def z658 : W := mkw 0xa000102008c08420 0x5000081004604210 0xdf80f0e0f9c0e639 0x6fc078707ce0731c

def z659 : W := mkw 0x100448084401304d 0x0802240422009826 0x6e0cc8180607f9c7 0xb706640c0303fce3

def z660 : W := mkw 0x2820b302ba90c832 0x941059815d486419 0x4100ff00fe00f83e 0x20807f807f007c1f

def z661 : W := mkw 0xc17ba6f7b36e0780 0x60bdd37bd9b703c0 0xbeff37ff39ff07c1 0xdf7f9bff9cff83e0

def z662 : W := mkw 0x0004480000013001 0x0002240000009800 0x0a0cc00000036000 0x050660000001b000

def z663 : W := mkw 0x01efff1e57b7f801 0x80f7ff8f2bdbfc00 0x7effff1f07fff801 0xbf7fff8f83fffc00

def z664 : W := mkw 0x0004480844000000 0x0002240422000000 0xed0cc898c6049d27 0xf686644c63024e93

def z665 : W := mkw 0x001000c0a0080210 0x0008006050040108 0x00000080c0000218 0x000000406000010c

def z666 : W := mkw 0x001000c000080200 0x0008006000040100 0x0a70008000380200 0x05380040001c0100

def z667 : W := mkw 0x805a00f400480600 0x402d007a00240300 0xbeff00ff01f80601 0xdf7f807f80fc0300

def z668 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xc100f0e0f800e638 0x608078707c00731c

def z669 : W := mkw 0x0004480844000000 0x0002240422000000 0x080cc098c0000000 0x0406604c60000000

def z670 : W := mkw 0x00eeec0000337001 0x007776000019b800 0x6e7cc800003ff801 0x373e6400001ffc00

def z671 : W := mkw 0x28efff021bb7f823 0x9477ff810ddbfc11 0x7fffff003ffff827 0x3fffff801ffffc13

def z672 : W := mkw 0xc05b11f501ee8f80 0xe02d88fa80f747c0 0xfeff3fff01ff9fc1 0xff7f9fff80ffcfe0

def z673 : W := mkw 0x100448084401304d 0x0802240422009826 0xed0cc898c60719c6 0xf686644c63038ce3

def z674 : W := mkw 0x801000e000480600 0x4008007000240300 0xdff0c0e0c1f8e639 0x6ff8607060fc731c

def z675 : W := mkw 0xb030b0e8ecd8c67c 0x58185874766c633e 0xdff0f0f8fff8e7ff 0xeff8787c7ffc73ff

def z676 : W := mkw 0xc15f4eff576e0780 0x60afa77fabb703c0 0xbeff0fff07ff07c1 0xdf7f87ff83ff83e0

def z677 : W := mkw 0xe031b0e1a9fec7b0 0x7018d870d4ff63d8 0xdff0f0e0f9ffe7f9 0x6ff878707cfff3fc

def z678 : W := mkw 0x100000000001304d 0x0800000000009826 0xae0c00980007ffff 0xd706004c0003ffff

def z679 : W := mkw 0x01a4ff0af691f801 0x80d27f857b48fc00 0x4100ff00fe00f800 0x20807f807f007c00

def z680 : W := mkw 0x2030b0c0a890c030 0x1018586054486018 0xdd70f0e0f800e038 0x6eb878707c00701c

def z681 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x3eff006701ff0001 0x1f7f803380ff8000

def z682 : W := mkw 0xe17ffefffffec7b0 0x70bfff7fffff63d8 0xffffffffffffe7f9 0xfffffffffffff3fc

def z683 : W := mkw 0xa000102008c08420 0x5000081004604210 0xf58038603fc49d27 0xfac01c301fe24e93

def z684 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xb483376739c40501 0xda419bb39ce20280

def z685 : W := mkw 0x017eecdce4000000 0x00bf766e72000000 0xbc7fc0ffc0000000 0xde3fe07fe0000000

def z686 : W := mkw 0xe8cf5f231be7bd23 0xf467af918df3de91 0xf58f3f673fc79d27 0xfac79fb39fe3ce93

def z687 : W := mkw 0x00000000002a0280 0x0000000000150140 0x02000000003b02c0 0x01000000001d8160

def z688 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0xb483006701c49d27 0xda41803380e24e93

def z689 : W := mkw 0x2924ff0afe808822 0x94927f857f404411 0x4100ff00fe009826 0x20807f807f004c13

def z690 : W := mkw 0xc0fffdf501ffff81 0xe07ffefa80ffffc0 0x7effff6701fff801 0x3f7fffb380fffc00

def z691 : W := mkw 0x38045b0a5e81b86f 0x9c022d852f40dc37 0xef0cff98fe07ffff 0xf7867fcc7f03ffff

def z692 : W := mkw 0x8030b0e000d8c600 0x40185870006c6300 0xdef0f0e001f8e601 0x6f78787000fc7300

def z693 : W := mkw 0x1034e8c8e419725d 0x081a7464720cb92e 0xef7cc898c63fffff 0xf7be644c631fffff

def z694 : W := mkw 0x100000084401304d 0x0800000422009826 0x83000098c607ffff 0xc180004c6303ffff

def z695 : W := mkw 0xa1fffffefffffe31 0xd0ffffff7fffff18 0xfffffffffffffe39 0xffffffffffffff1c

def z696 : W := mkw 0x01feffdef691f801 0x80ff7fef7b48fc00 0xfd7ffffffe00f800 0xfebfffffff007c00

def z697 : W := mkw 0x0000000000000000 0x0000000000000000 0x6400080000049801 0x3200040000024c00

def z698 : W := mkw 0xe85b02f71b6e07a2 0x742d817b8db703d1 0xbfff00ff3fff07e7 0xdfff807f9fff83f3

def z699 : W := mkw 0xf8055b2b5fc5bd6f 0xfc02ad95afe2deb7 0xf58f3f7f3fc79de7 0xfac79fbf9fe3cef3

def z700 : W := mkw 0xe85b13f71bee8fa2 0xf42d89fb8df747d1 0xf5f33f673ffc9d27 0xfaf99fb39ffe4e93

def z701 : W := mkw 0x01fffddce5b7f801 0x80fffeee72dbfc00 0x7effff98c1fff801 0x3f7fffcc60fffc00

def z702 : W := mkw 0xc04b0021016e0780 0x6025801080b703c0 0x3eff000001ff07c1 0x1f7f800000ff83e0

def z703 : W := mkw 0x4001000101040100 0x2000800080820080 0x2003000700040100 0x9001800380020080

def z704 : W := mkw 0x1024f8084491f04d 0x08127c042248f826 0xfffcf898c7ffffff 0xfffe7c4c63ffffff

def z705 : W := mkw 0xe831b3e3bbdccf32 0xf418d9f1ddee6799 0xf5f33f673ffc9d27 0xfaf99fb39ffe4e93

def z706 : W := mkw 0x0000000000000000 0x0000000000000000 0x020000000000e639 0x010000000000731c

def z707 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x7eff3f0001ff9801 0x3f7f9f8000ffcc00

def z708 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x7fffff00c1fff839 0x3fffff8060fffc1c

def z709 : W := mkw 0x117eeedef619725d 0x08bf776f7b0cb92e 0xff7ffffffe3b62d8 0xffbfffffff1db16c

def z710 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x32ff007f01ff07c1 0x997f803f80ff83e0

def z711 : W := mkw 0x019113def7b7f801 0x80c889ef7bdbfc00 0x838000fffffff801 0xc1c0007ffffffc00

def z712 : W := mkw 0x0000020212000000 0x0000010109000000 0x910337673e000000 0xc8819bb39f000000

def z713 : W := mkw 0x117eeedef62b32cd 0x08bf776f7b159966 0xff7ffffffe3fffff 0xffbfffffff1fffff

def z714 : W := mkw 0xe97ffdfdedc48d22 0xf4bffefef6e24691 0x08fcc098c1c49d27 0x047e604c60e24e93

def z715 : W := mkw 0x0021b1000194c800 0x8010d88000ca6400 0x74f33f0001fc9801 0x3a799f8000fe4c00

def z716 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xdff0f8e0fff8fe3f 0x6ff87c707ffc7f1f

def z717 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x8afc00ff01ff07c1 0xc57e007f80ff83e0

def z718 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xdff0f0e0fff8e73f 0xeff878707ffc739f

def z719 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x5bf0f0e0f9f8e238 0x2df878707cfc711c

def z720 : W := mkw 0xe030b0f5a8d8c7b0 0x7018587ad46c63d8 0xdff0f0e7f9f8e639 0x6ff87873fcfc731c

def z721 : W := mkw 0x100448084401304d 0x0802240422009826 0xff0fc8ffc607ffff 0xff87e47fe303ffff

def z722 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xb17f3ffffe000000 0xd8bf9fffff000000

def z723 : W := mkw 0x606bb015a9b6c1b0 0x3035d80ad4db60d8 0x610ff01ff807e1f8 0xb087f80ffc03f0fc

def z724 : W := mkw 0xe831b1e1a9dccf32 0xf418d8f0d4ee6799 0x0af0c080c1fcff3f 0x0578604060fe7f9f

def z725 : W := mkw 0xd05f48fd456f37cd 0x682fa47ea2b79be6 0x51f3c867c7f8f83e 0x28f9e433e3fc7c1f

def z726 : W := mkw 0x11feecdce433704d 0x08ff766e7219b826 0x0a7cc098c03b62d8 0x053e604c601db16c

def z727 : W := mkw 0x017aa6def6000000 0x00bd536f7b000000 0x107337fff8000000 0x08399bfffc000000

def z728 : W := mkw 0xe87bb3f7bbfecfb2 0xf43dd9fbddff67d9 0x10f3376739f80000 0x08799bb39cfc0000

def z729 : W := mkw 0xe801112109d4cd22 0xf400889084ea6691 0x0280000001fcfd27 0x0140000000fe7e93

def z730 : W := mkw 0x0030a2c2b2000000 0x0018516159000000 0xff73ffe7fe04ff3f 0xffb9fff3ff027f9f

def z731 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0x107f377f38000000 0x083f9bbf9c000000

def z732 : W := mkw 0x0000020212000000 0x0000010109000000 0xfd03ffe7fe000000 0xfe81fff3ff000000

def z733 : W := mkw 0x4831a3c3b31c4b12 0xa418d1e1d98e2589 0x2a73cf87c63c7b1e 0x9539e7c3e31e3d8f

def z734 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xff7ffffffe006218 0xffbfffffff00310c

def z735 : W := mkw 0x0000020212000000 0x0000010109000000 0x51033f673e000000 0x28819fb39f000000

def z736 : W := mkw 0xf80559294dddff7f 0xfc02ac94a6eeffbf 0xef8cc898c7ffffff 0xf7c6644c63ffffff

def z737 : W := mkw 0x016eee1e56000000 0x00b7770f2b000000 0xfd7fff7f3e000000 0xfebfffbf9f000000

def z738 : W := mkw 0xc11002ff56480780 0x6088017fab2403c0 0x800000ff060007c0 0xc000007f830003e0

def z739 : W := mkw 0xc05b01f5016e0f80 0xe02d80fa80b707c0 0xbeff0fff01ff1fc1 0xdf7f87ff80ff8fe0

def z740 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0x0080000001c41906 0x0040000000e20c83

def z741 : W := mkw 0xe81002f71a4807a2 0x7408017b8d2403d1 0x800000ff380007c0 0xc000007f9c0003e0

def z742 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xff7ffffffe03fafe 0xffbfffffff01fd7f

def z743 : W := mkw 0x01144adef6000000 0x008a256f7b000000 0xfd0ffffffe000000 0xfe87ffffff000000

def z744 : W := mkw 0xe88113231bf6cd22 0xf44089918dfb6691 0xf5833f673ffc9d27 0xfac19fb39ffe4e93

def z745 : W := mkw 0x0000020212000000 0x0000010109000000 0xd503376738000000 0x6a819bb39c000000

def z746 : W := mkw 0xe801112109cc8f32 0xf400889084e64799 0x0080000001c49f3f 0x0040000000e24f9f

def z747 : W := mkw 0xc801032313440d02 0xe400819189a20681 0xf5833f673fc41d07 0xfac19fb39fe20e83

def z748 : W := mkw 0xe80103231b440d22 0xf40081918da20691 0xf5033f673e041d26 0xfa819fb39f020e93

def z749 : W := mkw 0x40effd0101b7f901 0xa077fe8080dbfc80 0x7effff0701fff901 0xbf7fff8380fffc80

def z750 : W := mkw 0x01feeed6b2337001 0x00ff776b5919b800 0x1a7ff767383b6000 0x0d3ffbb39c1db000

def z751 : W := mkw 0xe91002fffe4807a2 0x7488017fff2403d1 0x810000fffe0007e6 0xc080007fff0003f3

def z752 : W := mkw 0xb034f8e8ecd9f67d 0x581a7c74766cfb3e 0x30fc38783fff19c6 0x987e1c3c1fff8ce3

def z753 : W := mkw 0x285a13d61aaa8aa2 0x942d09eb0d554551 0x4b7c3f983e3b9ae6 0x25be1fcc1f1dcd73

def z754 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0x7effff98c1ffffff 0x3f7fffcc60ffffff

def z755 : W := mkw 0x006ba40001260000 0x0035d20000930000 0x10f3370001f80000 0x08799b8000fc0000

def z756 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xff7ffffffe0367fe 0xffbfffffff01b3ff

def z757 : W := mkw 0xa01000e0a8480630 0x5008007054240318 0xdff0c0e0f9f8e639 0x6ff860707cfc731c

def z758 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xfff3ffe0f9f8e639 0x7ff9fff07cfc731c

def z759 : W := mkw 0x106eee0a5601304d 0x083777052b009826 0xff7ffffffe07ffff 0xffbfffffff03ffff

def z760 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0xcf80c080c1c4ff3f 0x67c0604060e27f9f

def z761 : W := mkw 0x280113021b848822 0x940089810dc24411 0xf5833f673fc49827 0xfac19fb39fe24c13

def z762 : W := mkw 0x011002d6b2000000 0x0088016b59000000 0x1003376738000000 0x08019bb39c000000

def z763 : W := mkw 0xe801112109e68da2 0xf400889084f346d1 0x0080000001c79de7 0x0040000000e3cef3

def z764 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x3eff00ff01ff02c1 0x1f7f807f80ff8160

def z765 : W := mkw 0xe8eeee231a737523 0x747777118d39ba91 0x8b7cc0673e3b6526 0xc5be60339f1db293

def z766 : W := mkw 0xe801112109ee8fa2 0xf400889084f747d1 0xef8c089807ff9fe7 0xf7c6044c03ffcff3

def z767 : W := mkw 0xf881112109f7fd6f 0xfc40889084fbfeb7 0x0280000001ffffff 0x0140000000ffffff

def z768 : W := mkw 0xc0b4fdf500d9ff81 0xe05a7efa806cffc0 0xc000ffff0000ffc0 0xe0007fff80007fe0

def z769 : W := mkw 0x11a4ff0af691f84d 0x88d27f857b48fc26 0x4100ff00fe00f83e 0x20807f807f007c1f

def z770 : W := mkw 0x0000020212000000 0x0000010109000000 0x41003f003e009826 0x20801f801f004c13

def z771 : W := mkw 0x006ba40001260000 0x0035d20000930000 0x3eff370001ff0001 0x1f7f9b8000ff8000

def z772 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0xdff3f780c1f8e639 0x6ff9fbc060fc731c

def z773 : W := mkw 0x811002fef6480600 0x4088017f7b240300 0x810000fffe000600 0xc080007fff000300

def z774 : W := mkw 0x40effd1501b7f981 0xa077fe8a80dbfcc0 0xfeffff9f01ffffc1 0xff7fffcf80ffffe0

def z775 : W := mkw 0x017aa6def6000000 0x00bd536f7b000000 0x1073377f3e000000 0x88399bbf9f000000

def z776 : W := mkw 0x017aa6d6b22a0280 0x00bd536b59150140 0x1a7f37ff383b02c0 0x0d3f9bff9c1d8160

def z777 : W := mkw 0x017eeedef6013001 0x00bf776f7b009800 0xfd7ffffffe00f800 0xfebfffffff007c00

def z778 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0xfeffff9801fff801 0xff7fffcc00fffc00

def z779 : W := mkw 0x00a1b10001b7f801 0x8050d88000dbfc00 0x7ef3ff0001fff801 0x3f79ff8000fffc00

def z780 : W := mkw 0xe85b11f509ee8fa2 0xf42d88fa84f747d1 0x0afc009801ff9fe7 0x057e004c00ffcff3

def z781 : W := mkw 0x1025f9084595f84d 0x8812fc8422cafc26 0xffffff98c7ffffff 0xffffffcc63ffffff

def z782 : W := mkw 0x805a00f400480600 0x402d007a00240300 0xbeff00ff01ff07c1 0xdf7f807f80ff83e0

def z783 : W := mkw 0xa00012221ac08420 0x500009110d604210 0xf5833f673fc49d27 0xfac19fb39fe24e93

def z784 : W := mkw 0x100002021201304d 0x0800010109009826 0xf7033f673e07ffff 0xfb819fb39f03ffff

def z785 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0xfeffff8001fffe01 0x7f7fffc000ffff00

def z786 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x10f0f060f9f86018 0x087878307cfc300c

def z787 : W := mkw 0x00effd1401b7f801 0x8077fe8a00dbfc00 0x7effff1f01fff801 0xbf7fff8f80fffc00

def z788 : W := mkw 0x001002c2b2000000 0x0008016159000000 0xf5033fe7fe000000 0xfa819ff3ff000000

def z789 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x1aff00ff01ff07c1 0x0d7f807f80ff83e0

def z790 : W := mkw 0x0020b0000090c000 0x0010580000486000 0x7ef3ff0001f8e001 0x3f79ff8000fc7000

def z791 : W := mkw 0x001002c212000000 0x0008016109000000 0xfd733fe73e000000 0xfeb99ff39f000000

def z792 : W := mkw 0x114e4e1e5601304d 0x08a7270f2b009826 0xf50f3f7f3e079de7 0xfa879fbf9f03cef3

def z793 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0xc580000001c49d27 0x62c0000000e24e93

def z794 : W := mkw 0x404b001501260180 0x2025800a809300c0 0x30ff001f01ff01c0 0x987f800f80ff80e0

def z795 : W := mkw 0xe801112109dccf32 0xf400889084ee6799 0xef80c880c7fcff3f 0xf7c0644063fe7f9f

def z796 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xfff0f8e0fff8e639 0xfff87c707ffc731c

def z797 : W := mkw 0x006bb10001b6c800 0x8035d88000db6400 0x7effff0001fff801 0x3f7fff8000fffc00

def z798 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x74f33f0001f80000 0x3a799f8000fc0000

def z799 : W := mkw 0x0030b0c0a098c210 0x00185860504c6108 0xdff0f0e0f9f8e219 0x6ff878707cfc710c

def z800 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0x7effff98c7fffbdf 0xbf7fffcc63fffdef

def z801 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xdd73ffe7fe000000 0x6eb9fff3ff000000

def z802 : W := mkw 0x10044a0a5601304d 0x080225052b009826 0xff0ffffffe0362d8 0xff87ffffff01b16c

def z803 : W := mkw 0xf8055b2b5fc5bd6f 0xfc02ad95afe2deb7 0x1a8ff7fff9c362d8 0x0d47fbfffce1b16c

def z804 : W := mkw 0xc05b00f5a16e0790 0x602d807ad0b703c8 0xbeff00ffc1ff07d9 0xdf7f807fe0ff83ec

def z805 : W := mkw 0x106fec084527304d 0x0837f60422939826 0xffffff98c7ffffff 0xffffffcc63ffffff

def z806 : W := mkw 0xe80113231bee8fa2 0xf40089918df747d1 0xff8f3fff3fff9fe7 0xffc79fff9fffcff3

def z807 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x4afcff0001fff801 0x257e7f8000fffc00

def z808 : W := mkw 0xe85b00f5096e07a2 0x742d807a84b703d1 0xbeff00ff01ff07e7 0xdf7f807f80ff83f3

def z809 : W := mkw 0x017eeedef6080280 0x00bf776f7b040140 0xfd7ffffffe0002c0 0xfebfffffff000160

def z810 : W := mkw 0xe030b0e1a8d8c730 0x70185870d46c6398 0xdff0f0e7f9f8e739 0xeff87873fcfc739c

def z811 : W := mkw 0xe885592109f7fd23 0xf442ac9084fbfe91 0xef8cc80007fffd27 0xf7c6640003fffe93

def z812 : W := mkw 0xe81002e3ba480732 0x74080171dd240399 0x810000673e000526 0xc08000339f000293

def z813 : W := mkw 0x0000020212000000 0x0000010109000000 0xf5033f673e009826 0xfa819fb39f004c13

def z814 : W := mkw 0x117eeedef600004c 0x08bf776f7b000026 0xfd7ffffffe049fff 0xfebfffffff024fff

def z815 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xff7ffffffe0302c0 0xffbfffffff018160

def z816 : W := mkw 0x514f4e1f572731cd 0x28a7a70fab9398e6 0x200f0f1f060719c6 0x9007878f83038ce3

def z817 : W := mkw 0xe80113231bee8fa2 0xf40089918df747d1 0xf5833f673ffc9d27 0xfac19fb39ffe4e93

def z818 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x4bf0f080f9f8e639 0x25f878407cfc731c

def z819 : W := mkw 0x2020b000a890c030 0x1010580054486018 0xdff0f080f9f8e639 0x6ff878407cfc731c

def z820 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0xffffff98c7fff83f 0xffffffcc63fffc1f

def z821 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0x30733f673e000000 0x98399fb39f000000

def z822 : W := mkw 0x00effd0845b6c800 0x8077fe8422db6400 0xfdffff98c7f80000 0xfeffffcc63fc0000

def z823 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0x907337ff38000000 0xc8399bff9c000000

def z824 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0x30833f673fc49d27 0x98419fb39fe24e93

def z825 : W := mkw 0xe830b0e1a8d8c732 0x74185870d46c6399 0xdff0f0e0f9f8e73f 0x6ff878707cfc739f

def z826 : W := mkw 0x01feeedef6324000 0x00ff776f7b192000 0xfd7ffffffe380000 0xfebfffffff1c0000

def z827 : W := mkw 0x0000000000000000 0x0000000000000000 0xef0cc898c607ffff 0xf786644c6303ffff

def z828 : W := mkw 0x006fec0845260000 0x0037f60422930000 0xffffff98c7ff07c1 0xffffffcc63ff83e0

def z829 : W := mkw 0xe881112109d5fd23 0xf440889084eafe91 0x0080000001c4fd27 0x0040000000e27e93

def z830 : W := mkw 0x006fec0001273001 0x0037f60000939800 0x7effff0001fff801 0x3f7fff8000fffc00

def z831 : W := mkw 0xe801112109cc8fa2 0xf400889084e647d1 0x0080000001c49fe7 0x0040000000e24ff3

def z832 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xdff0f0e0f9f86218 0x6ff878707cfc310c

def z833 : W := mkw 0x015e4edef6000000 0x00af276f7b000000 0xf50f3ffffe000000 0xfa879fffff000000

def z834 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xfff3f0e7f9f8e639 0xfff9f873fcfc731c

def z835 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0xffffff0007fff801 0xffffff8003fffc00

def z836 : W := mkw 0x48effd0101b7f903 0xa477fe8080dbfc81 0x7effff0001fff907 0x3f7fff8000fffc83

def z837 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0xffffff98c7fffad9 0xffffffcc63fffd6c

def z838 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0xb473376738000000 0xda399bb39c000000

def z839 : W := mkw 0xc04b002101660500 0x6025801080b30280 0xbeff00ff01ff07c1 0xdf7f807f80ff83e0

def z840 : W := mkw 0x01faa6d6b2324000 0x00fd536b59192000 0x1073376738380000 0x08399bb39c1c0000

def z841 : W := mkw 0x117eecdce42b32cd 0x08bf766e72159966 0x0a7cc098c03b62d8 0x053e604c601db16c

def z842 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0x7c7ffffff8000000 0x3e3ffffffc000000

def z843 : W := mkw 0xa0df4de0a96f3e31 0xd06fa6f054b79f18 0xa10f0fe0f8071e38 0x508787f07c038f1c

def z844 : W := mkw 0x014e4e1e56000000 0x00a7270f2b000000 0x300f3f7f3e000000 0x98079fbf9f000000

def z845 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0x1873f7e7f8000000 0x0c39fbf3fc000000

def z846 : W := mkw 0x017aa6d6b22a0280 0x00bd536b59150140 0x1073376738380000 0x08399bb39c1c0000

def z847 : W := mkw 0x4801030313040902 0xa400818189820481 0xf5033f673e049d27 0xfa819fb39f024e93

def z848 : W := mkw 0xe91002fffe480732 0x7488017fff240399 0x810000fffe00073e 0xc080007fff00039f

def z849 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xbeff00ff01ff9fe7 0xdf7f807f80ffcff3

def z850 : W := mkw 0xe801112109e68d22 0xf400889084f34691 0x0280000001ff9d27 0x0140000000ffce93

def z851 : W := mkw 0x017eeed6b2000000 0x00bf776b59000000 0x187ff76738000000 0x0c3ffbb39c000000

def z852 : W := mkw 0x00a0b5000090c800 0x80505a8000486400 0x10f0370001f80000 0x08781b8000fc0000

def z853 : W := mkw 0xe81002f71a4807a2 0x7408017b8d2403d1 0xef0c08ff3e079fe7 0xf786047f9f03cff3

def z854 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0x6480080001c49d27 0x3240040000e24e93

def z855 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xf7833f673fc79fe7 0xfbc19fb39fe3cff3

def z856 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xff7ffffffe000601 0xffbfffffff000300

def z857 : W := mkw 0x3824fb0afe91f87f 0x9c127d857f48fc3f 0x4100ff00fe00f83e 0x20807f807f007c1f

def z858 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x7effff0007fff907 0xbf7fff8003fffc83

def z859 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xfd7ffffffe006018 0xfebfffffff00300c

def z860 : W := mkw 0x50effd1d45b7f9cd 0xa877fe8ea2dbfce6 0xffffff9fc7ffffff 0xffffffcfe3ffffff

def z861 : W := mkw 0x004a020212000000 0x0025010109000000 0xfd7f3f673e000000 0xfebf9fb39f000000

def z862 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xb4ff007f01ff05c1 0xda7f803f80ff82e0

def z863 : W := mkw 0x00a4fd000091f801 0x80527e800048fc00 0x50f0ff0001f8f800 0x28787f8000fc7c00

def z864 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xff83ff673fc4fd27 0xffc1ffb39fe27e93

def z865 : W := mkw 0xc125ee2bf76e0780 0x6092f715fbb703c0 0x4380ff00ffff07c1 0x21c07f807fff83e0

def z866 : W := mkw 0x007eeec2b2000000 0x003f776159000000 0xfd7fffe7fe000000 0xfebffff3ff000000

def z867 : W := mkw 0xf8144aebfe49377f 0x7c0a2575ff249bbf 0xef0cc8fffe07ffff 0xf786647fff03ffff

def z868 : W := mkw 0x117eecdce401304d 0x08bf766e72009826 0x087cc098c00300c0 0x043e604c60018060

def z869 : W := mkw 0x10044a0a5601304d 0x080225052b009826 0xf50f3f7f3e0719c6 0xfa879fbf9f038ce3

def z870 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0x187f37ff38000000 0x0c3f9bff9c000000

def z871 : W := mkw 0x58cf4f0b5727394f 0xac67a785ab939ca7 0x200f0f1f060719c6 0x9007878f83038ce3

def z872 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xf5833fe7ffc49f3f 0xfac19ff3ffe24f9f

def z873 : W := mkw 0x017eeedef62a0280 0x00bf776f7b150140 0xff7ffffffe3f07c1 0xffbfffffff1f83e0

def z874 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x10f33f0001f81800 0x08799f8000fc0c00

def z875 : W := mkw 0xe881112109ffff33 0xf440889084ffff99 0x0280000001ffff3f 0x0140000000ffff9f

def z876 : W := mkw 0x0134eecaf6000000 0x009a77657b000000 0xfd73ffe7fe000000 0xfeb9fff3ff000000

def z877 : W := mkw 0x11feeedef633704d 0x08ff776f7b19b826 0xff7ffffffe3fffff 0xffbfffffff1fffff

def z878 : W := mkw 0x117eecdce401304d 0x08bf766e72009826 0x087cc098c0006018 0x043e604c6000300c

def z879 : W := mkw 0xf88559294df7fd6f 0xfc42ac94a6fbfeb7 0xef8cc898c7ffffff 0xf7c6644c63ffffff

def z880 : W := mkw 0xe80002231a400522 0x740001118d200291 0xf5033f673e049d27 0xfa819fb39f024e93

def z881 : W := mkw 0xf81002ebfe48077e 0x7c080175ff2403bf 0x810000fffe0007fe 0xc080007fff0003ff

def z882 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0x3c7f376738000000 0x1e3f9bb39c000000

def z883 : W := mkw 0x8030a0e0a0480600 0x4018507050240300 0xdff0f0e0f9f8e639 0x6ff878707cfc731c

def z884 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x12f3370001ff0001 0x09799b8000ff8000

def z885 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0x0280000001c4ff3f 0x0140000000e27f9f

def z886 : W := mkw 0xf801112109efbfef 0xfc00889084f7dff7 0x0280000001ffffff 0x0140000000ffffff

def z887 : W := mkw 0x11cf4f1e5727384d 0x88e7a78f2b939c26 0x200f0f1f060719c6 0x9007878f83038ce3

def z888 : W := mkw 0xe81002e3ba480732 0x74080171dd240399 0xef00c8e7fe04ff3f 0xf7806473ff027f9f

def z889 : W := mkw 0xe801112109dccf32 0xf400889084ee6799 0x0080000001f80000 0x0040000000fc0000

def z890 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x1af0f0e0f9f8e639 0x0d7878707cfc731c

def z891 : W := mkw 0xe80113231bd4cd22 0xf40089918dea6691 0xf7833f673ffcfd27 0xfbc19fb39ffe7e93

def z892 : W := mkw 0x10effd0001b7f84d 0x8877fe8000dbfc26 0x7effff0001fff83f 0x3f7fff8000fffc1f

def z893 : W := mkw 0x00044a0212013001 0x0002250109009800 0xff0fff673e07f801 0xff87ffb39f03fc00

def z894 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0x7c7fff7f3e000000 0xbe3fffbf9f000000

def z895 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x52f3ff0001fff801 0x2979ff8000fffc00

def z896 : W := mkw 0xe80113231bfecfb2 0xf40089918dff67d9 0xf7833f673fffffff 0xfbc19fb39fffffff

def z897 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0xffffff98c1fffef9 0x7fffffcc60ffff7c

def z898 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0x997ff7fffe000000 0xccbffbffff000000

def z899 : W := mkw 0x005a02d612000000 0x002d016b09000000 0xff7f3fff3e079fe7 0xffbf9fff9f03cff3

def z900 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xf58f3f7f3fc79de7 0xfac79fbf9fe3cef3

def z901 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0xbeff379801ff07c1 0xdf7f9bcc00ff83e0

def z902 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x34f3370001fc0001 0x1a799b8000fe0000

def z903 : W := mkw 0x404b001501260180 0x2025800a809300c0 0xbeff009f01ff07c1 0xdf7f804f80ff83e0

def z904 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x5ff0f060f9f8e039 0x2ff878307cfc701c

def z905 : W := mkw 0x00eefd000091f801 0x80777e800048fc00 0x7effff0001f8f801 0x3f7fff8000fc7c00

def z906 : W := mkw 0x017aa6d6b2184210 0x00bd536b590c2108 0x1073376738380000 0x08399bb39c1c0000

def z907 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0x8180000007c49d27 0xc0c0000003e24e93

def z908 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xf5833fff3fc49fe7 0xfac19fff9fe24ff3

def z909 : W := mkw 0x0000020a56000000 0x000001052b000000 0xf5033ffffe000000 0xfa819fffff000000

def z910 : W := mkw 0xa14e5e3e5ed8c630 0x50a72f1f2f6c6318 0x228f0f1f07f8e639 0x9147878f83fc731c

def z911 : W := mkw 0x01effd08e5b7f801 0x80f7fe8472dbfc00 0x7effff00c1fff801 0x3f7fff8060fffc00

def z912 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x50f3f70001f8e000 0x2879fb8000fc7000

def z913 : W := mkw 0x117eecdce419725d 0x08bf766e720cb92e 0x0a7cc098c03b62d8 0x053e604c601db16c

def z914 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x74f3ff0001fcf801 0x3a79ff8000fe7c00

def z915 : W := mkw 0xe81002e31a480722 0x740801718d240391 0x810000e73e000726 0xc08000739f000393

def z916 : W := mkw 0x00effd00a1b7f811 0x8077fe8050dbfc08 0x7effff00c1fff819 0x3f7fff8060fffc0c

def z917 : W := mkw 0x01feeedef6117001 0x00ff776f7b08b800 0xfd7ffffffe006000 0xfebfffffff003000

def z918 : W := mkw 0xe80559294dc48d22 0xf402ac94a6e24691 0xed8cc898c7c49d27 0xf6c6644c63e24e93

def z919 : W := mkw 0x006efc000091f001 0x00377e000048f800 0x7effff0001fff801 0x3f7fff8000fffc00

def z920 : W := mkw 0x004e4e0212000000 0x0027270109000000 0xf50f3f673e000000 0xfa879fb39f000000

def z921 : W := mkw 0x10ebb50845b6c84c 0x8875da8422db6426 0x91f33798c7f807fe 0xc8f99bcc63fc03ff

def z922 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xffff30ff39ff07c1 0xffff987f9cff83e0

def z923 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x10ff370001fb0000 0x087f9b8000fd8000

def z924 : W := mkw 0x0001130213848800 0x8000898109c24400 0xf5833f673fc49d27 0xfac19fb39fe24e93

def z925 : W := mkw 0x017eeedef6013001 0x00bf776f7b009800 0xff7ffffffe036000 0xffbfffffff01b000

def z926 : W := mkw 0x017aa6def6000000 0x00bd536f7b000000 0x11733767fe000000 0x08b99bb3ff000000

def z927 : W := mkw 0xe05b00f5a96e07b0 0x702d807ad4b703d8 0xbeff00ff39ff07c1 0xdf7f807f9cff83e0

def z928 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x53f0f060f9f8e639 0x29f878307cfc731c

def z929 : W := mkw 0xd11002fff64807cc 0x6888017ffb2403e6 0x810000fffe0007fe 0xc080007fff0003ff

def z930 : W := mkw 0xe05b00f5096e07b0 0x702d807a84b703d8 0xbeff00ff01ff07f9 0xdf7f807f80ff83fc

def z931 : W := mkw 0x006ab4000090c000 0x00355a0000486000 0x10f3370001f80000 0x08799b8000fc0000

def z932 : W := mkw 0x30effd08edb7f87d 0x9877fe8476dbfc3e 0xffffff98ffffffff 0xffffffcc7fffffff

def z933 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x3affff0001ff7800 0x1d7fff8000ffbc00

def z934 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x0afcc00001fb6000 0x057e600000fdb000

def z935 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xfd7ffffffe0701c0 0xfebfffffff0380e0

def z936 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x54f3370001f88001 0x2a799b8000fc4000

def z937 : W := mkw 0x017aa6def6000000 0x00bd536f7b000000 0xbd7f37fffe000000 0xdebf9bffff000000

def z938 : W := mkw 0x100448084401304d 0x0802240422009826 0x8b0cc098c607ffff 0xc586604c6303ffff

def z939 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0xf5733f673e049d27 0xfab99fb39f024e93

def z940 : W := mkw 0xa11002f6ba480630 0x5088017b5d240318 0x810000e7f8000638 0x40800073fc00031c

def z941 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x7ef3ff0001fcf801 0x3f79ff8000fe7c00

def z942 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0xffffff80c7fffe3f 0x7fffffc063ffff1f

def z943 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0x51833f673fc49d27 0x28c19fb39fe24e93

def z944 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0xffffff0001fffc21 0x7fffff8000fffe10

def z945 : W := mkw 0x680113031b848922 0xb40089818dc24491 0xf5033f673e049926 0xfa819fb39f024c93

def z946 : W := mkw 0x017eeed6b2000000 0x00bf776b59000000 0x5073ff6738000000 0x2839ffb39c000000

def z947 : W := mkw 0x2030b0c0a898c230 0x10185860544c6118 0x5ff0f080f9f8e239 0x2ff878407cfc711c

def z948 : W := mkw 0x117eeedef600004c 0x08bf776f7b000026 0xfd7ffffffe00003e 0xfebfffffff00001f

def z949 : W := mkw 0x001002d612000000 0x0008016b09000000 0xf5033fff3e000000 0xfa819fff9f000000

def z950 : W := mkw 0x11144adef601304d 0x088a256f7b009826 0xff0ffffffe07ffff 0xff87ffffff03ffff

def z951 : W := mkw 0x00effd0001b6c800 0x8077fe8000db6400 0x7effff0001f8e001 0x3f7fff8000fc7000

def z952 : W := mkw 0x006aa60212000000 0x0035530109000000 0x1073376738000000 0x08399bb39c000000

def z953 : W := mkw 0xe80113231bdccf32 0xf40089918dee6799 0xff83ffe7fffcff3f 0xffc1fff3fffe7f9f

def z954 : W := mkw 0xa01002e2ba480630 0x500801715d240318 0x810000e7fe000638 0xc0800073ff00031c

def z955 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x3eff3f0001ff1801 0x1f7f9f8000ff8c00

def z956 : W := mkw 0x0021b1000194c800 0x8010d88000ca6400 0x10f3370001f80000 0x08799b8000fc0000

def z957 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xbeffc0ffc1ff67d9 0xdf7fe07fe0ffb3ec

def z958 : W := mkw 0x017eeed6b2000000 0x00bf776b59000000 0xfc7fffff38000000 0xfe3fffff9c000000

def z959 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x5affff0001fbf800 0x2d7fff8000fdfc00

def z960 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0x74833f673fc49907 0xba419fb39fe24c83

def z961 : W := mkw 0x0120a602b2000000 0x0090530159000000 0x1003376738000000 0x08019bb39c000000

def z962 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0xffffff9807ffffe7 0xffffffcc03fffff3

def z963 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x3cff370001f80000 0x1e7f9b8000fc0000

def z964 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x8bf0c0e0f9f8e639 0x45f860707cfc731c

def z965 : W := mkw 0x28effd0009b7f823 0x9477fe8004dbfc11 0x7effff0001fff827 0x3f7fff8000fffc13

def z966 : W := mkw 0x280013021a808822 0x940009810d404411 0x51033f673e009826 0x28819fb39f004c13

def z967 : W := mkw 0x005b00d4012e0280 0x002d806a00970140 0xbeff00ff01ff02c1 0xdf7f807f80ff8160

def z968 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0x1afff798c1fb62d8 0x0d7ffbcc60fdb16c

def z969 : W := mkw 0xe81002f71a4807a2 0x7408017b8d2403d1 0x0000006738000000 0x000000339c000000

def z970 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x7cffff0001f8f800 0x3e7fff8000fc7c00

def z971 : W := mkw 0x00eefd0000b3f801 0x80777e800059fc00 0x5efcff0001fbf801 0x2f7e7f8000fdfc00

def z972 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xd1833f673fc09d26 0xe8c19fb39fe04e93

def z973 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xfeff08ff01ff9fc1 0xff7f847f80ffcfe0

def z974 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xf7833f673fc4ff3f 0xfbc19fb39fe27f9f

def z975 : W := mkw 0x0000020212000000 0x0000010109000000 0x20030f0706041906 0x9001878383020c83

def z976 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xbeff08ff07ff1fc7 0xdf7f847f83ff8fe3

def z977 : W := mkw 0x005a02d612000000 0x002d016b09000000 0xbc7f37ff38000000 0xde3f9bff9c000000

def z978 : W := mkw 0xa11002fefe480630 0x5088017f7f240318 0x810000fffe000000 0xc080007fff000000

def z979 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x3eff007f01ff01c1 0x9f7f803f80ff80e0

def z980 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0x917337e7f8000000 0x48b99bf3fc000000

def z981 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x32ff3f0001fff801 0x197f9f8000fffc00

def z982 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0x2080080007c49d27 0x9040040003e24e93

def z983 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xfd7ffffffe040501 0xfebfffffff020280

def z984 : W := mkw 0x1124ee0af601304d 0x089277057b009826 0xf503ff67fe04fd3f 0xfa81ffb3ff027e9f

def z985 : W := mkw 0xd1144afff64937cd 0x688a257ffb249be6 0xef0cc8fffe07ffff 0xf786647fff03ffff

def z986 : W := mkw 0x584f4b1f572739cf 0xac27a58fab939ce7 0x200f0f1f060719c6 0x9007878f83038ce3

def z987 : W := mkw 0x007aa2d6b2000000 0x003d516b59000000 0xfd7ffffffe000000 0xfebfffffff000000

def z988 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xd173fffffe000000 0xe8b9ffffff000000

def z989 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xff833fe73fc49f27 0xffc19ff39fe24f93

def z990 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x5cf3f70001f80000 0x2e79fb8000fc0000

def z991 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x7effff1801fff9c1 0xbf7fff8c00fffce0

def z992 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0x30ff3f1807ff19c6 0x987f9f8c03ff8ce3

def z993 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xe1033f673e049d26 0xf0819fb39f024e93

def z994 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x7effff0001ffffc1 0x3f7fff8000ffffe0

def z995 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x9bf0f0e0f9f86638 0x4df878707cfc331c

def z996 : W := mkw 0x006eee0a56000000 0x003777052b000000 0xfd7ffffffe000000 0xfebfffffff000000

def z997 : W := mkw 0xe801112109ee8fa2 0xf400889084f747d1 0x0280000001ff07c1 0x0140000000ff83e0

def z998 : W := mkw 0x006eee0212013001 0x0037770109009800 0xff7fff673e07fd27 0xffbfffb39f03fe93

def z999 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xf573ff67fe000000 0xfab9ffb3ff000000

def z1000 : W := mkw 0xe801112109fecfb2 0xf400889084ff67d9 0x0280000001ffffff 0x0140000000ffffff

def z1001 : W := mkw 0x0020b1000090c800 0x8010588000486400 0x5ef0ff0001f8f801 0x2f787f8000fc7c00

def z1002 : W := mkw 0xe81002f7ba4807b2 0x7408017bdd2403d9 0x810000fffe0007fe 0xc080007fff0003ff

def z1003 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xffffc8ffc7ffffff 0xffffe47fe3ffffff

def z1004 : W := mkw 0xc81002f712480782 0x6408017b892403c1 0x800000ff060007c6 0xc000007f830003e3

def z1005 : W := mkw 0xc05b00f5a16e0780 0x602d807ad0b703c0 0xbfff00fff9ff07c1 0xdfff807ffcff83e0

def z1006 : W := mkw 0x10effd0001b7f84d 0x8877fe8000dbfc26 0x7effff0001fffad9 0x3f7fff8000fffd6c

def z1007 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xffffc0ffc1ff07c1 0xffffe07fe0ff83e0

def z1008 : W := mkw 0x017eeedef63a4290 0x00bf776f7b1d2148 0xff7ffffffe3b62d8 0xffbfffffff1db16c

def z1009 : W := mkw 0xb11002fefe48067c 0x5888017f7f24033e 0x810000fffe0007fe 0xc080007fff0003ff

def z1010 : W := mkw 0x100448084401304d 0x0802240422009826 0x4b0cc898c607ffff 0x2586644c6303ffff

def z1011 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xfff0f8e0f9fcfe39 0x7ff87c707cfe7f1c

def z1012 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xbfff00ff07ff07e7 0xdfff807f83ff83f3

def z1013 : W := mkw 0x0124ee0af6000000 0x009277057b000000 0xfd0ffffffe000000 0xfe87ffffff000000

def z1014 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0x51f3ff00c7f8f83e 0x28f9ff8063fc7c1f

def z1015 : W := mkw 0x005a02d6122a0280 0x002d016b09150140 0xff7f3fff3e3b02c0 0xffbf9fff9f1d8160

def z1016 : W := mkw 0x00effd0845b7f801 0x8077fe8422dbfc00 0xffffff98c7fffd27 0xffffffcc63fffe93

def z1017 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xfff0f0e0f9fce739 0xfff878707cfe739c

def z1018 : W := mkw 0x017aa6def6000000 0x00bd536f7b000000 0xf5733ffffe000000 0xfab99fffff000000

def z1019 : W := mkw 0xe801112109dccf32 0xf400889084ee6799 0x0080000001fc9d27 0x0040000000fe4e93

def z1020 : W := mkw 0x017eeedef62a0280 0x00bf776f7b150140 0xfd7ffffffe380000 0xfebfffffff1c0000

def z1021 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xfd7ffffffe079de7 0xfebfffffff03cef3

def z1022 : W := mkw 0x00ebb50001b7f801 0x8075da8000dbfc00 0x10f3370001ff1800 0x08799b8000ff8c00

def z1023 : W := mkw 0x00cb110001b7f801 0x8065888000dbfc00 0x7eff3f0001fff801 0x3f7f9f8000fffc00

def z1024 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0x917337673e000000 0xc8b99bb39f000000

def z1025 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xf57f3f7f3e000000 0xfabf9fbf9f000000

def z1026 : W := mkw 0xa030a0e0a8584630 0x50185070542c2318 0x9ff0c0e0f9f86639 0x4ff860707cfc331c

def z1027 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xfd8f3fff3fc49d27 0xfec79fff9fe24e93

def z1028 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0xffffff98c7fff9c7 0xffffffcc63fffce3

def z1029 : W := mkw 0x017eeedef6220000 0x00bf776f7b110000 0xff7ffffffe3b0000 0xffbfffffff1d8000

def z1030 : W := mkw 0x004a021612000000 0x0025010b09000000 0xf50f3f7f3e000000 0xfa879fbf9f000000

def z1031 : W := mkw 0x011002d6b2000000 0x0088016b59000000 0xf5033f673e000000 0xfa819fb39f000000

def z1032 : W := mkw 0x007eeed612000000 0x003f776b09000000 0xfd7fffff3e000000 0xfebfffff9f000000

def z1033 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xfd7ffffffe041906 0xfebfffffff020c83

def z1034 : W := mkw 0xa020b02008d0c420 0x5010581004686210 0xdff0f0e0f9f8e639 0x6ff878707cfc731c

def z1035 : W := mkw 0xf80559294dc5bd6f 0xfc02ac94a6e2deb7 0x4180c800c7c4fd3f 0x20c0640063e27e9f

def z1036 : W := mkw 0x40effd1501b7f981 0xa077fe8a80dbfcc0 0x7effff0701fff801 0x3f7fff8380fffc00

def z1037 : W := mkw 0xe801112109cc8f22 0xf400889084e64791 0x0280000001fc9f27 0x0140000000fe4f93

def z1038 : W := mkw 0xe801112109ee8fa2 0xf400889084f747d1 0x0080000001f80000 0x0040000000fc0000

def z1039 : W := mkw 0x00efed0001377801 0x8077f680009bbc00 0x3effcf0001ff7801 0x1f7fe78000ffbc00

def z1040 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0x7d7fff67fe000000 0x3ebfffb3ff000000

def z1041 : W := mkw 0x00a4fd000091f801 0x80527e800048fc00 0x7efcff0001fff801 0x3f7e7f8000fffc00

def z1042 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xdd7ff7fff8000000 0x6ebffbfffc000000

def z1043 : W := mkw 0x117eeedef600004c 0x08bf776f7b000026 0xfd7ffffffe0002d8 0xfebfffffff00016c

def z1044 : W := mkw 0x0000000000000000 0x0000000000000000 0xd500306038008421 0x6a8018301c004210

def z1045 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xf5833f673fc09826 0xfac19fb39fe04c13

def z1046 : W := mkw 0xc04b0035016e0780 0x6025801a80b703c0 0x3eff001f01ff07c1 0x9f7f800f80ff83e0

def z1047 : W := mkw 0xf801112109c5bd6f 0xfc00889084e2deb7 0x0080000001c79de7 0x0040000000e3cef3

def z1048 : W := mkw 0xf801112109c5bd6f 0xfc00889084e2deb7 0x0080000001c4fd3f 0x0040000000e27e9f

def z1049 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x1aff370001fb0000 0x0d7f9b8000fd8000

def z1050 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0xfeffff98c1ffffd9 0xff7fffcc60ffffec

def z1051 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x1afff70001fff801 0x0d7ffb8000fffc00

def z1052 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xbeff00ff01ffe7f9 0xdf7f807f80fff3fc

def z1053 : W := mkw 0xe80113231bd4cd32 0xf40089918dea6699 0xf5833f673fc4fd3f 0xfac19fb39fe27e9f

def z1054 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xffff08ff07ff07c1 0xffff847f83ff83e0

def z1055 : W := mkw 0x117eeedef62b32cd 0x08bf776f7b159966 0xff7ffffffe3b62d8 0xffbfffffff1db16c

def z1056 : W := mkw 0xa0b0b5e0a8d8ce30 0xd0585af0546c6718 0xdff0f7e0f9f8e639 0x6ff87bf07cfc731c

def z1057 : W := mkw 0x10cf4d084527384d 0x8867a68422939c26 0xffffcf98c7ffffff 0xffffe7cc63ffffff

def z1058 : W := mkw 0xf80559294defbfef 0xfc02ac94a6f7dff7 0xef8cc898c7ffffff 0xf7c6644c63ffffff

def z1059 : W := mkw 0x005b00d401260000 0x002d806a00930000 0xbeff00ff01ff07c1 0xdf7f807f80ff83e0

def z1060 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xfd7ffffffe000638 0xfebfffffff00031c

def z1061 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xfd7ffffffe00fffe 0xfebfffffff007fff

def z1062 : W := mkw 0x0000020212000000 0x0000010109000000 0xf5033f673e041906 0xfa819fb39f020c83

def z1063 : W := mkw 0x017eeedef6184210 0x00bf776f7b0c2108 0xfd7ffffffe380000 0xfebfffffff1c0000

def z1064 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xb0ff00ff01ff07c0 0xd87f807f80ff83e0

def z1065 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xfd7ffffffe07f9fe 0xfebfffffff03fcff

def z1066 : W := mkw 0xe030b0e1a8d8c7b0 0x70185870d46c63d8 0xdff0f0e0f9f8e7f9 0x6ff878707cfc73fc

def z1067 : W := mkw 0x01feeedef63b7211 0x00ff776f7b1db908 0xff7ffffffe3b6218 0xffbfffffff1db10c

def z1068 : W := mkw 0x100448084401304d 0x0802240422009826 0xff0fff98c607ffff 0xff87ffcc6303ffff

def z1069 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0x307f377f38000000 0x983f9bbf9c000000

def z1070 : W := mkw 0xa830b1e0a8d8ce32 0xd41858f0546c6719 0xdff0f0e0f9f8fe3f 0x6ff878707cfc7f1f

def z1071 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0x74733f6738000000 0x3a399fb39c000000

def z1072 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x7efff70001ffe001 0x3f7ffb8000fff000

def z1073 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xff8f3f673fc79d27 0xffc79fb39fe3ce93

def z1074 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x7effff9801fffac1 0x3f7fffcc00fffd60

def z1075 : W := mkw 0x00cf4d0001273801 0x8067a68000939c00 0x30ff0f0001ff1800 0x187f878000ff8c00

def z1076 : W := mkw 0x100448084401304d 0x0802240422009826 0x2a0cc898c607ffff 0x9506644c6303ffff

def z1077 : W := mkw 0x004b110001a68800 0x8025888000d34400 0x74f33f0001fc9801 0x3a799f8000fe4c00

def z1078 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xff7ffffffe07e7f9 0xffbfffffff03f3fc

def z1079 : W := mkw 0x117aa6d6b201304d 0x08bd536b59009826 0x127337673807ffff 0x09399bb39c03ffff

def z1080 : W := mkw 0x005a02d612000000 0x002d016b09000000 0x1073376738000000 0x08399bb39c000000

def z1081 : W := mkw 0x4801030313040902 0xa400818189820481 0x30033f673e041906 0x98019fb39f020c83

def z1082 : W := mkw 0x10effd0001b7f84d 0x8877fe8000dbfc26 0x7effff0001fff9c7 0x3f7fff8000fffce3

def z1083 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0xfeffff9807ffffc7 0xff7fffcc03ffffe3

def z1084 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x9eff00ff01fb06c1 0x4f7f807f80fd8360

def z1085 : W := mkw 0x20effd00a9b7f831 0x9077fe8054dbfc18 0x7effff0039fff801 0x3f7fff801cfffc00

def z1086 : W := mkw 0x017eeed6b2000000 0x00bf776b59000000 0xfd7fffe7f8000000 0x7ebffff3fc000000

def z1087 : W := mkw 0x006aa60212000000 0x0035530109000000 0xf5733f673e000000 0xfab99fb39f000000

def z1088 : W := mkw 0x1000020a5600004c 0x080001052b000026 0xf5033ffffe0007fe 0xfa819fffff0003ff

def z1089 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x10ff007f01fb00c0 0x087f803f80fd8060

def z1090 : W := mkw 0x014a061612000000 0x00a5030b09000000 0x1003376738000000 0x08019bb39c000000

def z1091 : W := mkw 0x0130a2def6000000 0x0098516f7b000000 0xfd73fffffe000000 0xfeb9ffffff000000

def z1092 : W := mkw 0x0124ee0af6000000 0x009277057b000000 0x5103ff67fe000000 0x2881ffb3ff000000

def z1093 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x0af0c080c1f86218 0x0578604060fc310c

def z1094 : W := mkw 0xc85b01f5016e0f82 0xe42d80fa80b707c1 0xbeff00ff01ff1fc7 0xdf7f807f80ff8fe3

def z1095 : W := mkw 0x1034eacaf601304d 0x081a75657b009826 0xff7ffffffe07ffff 0xffbfffffff03ffff

def z1096 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xfd7ffffffe001806 0xfebfffffff000c03

def z1097 : W := mkw 0x0100020af6000000 0x008001057b000000 0xf5033f67fe000000 0xfa819fb3ff000000

def z1098 : W := mkw 0x405b00d501260180 0x202d806a809300c0 0xbeff00ff01ff01c1 0xdf7f807f80ff80e0

def z1099 : W := mkw 0x280013021a808822 0x940009810d404411 0xf5033f673e049d27 0xfa819fb39f024e93

def z1100 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xffff00ff01ff87e1 0xffff807f80ffc3f0

def z1101 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x7fffff0007fff827 0x3fffff8003fffc13

def z1102 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xff7ffffffe00fe3f 0xffbfffffff007f1f

def z1103 : W := mkw 0xa030b0f4a8d8c630 0x5018587a546c6318 0xdff0f0fff9f8e639 0xeff8787ffcfc731c

def z1104 : W := mkw 0x017eeedef6013001 0x00bf776f7b009800 0xfd7ffffffe071800 0xfebfffffff038c00

def z1105 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xff7ffffffe07f83f 0xffbfffffff03fc1f

def z1106 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xfffffffffff80001 0xfffffffffffc0000

def z1107 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xfff33f673ffc9d27 0xfff99fb39ffe4e93

def z1108 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xb1833f673fc41d26 0xd8c19fb39fe20e93

def z1109 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0x75833f673fc49827 0x3ac19fb39fe24c13

def z1110 : W := mkw 0xe05b00f5096e07a0 0x702d807a84b703d0 0xbfff00ff39ff07e1 0xdfff807f9cff83f0

def z1111 : W := mkw 0x38a4ff0a5e91f86f 0x9c527f852f48fc37 0x4100ff00fe00f83e 0x20807f807f007c1f

def z1112 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xff7ffffffe00e001 0xffbfffffff007000

def z1113 : W := mkw 0x016eee1ef6000000 0x00b7770f7b000000 0xf50fff7ffe000000 0xfa87ffbfff000000

def z1114 : W := mkw 0x01044e0a56000000 0x008227052b000000 0xf5033f673e000000 0xfa819fb39f000000

def z1115 : W := mkw 0x004b110001a68800 0x8025888000d34400 0xffff3f9807ff9fe7 0xffff9fcc03ffcff3

def z1116 : W := mkw 0x0025f9000195f801 0x8012fc8000cafc00 0x7effff0001fff801 0x3f7fff8000fffc00

def z1117 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0x597ffffffe000000 0x2cbfffffff000000

def z1118 : W := mkw 0x117eeedef600004c 0x08bf776f7b000026 0xfd7ffffffe0001c6 0xfebfffffff0000e3

def z1119 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xfffcf0f8f9f8e639 0xfffe787c7cfc731c

def z1120 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0xfd73ffe7fe000000 0xfeb9fff3ff000000

def z1121 : W := mkw 0x005e4ade56000000 0x002f256f2b000000 0xfd7ffffffe000000 0xfebfffffff000000

def z1122 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xfd7ffffffe0007c0 0xfebfffffff0003e0

def z1123 : W := mkw 0x005a02d612000000 0x002d016b09000000 0xf5733f673e000000 0xfab99fb39f000000

def z1124 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xfd7ffffffe071ffe 0xfebfffffff038fff

def z1125 : W := mkw 0x015a02def6000000 0x00ad016f7b000000 0xfd7f3ffffe000000 0xfebf9fffff000000

def z1126 : W := mkw 0x20effd0009b7f821 0x9077fe8004dbfc10 0x7fffff0039fff821 0x3fffff801cfffc10

def z1127 : W := mkw 0x017eeed6b2000000 0x00bf776b59000000 0xfd7fff673e000000 0xfebfffb39f000000

def z1128 : W := mkw 0x117eeedef600004c 0x08bf776f7b000026 0xff7ffffffe00e7ff 0xffbfffffff0073ff

def z1129 : W := mkw 0x00effd0845b7f801 0x8077fe8422dbfc00 0x7effff98c1fff801 0x3f7fffcc60fffc00

def z1130 : W := mkw 0x106efc084491f04d 0x08377e042248f826 0xffffff98c7ffffff 0xffffffcc63ffffff

def z1131 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x10f3f70001f86000 0x0879fb8000fc3000

def z1132 : W := mkw 0xc01002f712480780 0x6008017b892403c0 0x810000ff3e0007c0 0xc080007f9f0003e0

def z1133 : W := mkw 0x006ffc0001b6c000 0x0037fe0000db6000 0x7effff0001ffe001 0x3f7fff8000fff000

def z1134 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0xfeffff6701fff801 0xff7fffb380fffc00

def z1135 : W := mkw 0xe030b0f5a8d8c7b0 0x7018587ad46c63d8 0xfffcf0fff9ffe7f9 0xfffe787ffcfff3fc

def z1136 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0x5c73f76738000000 0x2e39fbb39c000000

def z1137 : W := mkw 0x20effd0009b7f831 0x9077fe8004dbfc18 0x7effff0001fff839 0x3f7fff8000fffc1c

def z1138 : W := mkw 0xa030b1e0a8d8ce30 0xd01858f0546c6718 0xdff0ffe0f9f8fe39 0x6ff87ff07cfc7f1c

def z1139 : W := mkw 0x01effd1c45b7f801 0x80f7fe8e22dbfc00 0x7effff1801fff801 0x3f7fff8c00fffc00

def z1140 : W := mkw 0xe801112109ee8fa2 0xf400889084f747d1 0x0080000001fc9d27 0x0040000000fe4e93

def z1141 : W := mkw 0x10cf4d084527384d 0x8867a68422939c26 0xbeff0f9807ff1fc7 0xdf7f87cc03ff8fe3

def z1142 : W := mkw 0x015e4ede56000000 0x00af276f2b000000 0xfd7f3fff3e000000 0xfebf9fff9f000000

def z1143 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xfd7ffffffe000526 0xfebfffffff000293

def z1144 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xfffcf0e0f9ffe639 0x7ffe78707cfff31c

def z1145 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0xa480000001c49d27 0xd240000000e24e93

def z1146 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0xffffff80c1fff801 0x7fffffc060fffc00

def z1147 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0xffffff6039fff801 0x7fffffb01cfffc00

def z1148 : W := mkw 0xe81002e3ba480732 0x74080171dd240399 0x810000e7f8000638 0x40800073fc00031c

def z1149 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x1af3f70001f86000 0x0d79fb8000fc3000

def z1150 : W := mkw 0xa020b020a8d0c430 0x5010581054686218 0xdff0f060f9f8e439 0x6ff878307cfc721c

def z1151 : W := mkw 0x100448084401304d 0x0802240422009826 0xff0cf8f8fe07ffff 0xff867c7c7f03ffff

def z1152 : W := mkw 0x11feeedef633704d 0x08ff776f7b19b826 0xff7ffffffe3b62d8 0xffbfffffff1db16c

def z1153 : W := mkw 0x017eeedef6080210 0x00bf776f7b040108 0xfd7ffffffe000218 0xfebfffffff00010c

def z1154 : W := mkw 0x00efec0001377001 0x0077f600009bb800 0x7effff0001ff6001 0x3f7fff8000ffb000

def z1155 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x3aff00ff01ff03c0 0x9d7f807f80ff81e0

def z1156 : W := mkw 0x10ebb50001b7f84d 0x8875da8000dbfc26 0x12f3370001ffffff 0x09799b8000ffffff

def z1157 : W := mkw 0x00effd0001b6c800 0x8077fe8000db6400 0x7cffff0001fc9801 0x3e7fff8000fe4c00

def z1158 : W := mkw 0x0030b0c0a090c000 0x0018586050486000 0xdff0f0e0f9f8e639 0x6ff878707cfc731c

def z1159 : W := mkw 0xf801112109c48d6e 0xfc00889084e246b7 0x0080000001c49fff 0x0040000000e24fff

def z1160 : W := mkw 0x117eeedef619725d 0x08bf776f7b0cb92e 0xff7ffffffe3fffff 0xffbfffffff1fffff

def z1161 : W := mkw 0x006ab4000090c000 0x00355a0000486000 0x5ef3f70001f8e001 0x2f79fb8000fc7000

def z1162 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xddf0f0e0f9f8e038 0x6ef878707cfc701c

def z1163 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0xae8c009801c79fe7 0xd746004c00e3cff3

def z1164 : W := mkw 0x30effd08edb7f87d 0x9877fe8476dbfc3e 0x7fffff00fffff83f 0x3fffff807ffffc1f

def z1165 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x1ef3370001f80001 0x0f799b8000fc0000

def z1166 : W := mkw 0x017aa6def6000000 0x00bd536f7b000000 0xdd73f7fffe000000 0xeeb9fbffff000000

def z1167 : W := mkw 0xc001022313440500 0x6000811189a20280 0xf5833f673fc49d27 0xfac19fb39fe24e93

def z1168 : W := mkw 0x006fec0001260000 0x0037f60000930000 0x7cffff0001f80000 0x3e7fff8000fc0000

def z1169 : W := mkw 0x00effd1401b7f881 0x8077fe8a00dbfc40 0x7effff1801fff8c1 0x3f7fff8c00fffc60

def z1170 : W := mkw 0x00effd0845b7f801 0x8077fe8422dbfc00 0x7effff1807fff801 0xbf7fff8c03fffc00

def z1171 : W := mkw 0x006ffd0001a68800 0x8037fe8000d34400 0x7effff0001ff9801 0x3f7fff8000ffcc00

def z1172 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x5ef3ff0001f8f801 0x2f79ff8000fc7c00

def z1173 : W := mkw 0x10a4fd084491f84d 0x88527e842248fc26 0xfffcff98c7ffffff 0xfffe7fcc63ffffff

def z1174 : W := mkw 0x2020b000a890c030 0x1010580054486018 0x51f0f000f9f8e038 0x28f878007cfc701c

def z1175 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xd1f0f0e0f9f8e638 0x68f878707cfc731c

def z1176 : W := mkw 0xa030b2e2bad8c630 0x501859715d6c6318 0xfff3ffe7fffcff3f 0xfff9fff3fffe7f9f

def z1177 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0x0080000001c08421 0x0040000000e04210

def z1178 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xbc7f3fff3e000000 0xde3f9fff9f000000

def z1179 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x7effff0001fb6000 0x3f7fff8000fdb000

def z1180 : W := mkw 0xc11002f7b2480780 0x6088017bd92403c0 0x800000ff380007c0 0xc000007f9c0003e0

def z1181 : W := mkw 0x10044a0a5601304d 0x080225052b009826 0xf503ff67fe00f83e 0xfa81ffb3ff007c1f

def z1182 : W := mkw 0x017eeedef6104010 0x00bf776f7b082008 0xfd7ffffffe006018 0xfebfffffff00300c

def z1183 : W := mkw 0x004b010001260800 0x8025808000930400 0x3eff0f0001ff1801 0x1f7f878000ff8c00

def z1184 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x12f3370001f8e001 0x09799b8000fc7000

def z1185 : W := mkw 0x8030a0e0a0584610 0x40185070502c2308 0xdff0f0e0f9f86619 0x6ff878707cfc330c

def z1186 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x2aff009f01ff07c1 0x957f804f80ff83e0

def z1187 : W := mkw 0x117aa6def600004c 0x08bd536f7b000026 0x917337fffe0007fe 0xc8b99bffff0003ff

def z1188 : W := mkw 0x01feeedef6337001 0x00ff776f7b19b800 0xff7ffffffe3ff801 0xffbfffffff1ffc00

def z1189 : W := mkw 0x00efed0001273801 0x8077f68000939c00 0x7effff0001ff1801 0x3f7fff8000ff8c00

def z1190 : W := mkw 0x017eeedef6184210 0x00bf776f7b0c2108 0xff7ffffffe38e639 0xffbfffffff1c731c

def z1191 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xff7ffffffe07fad9 0xffbfffffff03fd6c

def z1192 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0x717fff7ffe000000 0xb8bfffbfff000000

def z1193 : W := mkw 0x0000020212000000 0x0000010109000000 0xf5033f673e040501 0xfa819fb39f020280

def z1194 : W := mkw 0x0000020212000000 0x0000010109000000 0x810000673e000526 0xc08000339f000293

def z1195 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0xf5f33f0007fc9d27 0xfaf99f8003fe4e93

def z1196 : W := mkw 0x00cf5d0001b7f801 0x8067ae8000dbfc00 0x3eff0f0001fff801 0x1f7f878000fffc00

def z1197 : W := mkw 0xc01000f500480780 0x6008007a802403c0 0xbefc00ff01ff07c1 0xdf7e007f80ff83e0

def z1198 : W := mkw 0xc1144afff6480780 0x608a257ffb2403c0 0xef0cc8fffe0707c1 0xf786647fff0383e0

def z1199 : W := mkw 0xc0db05f5016e0f80 0xe06d82fa80b707c0 0xbeff07ff01ff07c1 0xdf7f83ff80ff83e0

def z1200 : W := mkw 0x00ebb50001b7f801 0x8075da8000dbfc00 0x10f3370001f8f800 0x08799b8000fc7c00

def z1201 : W := mkw 0x0120a602b2000000 0x0090530159000000 0xf5033f673e000000 0xfa819fb39f000000

def z1202 : W := mkw 0x006eec0000000000 0x0037760000000000 0x7effff0001f80001 0x3f7fff8000fc0000

def z1203 : W := mkw 0x017eeedef6220080 0x00bf776f7b110040 0xfd7ffffffe0300c0 0xfebfffffff018060

def z1204 : W := mkw 0x017eeed6b2013001 0x00bf776b59009800 0x7e7fff673807f801 0x3f3fffb39c03fc00

def z1205 : W := mkw 0xf80559294dc5bd6f 0xfc02ac94a6e2deb7 0x0a8cc098c1c7ffff 0x0546604c60e3ffff

def z1206 : W := mkw 0xe81002f71a4807a2 0x7408017b8d2403d1 0x810000673e000526 0xc08000339f000293

def z1207 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0xffffff80c7ffff3f 0xffffffc063ffff9f

def z1208 : W := mkw 0xc11002fff6480780 0x6088017ffb2403c0 0x810000fffe000000 0xc080007fff000000

def z1209 : W := mkw 0x105e4ade5601304d 0x082f256f2b009826 0xff7ffffffe07ffff 0xffbfffffff03ffff

def z1210 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xff7ffffffe0767d9 0xffbfffffff03b3ec

def z1211 : W := mkw 0xc05b02f7136e0780 0x602d817b89b703c0 0xffff3fff3fff9fe7 0xffff9fff9fffcff3

def z1212 : W := mkw 0xc01100e1014c0700 0x6008807080a60380 0xbeff00ff01ff07c1 0xdf7f807f80ff83e0

def z1213 : W := mkw 0x0000000000000000 0x0000000000000000 0xb403006700040501 0xda01803380020280

def z1214 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x0afc009801fb02c0 0x057e004c00fd8160

def z1215 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xf5833f673fc41906 0xfac19fb39fe20c83

def z1216 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x7effff0001fffe39 0x3f7fff8000ffff1c

def z1217 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x5ef0f0e0f9f8e219 0x2f7878707cfc710c

def z1218 : W := mkw 0x00ebb50001b7f801 0x8075da8000dbfc00 0x76f33f0001fff801 0x3b799f8000fffc00

def z1219 : W := mkw 0x00044a0212000000 0x0002250109000000 0xfd0fff673e000000 0xfe87ffb39f000000

def z1220 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0x1a7ff7fff80362d8 0x0d3ffbfffc01b16c

def z1221 : W := mkw 0xe05b00f5a96e07b0 0x702d807ad4b703d8 0xffffc0fff9ffe7f9 0xffffe07ffcfff3fc

def z1222 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0x51733f673e000000 0x28b99fb39f000000

def z1223 : W := mkw 0xe881112109e7bd23 0xf440889084f3de91 0x0080000001c79d27 0x0040000000e3ce93

def z1224 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xfeff3fff01ff07c1 0xff7f9fff80ff83e0

def z1225 : W := mkw 0xa0b4fde0a8d9fe31 0xd05a7ef0546cff18 0xc100ffe0f800fe38 0x60807ff07c007f1c

def z1226 : W := mkw 0x40ebb51501b6c980 0xa075da8a80db64c0 0x30ff371f01ff01c0 0x987f9b8f80ff80e0

def z1227 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xff7ffffffe079fe7 0xffbfffffff03cff3

def z1228 : W := mkw 0xe801112109d4cd32 0xf400889084ea6699 0x0080000001c4fd3f 0x0040000000e27e9f

def z1229 : W := mkw 0x0000020212000000 0x0000010109000000 0xf5033f673e000526 0xfa819fb39f000293

def z1230 : W := mkw 0xe8effd2109f7fd23 0xf477fe9084fbfe91 0x0afcc00001fffd27 0x057e600000fffe93

def z1231 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xbeff00ff01fb02c0 0xdf7f807f80fd8160

def z1232 : W := mkw 0x014e4e1e56000000 0x00a7270f2b000000 0xfd0ffffffe000000 0xfe87ffffff000000

def z1233 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0xfd7f3fff3e000000 0xfebf9fff9f000000

def z1234 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0xd573376738000000 0x6ab99bb39c000000

def z1235 : W := mkw 0x0021b1000194c800 0x8010d88000ca6400 0xfff3ff80c7fcff3f 0xfff9ffc063fe7f9f

def z1236 : W := mkw 0xe081112109ffffb1 0xf040889084ffffd8 0x0280000001fffff9 0x0140000000fffffc

def z1237 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0x7effff1807ffffff 0xbf7fff8c03ffffff

def z1238 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x2affcf0001fff801 0x157fe78000fffc00

def z1239 : W := mkw 0x0034eacaf6000000 0x001a75657b000000 0xfd7ffffffe000000 0xfebfffffff000000

def z1240 : W := mkw 0xf80559294dc5bd6f 0xfc02ac94a6e2deb7 0x208c081807c79de7 0x9046040c03e3cef3

def z1241 : W := mkw 0x00a5fd000195f801 0x8052fe8000cafc00 0x7ef3ff0001fcf801 0x3f79ff8000fe7c00

def z1242 : W := mkw 0xe80113231be68da2 0xf40089918df346d1 0xf5833f673fc79de7 0xfac19fb39fe3cef3

def z1243 : W := mkw 0x1124ee0af601304d 0x089277057b009826 0xff0ffffffe07ffff 0xff87ffffff03ffff

def z1244 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0x307f3f7f3e0719c6 0x983f9fbf9f038ce3

def z1245 : W := mkw 0x50effd1d45b7f9cd 0xa877fe8ea2dbfce6 0x7effff1f07fff9c7 0xbf7fff8f83fffce3

def z1246 : W := mkw 0x805a00f4006a0680 0x402d007a00350340 0xbeff00ff01fb06c1 0xdf7f807f80fd8360

def z1247 : W := mkw 0x00a0b5000090c800 0x80505a8000486400 0x5ef0f70001f8e001 0x2f787b8000fc7000

def z1248 : W := mkw 0xe881112109f7fd23 0xf440889084fbfe91 0x0280000001fff801 0x0140000000fffc00

def z1249 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0x0080000001c00526 0x0040000000e00293

def z1250 : W := mkw 0x006ffd000194c800 0x8037fe8000ca6400 0x7effff0001fcf801 0x3f7fff8000fe7c00

def z1251 : W := mkw 0x10effd0001b7f84d 0x8877fe8000dbfc26 0xffffff0007ffffff 0xffffff8003ffffff

def z1252 : W := mkw 0x0000020212000000 0x0000010109000000 0xf5033f673e049801 0xfa819fb39f024c00

def z1253 : W := mkw 0xc0df4df5016f3f81 0xe06fa6fa80b79fc0 0xa00f0fff00071fc0 0xd00787ff80038fe0

def z1254 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xff7ffffffe04ff3f 0xffbfffffff027f9f

def z1255 : W := mkw 0xf80111294dc48d6e 0xfc008894a6e246b7 0x81800098c7c49fff 0xc0c0004c63e24fff

def z1256 : W := mkw 0xf8144aff5e4937ef 0x7c0a257faf249bf7 0xef0cc8fffe07ffff 0xf786647fff03ffff

def z1257 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0x10733f673e000000 0x08399fb39f000000

def z1258 : W := mkw 0x01feeedef6233001 0x00ff776f7b119800 0xfd7ffffffe030000 0xfebfffffff018000

def z1259 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0x5173ff67fe00f83e 0x28b9ffb3ff007c1f

def z1260 : W := mkw 0x114e4e1e5601304d 0x08a7270f2b009826 0xff0ffffffe07ffff 0xff87ffffff03ffff

def z1261 : W := mkw 0x016eee0af6000000 0x00b777057b000000 0xfd7fff67fe000000 0xfebfffb3ff000000

def z1262 : W := mkw 0xe80113231bdccf32 0xf40089918dee6799 0xf5833f673ffc9d27 0xfac19fb39ffe4e93

def z1263 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0x7fffff00c7ffffff 0x3fffff8063ffffff

def z1264 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xdff0f0e0f9fcff3f 0x6ff878707cfe7f9f

def z1265 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0x7fffff18c7fff9ff 0xbfffff8c63fffcff

def z1266 : W := mkw 0x007eecd4a0000000 0x003f766a50000000 0xfd7ffffff8000000 0xfebffffffc000000

def z1267 : W := mkw 0x00effd0845b7f801 0x8077fe8422dbfc00 0xffffff98c7ffffc1 0xffffffcc63ffffe0

def z1268 : W := mkw 0xe801112109c5bd23 0xf400889084e2de91 0x0280000001c7fd27 0x0140000000e3fe93

def z1269 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xff7ffffffe07f9c7 0xffbfffffff03fce3

def z1270 : W := mkw 0x00044a0a56000000 0x000225052b000000 0xf50f3f7f3e000000 0xfa879fbf9f000000

def z1271 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0x7effff1801fff8c1 0x3f7fff8c00fffc60

def z1272 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0x7effff00c1fff819 0x3f7fff8060fffc0c

def z1273 : W := mkw 0xf81002ff5e4807ee 0x7c08017faf2403f7 0x810000fffe0007fe 0xc080007fff0003ff

def z1274 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x3efff70001ff6001 0x1f7ffb8000ffb000

def z1275 : W := mkw 0xe80113231be68d22 0xf40089918df34691 0xf7833f673fff9d27 0xfbc19fb39fffce93

def z1276 : W := mkw 0x10a4fd084491f84d 0x88527e842248fc26 0xdff0ff80c7f8fe3f 0x6ff87fc063fc7f1f

def z1277 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xfffcf8f8ffffffff 0xfffe7c7c7fffffff

def z1278 : W := mkw 0x004b110001a68800 0x8025888000d34400 0x10f3370001f80000 0x08799b8000fc0000

def z1279 : W := mkw 0x3124fe0afe91f07d 0x18927f057f48f83e 0x4100ff00fe00f83e 0x20807f807f007c1f

def z1280 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x30f33f0001fc1800 0x18799f8000fe0c00

def z1281 : W := mkw 0x117eeedef600004c 0x08bf776f7b000026 0xff7ffffffe0707ff 0xffbfffffff0383ff

def z1282 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xfd7ffffffe049801 0xfebfffffff024c00

def z1283 : W := mkw 0x00cb050001260800 0x8065828000930400 0x10f3070001f80000 0x0879838000fc0000

def z1284 : W := mkw 0x111002def600004c 0x0888016f7b000026 0xf5033ffffe049fff 0xfa819fffff024fff

def z1285 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xbcff00ff01ff01c0 0xde7f807f80ff80e0

def z1286 : W := mkw 0x00effd0001b6c800 0x8077fe8000db6400 0x30ff3f0001f80000 0x187f9f8000fc0000

def z1287 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xbfff00ffc1ff07f9 0xdfff807fe0ff83fc

def z1288 : W := mkw 0x0030a2c2b2000000 0x0018516159000000 0x1073376738000000 0x08399bb39c000000

def z1289 : W := mkw 0x40effd0101b7f981 0xa077fe8080dbfcc0 0x7effff0001fff9c1 0x3f7fff8000fffce0

def z1290 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xfd7ffffffe00e038 0xfebfffffff00701c

def z1291 : W := mkw 0x0020a202b2000000 0x0010510159000000 0xf503ff67fe000000 0xfa81ffb3ff000000

def z1292 : W := mkw 0x100448084401304d 0x0802240422009826 0xfffcc898c7ffffff 0xfffe644c63ffffff

def z1293 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xfd7ffffffe04fd3f 0xfebfffffff027e9f

def z1294 : W := mkw 0x00ebb50001b7f801 0x8075da8000dbfc00 0x5ef3f70001fff801 0x2f79fb8000fffc00

def z1295 : W := mkw 0xb1144afefe49367d 0x588a257f7f249b3e 0xef0cc8fffe07ffff 0xf786647fff03ffff

def z1296 : W := mkw 0x00a5fd0001b7f801 0x8052fe8000dbfc00 0x5ef0ff0001fff801 0x2f787f8000fffc00

def z1297 : W := mkw 0x405b00d5012e0380 0x202d806a809701c0 0x3eff009f01ff03c1 0x9f7f804f80ff81e0

def z1298 : W := mkw 0x0800030212000802 0x8400018109000401 0xf5033f673e001806 0xfa819fb39f000c03

def z1299 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x5efff70001fbe001 0x2f7ffb8000fdf000

def z1300 : W := mkw 0x20ebb500a9b6c830 0x9075da8054db6418 0x51f3f700f9f8e038 0x28f9fb807cfc701c

def z1301 : W := mkw 0xe81002e3ba480732 0x74080171dd240399 0x0000006738000000 0x000000339c000000

def z1302 : W := mkw 0x017eeedef6013001 0x00bf776f7b009800 0xff7ffffffe07ffc1 0xffbfffffff03ffe0

def z1303 : W := mkw 0xe881112109f6cd22 0xf440889084fb6691 0x0080000001fc9d27 0x0040000000fe4e93

def z1304 : W := mkw 0xa1144afefe480630 0x508a257f7f240318 0xef0cc8fffe00e639 0xf786647fff00731c

def z1305 : W := mkw 0x0024fc000090c000 0x00127e0000486000 0x5ef0ff0001f8e001 0x2f787f8000fc7000

def z1306 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x50f33f0001f89800 0x28799f8000fc4c00

def z1307 : W := mkw 0x0000020212000000 0x0000010109000000 0xff03ffe7fe00e639 0xff81fff3ff00731c

def z1308 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0x7effff0007fff807 0x3f7fff8003fffc03

def z1309 : W := mkw 0xc05a00f5006a0780 0x602d007a803503c0 0x9efc00ff01fb07c1 0xcf7e007f80fd83e0

def z1310 : W := mkw 0x004b000001260000 0x0025800000930000 0x7eff3f0001ff0001 0x3f7f9f8000ff8000

def z1311 : W := mkw 0x0100021e56000000 0x0080010f2b000000 0xf5033f7f3e000000 0xfa819fbf9f000000

def z1312 : W := mkw 0xa80013221ac08c22 0xd40009910d604611 0xf5833f673fc09c27 0xfac19fb39fe04e13

def z1313 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xfd7ffffffe0300c0 0xfebfffffff018060

def z1314 : W := mkw 0x00effd0001b6c800 0x8077fe8000db6400 0x50f3ff0001f80000 0x2879ff8000fc0000

def z1315 : W := mkw 0x0000020212000000 0x0000010109000000 0x30033f673e000000 0x98019fb39f000000

def z1316 : W := mkw 0xe881112109f6cd22 0xf440889084fb6691 0x0080000001f80000 0x0040000000fc0000

def z1317 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0xffffff98c1fffff9 0xffffffcc60fffffc

def z1318 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xff7ffffffe03e6f9 0xffbfffffff01f37c

def z1319 : W := mkw 0xa81002e2ba480632 0x540801715d240319 0x810000e0fe00063e 0x408000707f00031f

def z1320 : W := mkw 0xe80113231bcc8fa2 0xf40089918de647d1 0xf5833f673fc49fe7 0xfac19fb39fe24ff3

def z1321 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xdff0f0f8f9f8e7f9 0xeff8787c7cfc73fc

def z1322 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0x0080000001c40501 0x0040000000e20280

def z1323 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x7effff80c1fffa19 0x3f7fffc060fffd0c

def z1324 : W := mkw 0x0000020212000000 0x0000010109000000 0xf5033f673e008421 0xfa819fb39f004210

def z1325 : W := mkw 0xe805592109c5bd23 0xf402ac9084e2de91 0x6e8cc80001c7fd27 0x3746640000e3fe93

def z1326 : W := mkw 0x0021b1000194c800 0x8010d88000ca6400 0x5ef3f70001f8e001 0x2f79fb8000fc7000

def z1327 : W := mkw 0x0000020212000000 0x0000010109000000 0xfd0f3fff3e000000 0xfe879fff9f000000

def z1328 : W := mkw 0xf801112109ddff7f 0xfc00889084eeffbf 0x0280000001ffffff 0x0140000000ffffff

def z1329 : W := mkw 0x40ebb51501b6c980 0xa075da8a80db64c0 0x10f3370701f80000 0x08799b8380fc0000

def z1330 : W := mkw 0x017eeedef6013001 0x00bf776f7b009800 0xff7ffffffe07fe39 0xffbfffffff03ff1c

def z1331 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0xfd7ff7fff8000000 0xfebffbfffc000000

def z1332 : W := mkw 0x0030a2c2b2000000 0x0018516159000000 0xf5733f673e000000 0xfab99fb39f000000

def z1333 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0x71833f673fc49926 0xb8c19fb39fe24c93

def z1334 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xd5f0f060f9f8e439 0x6af878307cfc721c

def z1335 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xdff0f0e0f9ffe7f9 0x6ff878707cfff3fc

def z1336 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0x0080000001c09826 0x0040000000e04c13

def z1337 : W := mkw 0x0000020212000000 0x0000010109000000 0x74033f6738000000 0x3a019fb39c000000

def z1338 : W := mkw 0x00cf4d0001273801 0x8067a68000939c00 0x7effcf0001fff801 0x3f7fe78000fffc00

def z1339 : W := mkw 0x017eeedef6080200 0x00bf776f7b040100 0xff7ffffffe380200 0xffbfffffff1c0100

def z1340 : W := mkw 0x00ebb50001b7f801 0x8075da8000dbfc00 0x3eff370001fff801 0x1f7f9b8000fffc00

def z1341 : W := mkw 0xe80113231bcc8f22 0xf40089918de64791 0xf7833f673ffc9f27 0xfbc19fb39ffe4f93

def z1342 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xd5833f673fc09c27 0x6ac19fb39fe04e13

def z1343 : W := mkw 0x00effd0001b6c800 0x8077fe8000db6400 0x18fff70001f80000 0x0c7ffb8000fc0000

def z1344 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0x387ffffffe000000 0x9c3fffffff000000

def z1345 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0x0280000001c79fe7 0x0140000000e3cff3

def z1346 : W := mkw 0xa11002f6ba480630 0x5088017b5d240318 0x0000006738000000 0x000000339c000000

def z1347 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0x9ef0f0e0f9f86619 0x4f7878707cfc330c

def z1348 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0x4180080007c49d27 0x20c0040003e24e93

def z1349 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0x1073f767f8000000 0x0839fbb3fc000000

def z1350 : W := mkw 0x2030b0c0a890c030 0x1018586054486018 0xdff0f0e0f9f8e039 0x6ff878707cfc701c

def z1351 : W := mkw 0x00cf5d0001a7b801 0x8067ae8000d3dc00 0x7eff3f0001ff9801 0x3f7f9f8000ffcc00

def z1352 : W := mkw 0xe80013231ac08d22 0xf40009918d604691 0xf5033f673e009d26 0xfa819fb39f004e93

def z1353 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xff8fffffffc7ffff 0xffc7ffffffe3ffff

def z1354 : W := mkw 0x00effd0001b6c800 0x8077fe8000db6400 0x7effff0001ff0001 0x3f7fff8000ff8000

def z1355 : W := mkw 0x0000020212000000 0x0000010109000000 0xb403376738000000 0xda019bb39c000000

def z1356 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xbc7ff7fff8000000 0xde3ffbfffc000000

def z1357 : W := mkw 0x017aa6d6b2184210 0x00bd536b590c2108 0x1a73f7e7f8386218 0x0d39fbf3fc1c310c

def z1358 : W := mkw 0xe801112109dccf32 0xf400889084ee6799 0x0280000001f8e639 0x0140000000fc731c

def z1359 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xff7ffffffe077bde 0xffbfffffff03bdef

def z1360 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0xfeffc0ff01ffe7c1 0xff7fe07f80fff3e0

def z1361 : W := mkw 0x0020a20212000000 0x0010510109000000 0xfd73ff673e000000 0xfeb9ffb39f000000

def z1362 : W := mkw 0x20ebb500a9b6c830 0x9075da8054db6418 0x10f3370039f80000 0x08799b801cfc0000

def z1363 : W := mkw 0x017eeedef6104000 0x00bf776f7b082000 0xff7ffffffe386000 0xffbfffffff1c3000

def z1364 : W := mkw 0xc04b003501660580 0x6025801a80b302c0 0xbeff007f01ff05c1 0xdf7f803f80ff82e0

def z1365 : W := mkw 0xe11002fffe4807b0 0x7088017fff2403d8 0x810000fffe0007f8 0xc080007fff0003fc

def z1366 : W := mkw 0x00efff0213b7f801 0x8077ff8109dbfc00 0xffffff673ffffd27 0xffffffb39ffffe93

def z1367 : W := mkw 0xa11002eafe480630 0x508801757f240318 0x810000e0fe000638 0x408000707f00031c

def z1368 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x7cffff0001ff1800 0x3e7fff8000ff8c00

def z1369 : W := mkw 0x10effd0001b7f84d 0x8877fe8000dbfc26 0xfeffff9801ffffff 0xff7fffcc00ffffff

def z1370 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0x7fffff98c7fffaff 0x3fffffcc63fffd7f

def z1371 : W := mkw 0x4801130313848902 0xa400898189c24481 0xf5833f673fc49907 0xfac19fb39fe24c83

def z1372 : W := mkw 0x0001110001848800 0x8000888000c24400 0x7ef33f0001fc9801 0x3f799f8000fe4c00

def z1373 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x10f3370001fc9801 0x08799b8000fe4c00

def z1374 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xfd7ffffffe008421 0xfebfffffff004210

def z1375 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0x10833f673fc01806 0x08419fb39fe00c03

def z1376 : W := mkw 0xa030b0f4a8d8c6b0 0x5018587a546c6358 0xdff0f0f8f9f8e6f9 0x6ff8787c7cfc737c

def z1377 : W := mkw 0x00effd00a1b7f801 0x8077fe8050dbfc00 0x7fffff00f9fff801 0x3fffff807cfffc00

def z1378 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0x9c7337e738000000 0x4e399bf39c000000

def z1379 : W := mkw 0x004f4c0001260000 0x0027a60000930000 0x3eff0f0001ff0001 0x1f7f878000ff8000

def z1380 : W := mkw 0x006efc000090c000 0x00377e0000486000 0x7cffff0001f80000 0x3e7fff8000fc0000

def z1381 : W := mkw 0xc11002f7b2480780 0x6088017bd92403c0 0x0000006738000000 0x000000339c000000

def z1382 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xff7ffffffe070001 0xffbfffffff038000

def z1383 : W := mkw 0x00effd0845b7f801 0x8077fe8422dbfc00 0xffffff98c7fffe39 0xffffffcc63ffff1c

def z1384 : W := mkw 0x00eefc0000b3f001 0x00777e000059f800 0x7effff0001fbe001 0x3f7fff8000fdf000

def z1385 : W := mkw 0xe80113231bcc8f32 0xf40089918de64799 0xf5833f673fc49f3f 0xfac19fb39fe24f9f

def z1386 : W := mkw 0x100448084401304d 0x0802240422009826 0xe10cc898c607fffe 0xf086644c6303ffff

def z1387 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xf583ff67ffc4fd3f 0xfac1ffb3ffe27e9f

def z1388 : W := mkw 0x00ebb50001b6c800 0x8075da8000db6400 0x30ff370001ff0000 0x187f9b8000ff8000

def z1389 : W := mkw 0x00effd0845b7f801 0x8077fe8422dbfc00 0x7fffff00c7fff801 0x3fffff8063fffc00

def z1390 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xe10ffffffe000000 0xf087ffffff000000

def z1391 : W := mkw 0x017eeedef6013001 0x00bf776f7b009800 0xff7ffffffe07fd27 0xffbfffffff03fe93

def z1392 : W := mkw 0xe801112109c48d22 0xf400889084e24691 0x0080000001c49801 0x0040000000e24c00

def z1393 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x70ffff0001fff800 0x387fff8000fffc00

def z1394 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0x5173f767f8000000 0x28b9fbb3fc000000

def z1395 : W := mkw 0x006efc084490c000 0x00377e0422486000 0xffffff98c7f8e639 0xffffffcc63fc731c

def z1396 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0xdf73f7e7f800e639 0x6fb9fbf3fc00731c

def z1397 : W := mkw 0x006eee0212000000 0x0037770109000000 0x7c7fff6738000000 0x3e3fffb39c000000

def z1398 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xfd83ffe7ffc49d27 0xfec1fff3ffe24e93

def z1399 : W := mkw 0x10effd0001b7f84d 0x8877fe8000dbfc26 0xffffff80c1ffffff 0x7fffffc060ffffff

def z1400 : W := mkw 0x00ebb50001b7f801 0x8075da8000dbfc00 0x12f3370001fb6000 0x09799b8000fdb000

def z1401 : W := mkw 0xa01010e008c88620 0x5008087004644310 0xdff0f0e0f9f8e639 0x6ff878707cfc731c

def z1402 : W := mkw 0x104f590845a7b84d 0x8827ac8422d3dc26 0xffffff98c7ffffff 0xffffffcc63ffffff

def z1403 : W := mkw 0xe881112109ffffa3 0xf440889084ffffd1 0x0280000001ffffe7 0x0140000000fffff3

def z1404 : W := mkw 0x0024ee0212000000 0x0012770109000000 0xf503ff673e000000 0xfa81ffb39f000000

def z1405 : W := mkw 0x017aa6d6b2000000 0x00bd536b59000000 0xbe7f37ff380707c1 0xdf3f9bff9c0383e0

def z1406 : W := mkw 0x00044a0a56000000 0x000225052b000000 0xf503ff67fe000000 0xfa81ffb3ff000000

def z1407 : W := mkw 0x20effd00a9b7f831 0x9077fe8054dbfc18 0xffffff80f9fffe39 0x7fffffc07cffff1c

def z1408 : W := mkw 0x117eeedef601304d 0x08bf776f7b009826 0xff7ffffffe071fc7 0xffbfffffff038fe3

def z1409 : W := mkw 0x014a061612000000 0x00a5030b09000000 0xf5033f673e000000 0xfa819fb39f000000

def z1410 : W := mkw 0x017eeed6b2000000 0x00bf776b59000000 0x307f3f6738000000 0x183f9fb39c000000

def z1411 : W := mkw 0x0000000000000000 0x0000000000000000 0x74033f0000049801 0x3a019f8000024c00

def z1412 : W := mkw 0x004b110001a68800 0x8025888000d34400 0x3eff370001ff0001 0x1f7f9b8000ff8000

def z1413 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0xfeffff0001fffd01 0xff7fff8000fffe80

def z1414 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x74ff3f0001ff9801 0x3a7f9f8000ffcc00

def z1415 : W := mkw 0xc05b00f5016e0780 0x602d807a80b703c0 0x9aff00ff01fb07c0 0xcd7f807f80fd83e0

def z1416 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0xffffff1807fffde7 0xffffff8c03fffef3

def z1417 : W := mkw 0x10effd0845b7f84d 0x8877fe8422dbfc26 0xffffff00c7fffd3f 0xffffff8063fffe9f

def z1418 : W := mkw 0xa020b020a8d8c630 0x50105810546c6318 0x5ff0f000f9f8e639 0x2ff878007cfc731c

def z1419 : W := mkw 0x00effd0001b7f801 0x8077fe8000dbfc00 0x7effff0001fffd27 0x3f7fff8000fffe93

def z1420 : W := mkw 0x0030a2c2b2184210 0x00185161590c2108 0xff73ffe7fe386218 0xffb9fff3ff1c310c

def z1421 : W := mkw 0x00cb050001260800 0x8065828000930400 0x3eff070001ff0001 0x1f7f838000ff8000

def z1422 : W := mkw 0x004f590001a7b801 0x8027ac8000d3dc00 0x7effff0001fff801 0x3f7fff8000fffc00

def z1423 : W := mkw 0xe80113231bc48d22 0xf40089918de24691 0xb4833f673fc41d07 0xda419fb39fe20e83

def z1424 : W := mkw 0x017eeedef6000000 0x00bf776f7b000000 0xfd7ffffffe009826 0xfebfffffff004c13

def z1425 : W := mkw 0x0000020212000000 0x0000010109000000 0xff0f3fff3e0707c1 0xff879fff9f0383e0

def z1426 : W := mkw 0x0134eedef6000000 0x009a776f7b000000 0xf503fffffe000000 0xfa81ffffff000000

def z1427 : W := mkw 0x00eeee0212337001 0x007777010919b800 0xff7fff673e3b6000 0xffbfffb39f1db000

def z1428 : W := mkw 0x011002def6000000 0x0088016f7b000000 0x910337fffe000000 0xc8819bffff000000

def z1429 : W := mkw 0x01feeedef63b7281 0x00ff776f7b1db940 0xff7ffffffe3b62c0 0xffbfffffff1db160

def z1430 : W := mkw 0xa030b0e0a8d8c630 0x50185870546c6318 0xdffcf0f8f9fbe6f9 0x6ffe787c7cfdf37c

def z1431 : W := mkw 0x0030a2c2b2000000 0x0018516159000000 0xdd73f7e7f8000000 0x6eb9fbf3fc000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z4,z8,z5,z6]),(0,[z9,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z10,z4,z5,z6]),(0,[z7,z1,z2,z11,z4,z5,z6])],[(0,[z12,z7,z13,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z6]),(0,[z7,z2,z14,z4,z15,z5,z6])],[(0,[z12,z7,z2,z4,z16,z5,z6]),(0,[z7,z1,z2,z4,z5,z17,z6]),(1,[z1,z2,z4,z5,z6,z18])],[(0,[z7,z19,z1,z2,z4,z5,z6])],[(0,[z20,z7,z2,z21,z4,z5,z6]),(0,[z7,z1,z2,z22,z4,z5,z6]),(0,[z7,z1,z23,z2,z4,z5,z6]),(0,[z24,z7,z1,z2,z4,z5,z6])],[(0,[z1,z2,z25,z4,z5,z26,z6])],[(0,[z27,z7,z1,z2,z4,z5,z6]),(0,[z20,z7,z1,z2,z5,z28,z6]),(1,[z7,z2,z4,z5,z6,z29]),(0,[z30,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z31,z4,z5,z6]),(1,[z32,z7,z2,z4,z5,z6])],[(0,[z20,z33,z1,z2,z4,z5,z6]),(0,[z34,z12,z7,z2,z4,z5,z6]),(0,[z35,z7,z1,z36,z4,z5,z6])],[(0,[z37,z1,z2,z4,z38,z5,z6]),(0,[z39,z12,z7,z2,z4,z5,z6])],[(0,[z7,z1,z2,z40,z4,z5,z6]),(1,[z7,z1,z2,z41,z4,z5]),(0,[z7,z1,z2,z42,z5,z6,z43])],[(0,[z7,z1,z2,z44,z4,z5,z6]),(0,[z7,z1,z2,z45,z4,z5,z6]),(0,[z7,z1,z2,z46,z4,z5,z6])],[(0,[z20,z0,z1,z2,z4,z5,z6]),(0,[z47,z12,z7,z2,z4,z5,z6]),(0,[z7,z1,z48,z2,z4,z5,z6])],[(0,[z1,z2,z25,z14,z4,z5,z6]),(0,[z7,z49,z1,z2,z4,z5,z50])],[(0,[z51,z7,z1,z2,z4,z52,z6])],[(0,[z12,z7,z36,z2,z4,z5,z6])],[(0,[z7,z1,z2,z53,z4,z5,z6]),(0,[z54,z55,z1,z2,z4,z5,z6]),(0,[z7,z56,z2,z57,z4,z5,z6])]],
   [[(0,[z7,z1,z2,z4,z58,z5,z6]),(0,[z59,z7,z1,z2,z4,z5,z6])],[(0,[z1,z2,z25,z60,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z61,z6]),(0,[z7,z1,z2,z4,z62,z28,z6]),(0,[z63,z7,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z15,z5,z6]),(0,[z7,z1,z2,z4,z15,z5,z6]),(0,[z12,z7,z56,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z50,z6,z64]),(0,[z7,z1,z2,z65,z4,z5,z6])],[(0,[z7,z1,z66,z2,z4,z5,z6]),(1,[z12,z0,z2,z4,z5,z6])],[(0,[z51,z1,z2,z25,z4,z5,z6]),(0,[z0,z1,z2,z4,z67,z5,z6])],[(0,[z7,z2,z21,z4,z52,z5,z6]),(0,[z7,z1,z2,z4,z68,z5,z6]),(0,[z7,z1,z2,z69,z4,z5,z6])],[(0,[z59,z7,z1,z2,z4,z28,z6]),(1,[z1,z2,z70,z4,z5,z6]),(0,[z7,z1,z2,z71,z5,z6,z43])],[(0,[z20,z7,z72,z2,z4,z5,z6]),(0,[z54,z7,z1,z2,z4,z5,z73]),(0,[z7,z1,z2,z4,z74,z5,z6])],[(0,[z7,z1,z2,z4,z5,z75,z6]),(0,[z7,z1,z76,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z77])],[(1,[z7,z2,z78,z4,z5,z6])],[(0,[z7,z72,z2,z4,z79,z5,z6]),(0,[z80,z7,z2,z4,z5,z6,z43])],[(0,[z1,z2,z25,z42,z4,z5,z6]),(0,[z54,z1,z2,z3,z4,z5,z6]),(0,[z59,z7,z2,z4,z5,z50,z6]),(0,[z81,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z82]),(0,[z7,z1,z2,z69,z4,z28,z6])],[(0,[z7,z2,z4,z5,z50,z6,z73])],[(0,[z83,z7,z1,z2,z4,z5,z6]),(0,[z7,z2,z84,z4,z5,z50,z6])],[(0,[z7,z1,z2,z4,z85,z5,z6]),(0,[z86,z7,z2,z4,z5,z50,z6]),(0,[z7,z1,z2,z4,z5,z6,z87]),(0,[z7,z1,z2,z88,z4,z5,z6])],[(0,[z89,z7,z1,z2,z4,z5,z6]),(0,[z7,z72,z2,z4,z52,z5,z6]),(0,[z7,z49,z1,z2,z71,z4,z5]),(0,[z39,z7,z1,z2,z90,z5,z6])]],
   [[(0,[z91,z1,z2,z4,z5,z92,z6]),(1,[z7,z93,z2,z4,z5,z6])],[(0,[z7,z1,z2,z94,z4,z5,z6]),(0,[z7,z1,z2,z95,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z96]),(0,[z35,z12,z7,z2,z4,z5,z6]),(0,[z7,z1,z2,z97,z4,z5,z6]),(0,[z7,z1,z98,z2,z4,z5,z6])],[(0,[z0,z1,z99,z2,z4,z5,z6]),(1,[z0,z1,z100,z4,z5,z6]),(0,[z7,z101,z72,z2,z4,z5,z6]),(0,[z9,z1,z56,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z102,z6]),(0,[z103,z7,z1,z2,z4,z5,z6])],[(0,[z104,z7,z1,z25,z4,z5,z6]),(0,[z105,z0,z1,z2,z4,z5,z6]),(0,[z7,z72,z2,z3,z4,z5,z6]),(0,[z7,z2,z21,z4,z106,z5,z6]),(0,[z7,z1,z2,z107,z4,z5,z6])],[(0,[z1,z2,z25,z4,z5,z108,z6]),(0,[z7,z2,z4,z5,z50,z50,z6])],[(0,[z0,z1,z2,z4,z5,z109,z6]),(0,[z12,z7,z2,z4,z110,z5,z6]),(0,[z12,z7,z2,z4,z5,z111,z6]),(0,[z7,z1,z2,z4,z5,z109,z6]),(1,[z12,z7,z2,z4,z5,z43]),(0,[z7,z1,z2,z4,z5,z112,z6])],[(0,[z1,z2,z25,z71,z4,z5,z6])],[(0,[z7,z1,z2,z4,z113,z5,z6]),(0,[z114,z7,z1,z2,z4,z115,z6]),(0,[z116,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z117,z4,z5,z6])],[(0,[z89,z7,z2,z4,z5,z50,z6]),(0,[z7,z1,z2,z4,z5,z118,z6]),(0,[z32,z7,z1,z2,z4,z5,z6])],[(0,[z0,z1,z119,z2,z4,z5,z6]),(0,[z120,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z119,z2,z4,z5,z6])],[(0,[z1,z2,z25,z4,z5,z62,z6]),(0,[z121,z7,z1,z2,z4,z5,z6]),(1,[z122,z1,z2,z4,z5,z6])],[(0,[z7,z2,z21,z4,z15,z5,z6]),(0,[z7,z1,z2,z123,z4,z5,z6]),(0,[z7,z2,z4,z67,z5,z50,z6]),(0,[z124,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z125,z4,z5,z6]),(0,[z7,z1,z126,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z67,z5,z127])],[(0,[z12,z33,z7,z2,z4,z5,z6]),(1,[z7,z72,z21,z4,z5,z6]),(0,[z12,z7,z2,z128,z4,z5,z6]),(0,[z7,z1,z2,z129,z5,z28,z6])],[(0,[z7,z2,z21,z4,z67,z5,z6]),(0,[z7,z1,z2,z4,z130,z5,z6]),(0,[z7,z1,z2,z4,z5,z131,z6]),(0,[z132,z7,z1,z2,z4,z5,z6])]],
   [[],[(0,[z7,z1,z2,z4,z5,z6,z133]),(0,[z7,z76,z2,z4,z5,z50,z6]),(0,[z7,z1,z134,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z26,z6]),(0,[z12,z0,z7,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z135]),(0,[z136,z7,z1,z2,z4,z5,z6]),(0,[z35,z7,z1,z2,z137,z5,z6])],[(0,[z138,z7,z1,z2,z4,z5,z6]),(0,[z20,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z139])],[],[(0,[z140,z0,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z141,z5,z6]),(0,[z142,z7,z1,z2,z4,z5,z6])],[(0,[z143,z7,z1,z2,z4,z5,z6]),(0,[z0,z7,z2,z21,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z144,z6]),(0,[z7,z1,z4,z5,z26,z6,z145])],[(0,[z7,z1,z2,z4,z146,z5,z6]),(0,[z7,z72,z2,z4,z15,z5,z6])],[(0,[z7,z1,z2,z4,z79,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z147]),(0,[z12,z7,z2,z4,z5,z6,z145])],[(0,[z148,z1,z2,z25,z4,z5,z6]),(0,[z7,z1,z2,z149,z4,z5,z6]),(0,[z7,z72,z2,z4,z67,z5,z6])],[(0,[z7,z2,z4,z5,z50,z6,z150])],[(0,[z20,z7,z1,z2,z4,z5,z6]),(0,[z7,z2,z21,z129,z4,z5,z6]),(0,[z7,z1,z2,z151,z4,z5,z6])],[(0,[z7,z152,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z2,z4,z5,z6]),(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z153]),(0,[z7,z1,z2,z4,z5,z154,z6]),(1,[z155,z1,z2,z4,z5,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(1,[z59,z1,z2,z4,z38,z6]),(0,[z7,z2,z4,z5,z6,z156,z145]),(0,[z7,z1,z2,z157,z4,z5,z6])],[(1,[z7,z1,z2,z46,z5,z6]),(0,[z7,z1,z2,z4,z5,z158,z6])],[(0,[z159,z7,z1,z2,z4,z5,z6]),(0,[z114,z7,z1,z2,z4,z5,z112]),(0,[z7,z1,z2,z160,z4,z5,z6])]],
   [[(1,[z7,z66,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z161,z5,z6]),(0,[z12,z7,z2,z4,z5,z6,z43]),(0,[z7,z1,z2,z162,z4,z5,z6]),(0,[z163,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z164]),(0,[z7,z1,z2,z4,z5,z165,z6]),(0,[z7,z1,z2,z4,z5,z166,z6])],[(0,[z37,z1,z2,z25,z4,z5,z6]),(0,[z7,z99,z2,z21,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z167]),(0,[z7,z1,z2,z4,z5,z6,z167]),(0,[z168,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z60,z5,z6,z43])],[(0,[z7,z1,z169,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z50,z6,z170]),(0,[z7,z1,z2,z4,z52,z28,z6])],[],[(0,[z55,z7,z171,z2,z4,z5,z6]),(0,[z7,z1,z2,z172,z4,z5,z6]),(0,[z1,z2,z128,z173,z4,z5,z6]),(0,[z7,z1,z2,z4,z174,z5,z6])],[(0,[z20,z7,z2,z4,z5,z50,z6]),(0,[z175,z12,z7,z2,z4,z5,z6])],[(0,[z7,z176,z1,z2,z4,z5,z6]),(0,[z7,z101,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z177,z5,z6]),(0,[z7,z36,z2,z4,z5,z50,z6]),(0,[z7,z2,z4,z5,z178,z26,z6])],[(0,[z7,z72,z99,z2,z4,z5,z6])],[(0,[z0,z7,z72,z2,z4,z5,z6]),(0,[z12,z7,z2,z179,z4,z5,z6])],[(0,[z7,z72,z1,z21,z4,z5,z6]),(0,[z7,z180,z1,z2,z4,z5,z6])],[(0,[z37,z7,z99,z2,z4,z5,z6]),(0,[z7,z1,z181,z2,z4,z5,z6]),(0,[z39,z182,z1,z2,z4,z5,z6]),(1,[z7,z183,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z26,z127])],[(0,[z7,z1,z2,z4,z5,z6,z184]),(0,[z55,z7,z185,z2,z4,z5,z6]),(0,[z7,z1,z186,z2,z4,z5,z6]),(0,[z7,z72,z2,z4,z5,z109,z6]),(0,[z187,z7,z1,z2,z4,z5,z6]),(1,[z12,z7,z2,z4,z5,z188]),(0,[z7,z1,z2,z60,z5,z28,z6]),(0,[z124,z1,z36,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z189,z6])],[(0,[z7,z190,z1,z2,z4,z5,z6]),(0,[z7,z2,z21,z4,z5,z26,z6]),(0,[z7,z1,z2,z4,z106,z5,z6]),(0,[z191,z7,z1,z2,z4,z5,z6]),(0,[z192,z7,z1,z2,z4,z5,z6])],[(0,[z1,z100,z2,z25,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z193,z6]),(0,[z55,z7,z2,z21,z4,z5,z6]),(0,[z7,z1,z2,z4,z194,z5,z6])],[(0,[z7,z49,z1,z2,z4,z5,z43]),(0,[z7,z1,z2,z4,z5,z195,z6]),(1,[z196,z1,z2,z4,z5,z6]),(1,[z7,z1,z2,z4,z197,z6]),(0,[z7,z1,z119,z2,z4,z5,z26])]],
   [[(0,[z7,z1,z2,z4,z5,z198,z6]),(0,[z7,z72,z119,z2,z4,z5,z6]),(0,[z199,z7,z1,z2,z4,z5,z6])],[(0,[z91,z1,z2,z25,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z200,z6]),(0,[z201,z7,z1,z2,z4,z5,z6])],[(0,[z7,z2,z4,z16,z5,z50,z6])],[(0,[z1,z2,z25,z4,z16,z5,z6]),(0,[z54,z20,z1,z2,z4,z5,z6])],[(0,[z12,z7,z2,z21,z4,z5,z6]),(0,[z7,z1,z2,z202,z4,z5,z6])],[(0,[z105,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z203,z4,z5,z6]),(0,[z7,z56,z2,z4,z5,z50,z6]),(1,[z9,z1,z2,z4,z5,z6])],[(0,[z91,z37,z1,z2,z4,z5,z6]),(0,[z86,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z56,z2,z16,z5,z6]),(0,[z204,z7,z205,z2,z4,z5,z6])],[(0,[z72,z1,z2,z25,z4,z5,z6]),(0,[z7,z72,z2,z4,z5,z26,z6]),(1,[z7,z2,z4,z5,z118,z6]),(0,[z7,z1,z2,z4,z67,z5,z6])],[(0,[z59,z7,z1,z2,z4,z92,z6]),(0,[z7,z1,z2,z206,z4,z5,z6])],[(0,[z7,z1,z2,z207,z4,z5,z6])],[(0,[z7,z2,z25,z21,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z208,z6]),(0,[z7,z2,z69,z4,z5,z50,z6]),(1,[z7,z209,z2,z4,z5,z6])],[(0,[z12,z0,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z210])],[(0,[z7,z1,z211,z2,z4,z5,z6])],[],[(0,[z212,z7,z1,z2,z4,z5,z6]),(0,[z7,z182,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z213]),(0,[z214,z7,z1,z2,z15,z5,z6])]],
   [[(0,[z215,z7,z1,z2,z4,z5,z6]),(0,[z105,z7,z2,z4,z5,z50,z6]),(0,[z35,z7,z216,z2,z4,z5,z6]),(0,[z7,z1,z2,z128,z69,z5,z6])],[(0,[z7,z1,z2,z217,z4,z5,z6]),(0,[z55,z7,z72,z2,z4,z5,z6]),(0,[z7,z72,z2,z2,z4,z5,z6]),(0,[z12,z7,z1,z2,z4,z5,z127])],[(0,[z218,z7,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z129,z4,z5,z6]),(0,[z7,z2,z21,z42,z4,z5,z6]),(0,[z7,z1,z2,z129,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z219])],[(0,[z7,z1,z119,z4,z5,z26,z6]),(0,[z220,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z221,z2,z4,z5,z6]),(0,[z140,z7,z1,z2,z4,z5,z6]),(0,[z33,z1,z2,z3,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z6,z188]),(0,[z7,z222,z1,z2,z4,z5,z6]),(0,[z80,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z99,z2,z4,z5,z6]),(0,[z7,z1,z223,z2,z4,z5,z6]),(0,[z39,z7,z2,z21,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z224,z6]),(0,[z7,z1,z36,z2,z4,z62,z6])],[(0,[z12,z7,z72,z2,z4,z5,z6]),(0,[z225,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z226,z4,z5,z6])],[(0,[z7,z1,z2,z4,z227,z5,z6])],[(0,[z104,z7,z2,z21,z4,z5,z6]),(0,[z7,z1,z2,z228,z4,z5,z6]),(1,[z229,z1,z2,z4,z5,z6]),(0,[z47,z7,z2,z21,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z230,z6]),(0,[z1,z2,z231,z25,z4,z5,z6]),(0,[z7,z1,z232,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z233])],[(0,[z7,z1,z2,z4,z5,z234,z6]),(0,[z235,z7,z72,z2,z4,z5,z6])],[(0,[z236,z1,z2,z4,z15,z5,z6])],[(0,[z39,z0,z1,z2,z4,z5,z6]),(0,[z218,z7,z2,z4,z5,z50,z6]),(0,[z7,z237,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z238,z5,z6])],[(0,[z7,z1,z239,z2,z4,z5,z6]),(1,[z7,z1,z56,z60,z5,z6])]],
   [[(0,[z104,z0,z1,z2,z4,z5,z6]),(0,[z47,z0,z1,z2,z4,z5,z6]),(0,[z7,z240,z1,z2,z4,z5,z6]),(0,[z7,z183,z119,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z241,z6])],[(0,[z7,z1,z2,z4,z5,z242,z6]),(0,[z7,z1,z243,z2,z4,z5,z6]),(0,[z7,z72,z186,z2,z4,z5,z6])],[(0,[z12,z54,z7,z2,z4,z5,z6]),(0,[z244,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z128,z16,z5,z6]),(0,[z32,z7,z2,z4,z5,z6,z127])],[(0,[z12,z91,z7,z2,z4,z5,z6])],[(0,[z7,z1,z245,z2,z4,z5,z6]),(0,[z7,z49,z1,z2,z4,z5,z188]),(0,[z246,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z247]),(0,[z7,z1,z2,z248,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z249,z6]),(0,[z7,z1,z2,z4,z5,z26,z6]),(0,[z7,z1,z2,z4,z5,z6,z250]),(0,[z251,z7,z1,z2,z4,z5,z6])],[(0,[z1,z36,z2,z25,z4,z5,z6])],[(0,[z252,z7,z1,z2,z4,z5,z6])],[(0,[z1,z2,z25,z4,z110,z5,z6]),(0,[z1,z2,z25,z4,z5,z111,z6]),(0,[z253,z0,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z254,z4,z5,z6]),(0,[z7,z1,z255,z2,z4,z5,z6])],[(0,[z39,z7,z72,z2,z4,z5,z6])],[(0,[z256,z7,z1,z2,z4,z5,z6])],[],[(0,[z7,z1,z2,z257,z4,z5,z6]),(0,[z104,z7,z72,z2,z4,z5,z6]),(0,[z0,z1,z2,z14,z4,z5,z6]),(0,[z47,z7,z72,z2,z4,z5,z6]),(0,[z7,z1,z2,z14,z4,z5,z6])],[(0,[z7,z1,z2,z258,z4,z5,z6]),(0,[z7,z259,z1,z2,z15,z5,z6]),(0,[z7,z260,z1,z2,z4,z5,z6])],[(0,[z1,z2,z2,z25,z4,z5,z6]),(0,[z7,z1,z2,z4,z261,z5,z6]),(0,[z262,z7,z1,z2,z4,z5,z6])],[(0,[z1,z2,z25,z128,z4,z5,z6]),(0,[z7,z1,z2,z4,z263,z5,z6]),(0,[z246,z7,z2,z4,z5,z50,z6])]],
   [[(0,[z35,z7,z2,z21,z4,z5,z6]),(0,[z264,z1,z2,z128,z4,z5,z6]),(0,[z265,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z266,z4,z5,z6])],[(0,[z0,z1,z2,z60,z4,z5,z6]),(0,[z7,z1,z2,z60,z4,z5,z6])],[(1,[z104,z1,z25,z4,z5,z6])],[(0,[z267,z7,z1,z2,z4,z5,z6]),(0,[z12,z7,z2,z4,z38,z5,z6]),(0,[z7,z1,z2,z4,z268,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z269])],[(0,[z55,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z270,z4,z5,z6]),(0,[z12,z7,z271,z2,z4,z5,z6]),(0,[z7,z1,z2,z272,z4,z5,z6])],[(0,[z204,z1,z2,z25,z4,z5,z6])],[(0,[z273,z1,z2,z25,z4,z5,z6]),(0,[z35,z0,z1,z2,z4,z5,z6]),(1,[z274,z1,z2,z4,z5,z6]),(1,[z114,z7,z1,z16,z5,z6]),(0,[z275,z7,z1,z2,z4,z5,z6]),(0,[z276,z7,z1,z2,z4,z5,z6])],[(0,[z7,z72,z2,z129,z4,z5,z6]),(0,[z114,z7,z93,z2,z4,z5,z6]),(0,[z7,z1,z56,z2,z60,z5,z6]),(0,[z7,z1,z2,z277,z4,z5,z6]),(0,[z204,z7,z1,z2,z71,z4,z5]),(0,[z7,z1,z278,z2,z4,z5,z6])],[(0,[z279,z7,z1,z2,z4,z5,z6]),(0,[z1,z2,z25,z4,z5,z6,z145])],[(1,[z1,z2,z25,z4,z5,z6]),(0,[z7,z1,z2,z280,z4,z5,z6]),(0,[z7,z281,z1,z2,z4,z5,z6]),(1,[z7,z1,z2,z5,z200,z6]),(0,[z7,z1,z2,z282,z4,z5,z6])],[(0,[z7,z1,z2,z4,z283,z5,z6]),(0,[z0,z1,z2,z42,z4,z5,z6]),(0,[z1,z76,z2,z284,z4,z5,z6]),(0,[z12,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z42,z4,z5,z6])],[(0,[z12,z7,z2,z4,z5,z92,z6]),(0,[z12,z7,z2,z4,z5,z6,z73]),(0,[z35,z285,z1,z2,z4,z5,z6]),(1,[z1,z2,z173,z4,z5,z6])],[(0,[z12,z7,z2,z4,z5,z28,z6]),(0,[z7,z2,z4,z5,z62,z50,z6]),(0,[z286,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z36,z4,z52,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z287])],[(0,[z7,z1,z2,z4,z288,z5,z6])],[(0,[z289,z7,z1,z2,z4,z5,z6]),(0,[z7,z290,z1,z2,z4,z5,z6]),(1,[z291,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z197,z5,z6])]],
   [[(0,[z55,z7,z2,z4,z5,z50,z6])],[(0,[z1,z2,z25,z4,z5,z6,z43]),(0,[z292,z7,z1,z2,z4,z5,z6]),(0,[z293,z7,z1,z2,z4,z5,z6]),(0,[z35,z7,z1,z2,z4,z62,z6]),(0,[z294,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z295,z5,z6]),(0,[z296,z7,z2,z21,z4,z5,z6])],[(0,[z7,z2,z21,z254,z4,z5,z6]),(0,[z7,z72,z2,z4,z5,z6,z297]),(0,[z35,z7,z72,z2,z4,z5,z6])],[(0,[z54,z7,z2,z21,z4,z5,z6]),(0,[z7,z2,z4,z5,z50,z6,z298]),(0,[z35,z180,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z299,z6]),(0,[z7,z300,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z301,z4,z5,z6])],[(1,[z7,z2,z107,z4,z5,z6])],[(0,[z104,z7,z152,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z108,z6]),(0,[z7,z302,z1,z2,z4,z5,z6]),(0,[z214,z7,z2,z4,z15,z5,z6]),(0,[z12,z7,z2,z4,z5,z50,z6])],[(0,[z303,z7,z1,z2,z4,z5,z6]),(0,[z1,z2,z25,z304,z4,z5,z6]),(0,[z7,z2,z21,z14,z4,z5,z6])],[(0,[z0,z1,z2,z71,z4,z5,z6]),(0,[z7,z305,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z71,z4,z5,z6])],[(0,[z259,z1,z2,z25,z4,z5,z6])],[(0,[z306,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z62,z6,z127])],[(0,[z54,z0,z1,z2,z4,z5,z6]),(0,[z307,z7,z1,z2,z4,z5,z6]),(0,[z33,z7,z2,z21,z4,z5,z6]),(0,[z7,z1,z2,z308,z4,z6,z127])],[(0,[z34,z7,z1,z2,z4,z5,z6]),(0,[z7,z2,z25,z4,z5,z50,z6]),(0,[z0,z1,z2,z4,z5,z62,z6]),(0,[z7,z2,z21,z60,z4,z5,z6]),(1,[z120,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z309,z4,z5,z6]),(0,[z7,z2,z4,z5,z28,z50,z6])],[(0,[z39,z7,z1,z2,z4,z5,z6]),(1,[z7,z205,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z310,z6,z127])],[(0,[z7,z1,z2,z311,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z29,z73]),(0,[z7,z1,z2,z4,z312,z5,z6]),(0,[z7,z1,z313,z2,z4,z5,z6])],[(0,[z314,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z315,z38,z5,z6]),(1,[z316,z7,z2,z4,z5,z6])]],
   [[(0,[z47,z7,z1,z2,z4,z5,z6]),(0,[z91,z13,z1,z2,z4,z5,z6]),(0,[z7,z317,z100,z2,z4,z5,z6]),(0,[z318,z12,z7,z2,z4,z5,z6]),(0,[z7,z1,z2,z71,z42,z4,z5])],[(0,[z1,z2,z319,z25,z4,z5,z6]),(0,[z7,z72,z2,z14,z4,z5,z6]),(0,[z7,z1,z320,z2,z4,z5,z6]),(0,[z7,z1,z2,z321,z4,z5,z6])],[(0,[z7,z1,z2,z322,z4,z5,z6]),(0,[z7,z1,z2,z128,z129,z4,z6])],[(0,[z1,z76,z2,z25,z4,z5,z6])],[(0,[z59,z1,z2,z4,z38,z5,z6]),(0,[z7,z1,z2,z128,z60,z5,z6]),(0,[z323,z7,z1,z2,z4,z5,z6])],[(0,[z1,z2,z25,z21,z4,z5,z6]),(0,[z7,z1,z2,z324,z4,z5,z6]),(0,[z296,z7,z72,z2,z4,z5,z6])],[(0,[z7,z1,z325,z2,z4,z5,z6]),(0,[z7,z72,z2,z60,z4,z5,z6]),(0,[z7,z1,z2,z326,z4,z5,z6]),(0,[z7,z2,z4,z5,z50,z6,z127])],[(0,[z54,z7,z72,z2,z4,z5,z6])],[(0,[z39,z7,z2,z4,z5,z50,z6]),(0,[z327,z7,z1,z2,z4,z5,z6]),(0,[z7,z328,z1,z2,z4,z5,z6])],[(1,[z20,z1,z2,z110,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z329]),(0,[z7,z330,z36,z2,z4,z5,z6])],[(0,[z12,z7,z100,z2,z4,z5,z6]),(1,[z331,z1,z2,z4,z5,z6]),(0,[z7,z1,z332,z2,z4,z5,z6])],[(0,[z333,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z334,z4,z5,z6]),(0,[z47,z7,z2,z4,z5,z50,z6]),(0,[z114,z7,z1,z4,z16,z5,z6])],[(0,[z335,z7,z1,z2,z4,z5,z6]),(0,[z12,z51,z7,z2,z4,z5,z6]),(0,[z155,z1,z2,z129,z4,z5,z6])],[(0,[z12,z7,z2,z4,z336,z5,z6]),(0,[z7,z1,z2,z4,z5,z337,z6])],[(0,[z33,z7,z72,z2,z4,z5,z6]),(0,[z7,z1,z2,z84,z4,z5,z6]),(0,[z7,z1,z2,z338,z4,z5,z6]),(0,[z339,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z310,z6])],[(0,[z7,z1,z2,z4,z340,z5,z6]),(1,[z72,z2,z25,z4,z5,z6]),(0,[z7,z119,z2,z21,z4,z5,z6]),(0,[z7,z1,z341,z2,z4,z5,z6])]],
   [[(0,[z7,z7,z1,z2,z4,z5,z6]),(0,[z0,z7,z1,z2,z4,z5,z6]),(0,[z7,z72,z2,z42,z4,z5,z6]),(0,[z7,z72,z49,z2,z4,z5,z6]),(1,[z342,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z297])],[(0,[z343,z7,z2,z21,z4,z5,z6])],[(0,[z7,z2,z21,z71,z4,z5,z6]),(0,[z7,z2,z4,z15,z5,z50,z6]),(0,[z7,z1,z2,z4,z344,z5,z6])],[(0,[z345,z7,z2,z21,z4,z5,z6])],[(1,[z1,z2,z284,z4,z5,z6])],[(0,[z1,z2,z25,z4,z5,z6,z188]),(0,[z20,z1,z2,z4,z110,z5,z6]),(0,[z20,z1,z2,z4,z5,z111,z6]),(0,[z7,z1,z2,z4,z346,z5,z6]),(1,[z347,z1,z2,z4,z5,z6]),(0,[z122,z1,z2,z4,z5,z6,z127])],[(0,[z7,z2,z21,z4,z5,z62,z6]),(1,[z7,z348,z2,z4,z5,z6])],[(0,[z7,z349,z1,z2,z4,z109,z6]),(0,[z350,z7,z1,z2,z4,z5,z6]),(0,[z204,z7,z1,z2,z4,z5,z43]),(0,[z7,z351,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z352])],[(0,[z7,z1,z2,z4,z353,z5,z6]),(0,[z7,z1,z354,z2,z4,z5,z6]),(0,[z7,z1,z355,z2,z4,z5,z6]),(0,[z12,z7,z349,z2,z4,z5,z6]),(1,[z12,z7,z2,z4,z5,z127])],[(0,[z0,z7,z2,z4,z5,z50,z6])],[(0,[z39,z7,z1,z2,z4,z356,z6])],[(0,[z12,z7,z2,z25,z4,z5,z6]),(0,[z33,z7,z1,z2,z110,z5,z6]),(0,[z7,z1,z2,z4,z5,z357,z6]),(0,[z7,z72,z2,z4,z5,z358,z6]),(0,[z7,z72,z2,z71,z4,z5,z6]),(0,[z7,z359,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z360,z5,z6]),(0,[z55,z7,z1,z2,z4,z5,z111])],[(0,[z361,z7,z1,z2,z4,z5,z6]),(1,[z7,z1,z2,z362,z4,z5])]],
   [[(0,[z7,z1,z2,z4,z5,z363,z6]),(0,[z364,z7,z1,z2,z4,z5,z6]),(0,[z214,z7,z259,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z365,z6]),(0,[z7,z1,z2,z4,z5,z366,z6])],[(0,[z91,z7,z1,z2,z4,z38,z6]),(0,[z7,z72,z2,z4,z5,z62,z6]),(0,[z367,z7,z1,z2,z4,z5,z6])],[],[(0,[z0,z1,z2,z4,z16,z5,z6]),(1,[z7,z1,z2,z4,z5,z368])],[(0,[z37,z1,z2,z3,z4,z5,z6]),(0,[z7,z317,z1,z2,z4,z5,z6]),(1,[z199,z7,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z369,z5,z6]),(0,[z7,z1,z370,z2,z4,z5,z6]),(0,[z51,z7,z371,z2,z4,z5,z6])],[(0,[z372,z7,z1,z2,z4,z5,z6]),(1,[z264,z1,z2,z4,z5,z6])],[(0,[z91,z59,z1,z2,z4,z5,z6]),(0,[z373,z7,z1,z2,z4,z5,z6]),(1,[z7,z374,z2,z4,z5,z6]),(1,[z204,z7,z1,z2,z71,z5])],[(0,[z7,z99,z2,z4,z5,z50,z6]),(0,[z375,z7,z1,z2,z4,z5,z6]),(0,[z1,z56,z2,z25,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z376,z6])],[(0,[z7,z1,z2,z4,z5,z6,z377]),(1,[z1,z2,z11,z4,z5,z6]),(1,[z80,z7,z2,z4,z5,z6])],[(0,[z33,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z4,z5,z378,z6]),(0,[z7,z1,z2,z4,z379,z5,z6]),(0,[z51,z7,z1,z2,z4,z67,z6])],[(0,[z54,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z380,z5,z6]),(0,[z7,z1,z381,z2,z4,z5,z6]),(0,[z382,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z383])],[(0,[z7,z384,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z385,z6]),(0,[z7,z1,z2,z4,z52,z6,z127]),(1,[z51,z7,z1,z2,z308,z4])],[(0,[z7,z1,z2,z386,z4,z5,z6])],[(1,[z0,z1,z25,z4,z5,z6]),(0,[z7,z2,z362,z21,z4,z5,z6]),(1,[z7,z1,z2,z4,z5,z387])],[(0,[z1,z2,z25,z4,z388,z5,z6]),(0,[z0,z1,z36,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z110,z5,z6]),(0,[z1,z2,z3,z4,z5,z111,z6]),(0,[z114,z331,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z389,z4,z5,z6]),(0,[z7,z1,z36,z2,z4,z5,z6]),(0,[z390,z7,z1,z2,z4,z5,z6])]],
   [[(0,[z7,z2,z308,z4,z5,z50,z6]),(0,[z7,z2,z4,z5,z50,z6,z6]),(0,[z7,z1,z2,z4,z5,z391,z6])],[(0,[z7,z1,z2,z4,z5,z392,z6]),(0,[z7,z1,z2,z393,z4,z5,z6])],[(0,[z0,z1,z2,z21,z4,z5,z6]),(1,[z7,z2,z324,z4,z5,z6]),(0,[z235,z7,z1,z2,z4,z5,z6]),(0,[z7,z36,z2,z107,z4,z5,z6])],[(0,[z0,z1,z56,z2,z4,z5,z6]),(0,[z7,z1,z56,z2,z4,z5,z6])],[(0,[z1,z2,z25,z4,z38,z5,z6]),(1,[z214,z7,z2,z15,z5,z6]),(0,[z7,z1,z2,z4,z394,z5,z6])],[(0,[z7,z49,z2,z21,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z395])],[(0,[z54,z7,z2,z4,z5,z50,z6]),(0,[z7,z1,z396,z2,z4,z5,z6]),(0,[z382,z7,z2,z4,z5,z50,z6])],[(0,[z7,z1,z2,z397,z4,z5,z6]),(0,[z7,z1,z2,z398,z4,z5,z6]),(0,[z7,z2,z4,z52,z5,z50,z6]),(0,[z7,z1,z2,z399,z4,z5,z6]),(1,[z7,z332,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z400]),(0,[z401,z12,z7,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z402])],[(0,[z403,z7,z1,z2,z4,z5,z6]),(0,[z404,z7,z1,z2,z4,z5,z6]),(0,[z405,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z406,z2,z4,z5,z6]),(0,[z35,z7,z1,z2,z4,z5,z299])],[(0,[z7,z1,z2,z4,z5,z358,z6]),(0,[z7,z1,z2,z4,z5,z407,z6]),(0,[z7,z259,z2,z14,z4,z5,z6]),(0,[z7,z1,z2,z4,z408,z5,z6])],[(0,[z409,z7,z1,z2,z4,z5,z6]),(0,[z296,z0,z1,z2,z4,z5,z6]),(0,[z54,z91,z1,z2,z4,z5,z6])],[(0,[z1,z2,z25,z4,z5,z92,z6]),(0,[z1,z2,z25,z4,z5,z6,z73]),(0,[z0,z410,z1,z2,z4,z5,z6]),(0,[z35,z7,z1,z2,z4,z5,z411]),(0,[z51,z7,z1,z2,z4,z62,z6])],[(0,[z1,z2,z25,z4,z5,z28,z6]),(0,[z59,z1,z2,z25,z4,z5,z6]),(0,[z7,z1,z2,z315,z4,z5,z6]),(0,[z7,z2,z21,z4,z16,z5,z6]),(0,[z7,z412,z72,z2,z4,z5,z6])],[(0,[z7,z1,z413,z2,z4,z5,z6]),(0,[z51,z7,z72,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z62,z6])]],
   [[(0,[z7,z1,z2,z414,z4,z5,z6]),(0,[z33,z7,z1,z2,z5,z28,z6])],[(0,[z214,z1,z2,z25,z4,z5,z6])],[(0,[z7,z2,z4,z415,z5,z50,z6]),(1,[z1,z2,z4,z5,z6,z416])],[(0,[z12,z89,z7,z2,z4,z5,z6]),(0,[z104,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z417,z5,z6])],[(1,[z12,z7,z2,z4,z5,z6]),(0,[z204,z7,z418,z2,z4,z5,z6])],[(0,[z33,z0,z1,z2,z4,z5,z6]),(0,[z419,z7,z1,z2,z4,z5,z6])],[(0,[z7,z72,z1,z76,z4,z5,z6]),(0,[z214,z7,z1,z2,z14,z5,z6]),(0,[z420,z12,z7,z2,z4,z5,z6]),(0,[z421,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z422,z4,z5,z6]),(0,[z7,z1,z2,z4,z67,z6,z127])],[(0,[z1,z2,z25,z4,z5,z50,z6]),(0,[z7,z100,z2,z324,z4,z5,z6]),(0,[z409,z7,z2,z4,z5,z50,z6])],[(0,[z423,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z110,z5,z6]),(0,[z0,z1,z2,z4,z5,z111,z6]),(1,[z7,z1,z2,z53,z4,z6]),(0,[z7,z1,z2,z4,z5,z111,z6]),(0,[z7,z72,z2,z4,z16,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z424]),(0,[z343,z7,z1,z2,z4,z5,z6])],[(0,[z37,z7,z13,z2,z4,z5,z6]),(0,[z7,z1,z2,z425,z4,z5,z6]),(0,[z7,z1,z2,z4,z426,z5,z6])],[(0,[z83,z1,z2,z25,z4,z5,z6]),(0,[z253,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z427,z5,z6])],[(0,[z1,z2,z4,z38,z5,z111,z6]),(0,[z7,z1,z2,z428,z4,z5,z6]),(1,[z35,z7,z1,z4,z62,z6]),(0,[z7,z1,z2,z4,z429,z5,z6])],[(0,[z89,z1,z2,z25,z4,z5,z6]),(0,[z7,z430,z1,z2,z4,z5,z6]),(0,[z7,z2,z21,z21,z4,z5,z6]),(0,[z7,z2,z60,z4,z5,z50,z6]),(0,[z204,z7,z1,z2,z71,z5,z6])],[(0,[z104,z7,z2,z4,z5,z50,z6])],[(0,[z0,z1,z2,z128,z4,z5,z6]),(0,[z7,z72,z2,z4,z379,z5,z6]),(0,[z1,z119,z2,z70,z4,z5,z6])]],
   [[(0,[z7,z1,z2,z431,z4,z5,z6]),(1,[z7,z1,z2,z69,z28,z6])],[(0,[z20,z7,z1,z2,z128,z5,z6])],[(0,[z114,z1,z2,z25,z4,z5,z6])],[(0,[z1,z2,z25,z432,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z50,z6]),(0,[z433,z7,z1,z2,z4,z5,z6]),(0,[z35,z7,z434,z2,z4,z5,z6])],[(0,[z7,z72,z36,z2,z4,z5,z6]),(0,[z7,z1,z2,z435,z4,z5,z6]),(1,[z7,z1,z2,z137,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z436]),(0,[z7,z1,z2,z437,z4,z5,z6]),(0,[z7,z1,z216,z2,z4,z5,z6])],[(0,[z89,z7,z99,z2,z4,z5,z6]),(0,[z1,z99,z2,z25,z4,z5,z6]),(1,[z55,z1,z2,z4,z5,z111])],[(0,[z7,z72,z2,z21,z4,z5,z6])],[(0,[z7,z1,z2,z438,z4,z5,z6]),(0,[z7,z72,z56,z2,z4,z5,z6]),(0,[z7,z1,z2,z439,z4,z5,z6]),(0,[z204,z7,z1,z2,z16,z5,z6]),(0,[z7,z1,z2,z440,z4,z5,z6]),(0,[z441,z7,z1,z2,z4,z5,z6])],[(0,[z89,z13,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z145]),(0,[z7,z1,z2,z4,z5,z442,z6]),(0,[z155,z7,z1,z2,z4,z5,z6])],[(0,[z37,z7,z2,z21,z4,z5,z6]),(0,[z121,z1,z2,z25,z4,z5,z6]),(0,[z35,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z443,z4,z5,z6]),(1,[z7,z1,z2,z90,z5,z6])],[],[(0,[z7,z1,z2,z16,z5,z6,z43]),(0,[z7,z1,z2,z4,z5,z444,z6])],[(0,[z13,z1,z2,z4,z38,z5,z6]),(0,[z7,z1,z2,z4,z5,z445,z6]),(0,[z1,z2,z25,z4,z336,z5,z6]),(0,[z7,z1,z2,z4,z137,z5,z6]),(0,[z7,z1,z418,z2,z4,z5,z6])],[(0,[z446,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z447,z6]),(0,[z7,z1,z2,z4,z5,z447,z6]),(0,[z7,z1,z2,z448,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z449]),(0,[z7,z1,z2,z71,z4,z5,z26]),(0,[z339,z1,z2,z4,z5,z6,z43])]],
   [[(0,[z7,z1,z2,z4,z450,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z451]),(0,[z55,z1,z2,z4,z5,z111,z6]),(0,[z7,z2,z4,z5,z230,z50,z6])],[(0,[z37,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z43]),(0,[z7,z1,z452,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z43])],[(0,[z7,z412,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z453,z4,z5,z6]),(0,[z105,z229,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z454,z6])],[(0,[z7,z2,z21,z4,z110,z5,z6]),(0,[z7,z1,z2,z4,z5,z455,z6]),(0,[z7,z2,z21,z4,z5,z111,z6]),(0,[z7,z456,z1,z2,z4,z5,z6])],[(0,[z54,z7,z1,z2,z4,z5,z111]),(0,[z7,z259,z1,z2,z14,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z457]),(0,[z39,z7,z1,z2,z4,z5,z26]),(0,[z7,z1,z2,z308,z4,z5,z145])],[(0,[z7,z2,z21,z4,z426,z5,z6]),(0,[z35,z7,z2,z4,z5,z50,z6]),(0,[z7,z1,z2,z4,z90,z5,z6])],[(0,[z7,z1,z2,z4,z16,z5,z6])],[(0,[z7,z1,z2,z458,z4,z5,z6]),(0,[z7,z1,z2,z304,z4,z5,z6]),(0,[z7,z1,z2,z16,z5,z28,z6])],[(1,[z7,z2,z4,z5,z358,z6]),(0,[z1,z2,z4,z161,z15,z5,z6]),(0,[z12,z7,z2,z308,z4,z5,z6]),(0,[z12,z7,z1,z119,z2,z4,z5]),(0,[z7,z1,z2,z4,z5,z6,z368])],[(0,[z7,z1,z2,z459,z4,z5,z6]),(0,[z91,z7,z2,z21,z4,z5,z6]),(0,[z7,z1,z2,z4,z336,z5,z460])],[(0,[z7,z1,z2,z4,z461,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z73]),(0,[z7,z2,z21,z128,z4,z5,z6]),(0,[z7,z72,z72,z2,z4,z5,z6]),(0,[z236,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z70,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z462])],[(0,[z0,z1,z2,z4,z5,z28,z6]),(0,[z7,z1,z463,z2,z4,z5,z6]),(0,[z7,z1,z2,z38,z5,z200,z6]),(0,[z7,z1,z2,z464,z4,z5,z6]),(0,[z7,z465,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z466]),(0,[z0,z49,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z467,z4,z5,z6]),(0,[z296,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z129,z69,z4,z6])],[(0,[z37,z7,z72,z2,z4,z5,z6]),(0,[z1,z2,z25,z4,z5,z6,z468]),(0,[z7,z72,z2,z4,z110,z5,z6]),(0,[z7,z1,z2,z4,z469,z5,z6]),(0,[z7,z72,z2,z4,z5,z111,z6]),(0,[z7,z1,z371,z2,z4,z5,z6])],[(0,[z20,z37,z1,z2,z4,z5,z6]),(0,[z470,z7,z1,z2,z4,z5,z6]),(0,[z1,z2,z25,z25,z4,z5,z6])],[(0,[z51,z7,z2,z21,z4,z5,z6])]],
   [[(0,[z91,z0,z1,z2,z4,z5,z6]),(0,[z7,z2,z4,z38,z5,z50,z6]),(1,[z7,z1,z119,z4,z5,z26]),(0,[z471,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z41,z4,z5,z6]),(0,[z12,z7,z2,z69,z4,z5,z6]),(0,[z7,z1,z2,z57,z4,z5,z6])],[(1,[z0,z2,z21,z4,z5,z6])],[(0,[z472,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z387])],[(0,[z7,z2,z21,z4,z5,z6,z145]),(0,[z7,z72,z2,z128,z4,z5,z6]),(0,[z12,z7,z76,z2,z4,z5,z6]),(0,[z473,z7,z1,z2,z4,z5,z6])],[(0,[z474,z7,z1,z2,z4,z5,z6]),(0,[z33,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z21,z4,z5,z6]),(0,[z12,z7,z475,z2,z4,z5,z6])],[(0,[z51,z0,z1,z2,z4,z5,z6]),(0,[z7,z185,z1,z2,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z6,z127]),(0,[z7,z1,z2,z4,z5,z6,z476]),(1,[z7,z1,z2,z4,z67,z127])],[(0,[z7,z477,z1,z2,z4,z5,z6]),(0,[z296,z7,z2,z4,z5,z50,z6])],[(1,[z54,z1,z2,z4,z5,z73]),(0,[z114,z342,z1,z2,z4,z5,z6]),(0,[z7,z348,z1,z2,z4,z5,z6]),(0,[z7,z1,z56,z60,z4,z5,z6])],[(0,[z7,z478,z1,z2,z4,z5,z6]),(0,[z12,z367,z7,z2,z4,z5,z6])],[(0,[z479,z0,z1,z2,z4,z5,z6]),(0,[z480,z7,z1,z2,z4,z5,z6]),(0,[z1,z36,z2,z97,z4,z5,z6])],[(0,[z20,z1,z2,z4,z5,z92,z6]),(0,[z7,z1,z2,z4,z5,z208,z6])],[(0,[z91,z7,z72,z2,z4,z5,z6]),(0,[z7,z2,z21,z4,z5,z6,z43]),(0,[z51,z7,z1,z2,z4,z5,z127])],[(0,[z7,z1,z2,z481,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z43,z145]),(0,[z7,z1,z2,z482,z4,z5,z6])],[(0,[z7,z1,z2,z483,z4,z5,z6]),(0,[z175,z7,z1,z2,z4,z5,z6]),(0,[z7,z72,z2,z4,z5,z6,z145]),(0,[z7,z1,z2,z484,z4,z5,z6]),(1,[z7,z2,z4,z5,z310,z6])],[(0,[z114,z7,z348,z2,z4,z5,z6]),(0,[z7,z1,z485,z2,z4,z5,z6]),(0,[z39,z7,z1,z2,z46,z5,z6])]],
   [[(0,[z7,z410,z1,z2,z4,z5,z6]),(0,[z33,z7,z2,z4,z5,z50,z6]),(0,[z105,z274,z1,z2,z4,z5,z6]),(0,[z486,z7,z2,z21,z4,z5,z6])],[(0,[z7,z1,z487,z2,z4,z5,z6]),(0,[z7,z1,z488,z2,z4,z5,z6])],[(0,[z7,z1,z2,z489,z4,z5,z6]),(0,[z114,z7,z1,z56,z4,z5,z6]),(0,[z7,z1,z2,z4,z490,z5,z6]),(1,[z7,z216,z2,z4,z5,z6])],[(0,[z105,z1,z2,z25,z4,z5,z6]),(0,[z7,z491,z1,z2,z4,z5,z6]),(0,[z492,z7,z1,z2,z4,z5,z6])],[],[(0,[z493,z7,z1,z2,z4,z5,z6]),(1,[z0,z72,z2,z4,z5,z6]),(0,[z7,z2,z21,z4,z5,z6,z73]),(0,[z7,z1,z2,z4,z494,z5,z6]),(1,[z7,z2,z439,z4,z5,z6]),(0,[z12,z7,z2,z4,z113,z5,z6]),(0,[z7,z49,z1,z2,z4,z5,z127])],[(0,[z0,z1,z2,z4,z5,z6,z188]),(0,[z7,z1,z2,z4,z5,z495,z6]),(0,[z7,z2,z21,z4,z5,z28,z6]),(0,[z7,z72,z2,z4,z5,z6,z43]),(0,[z7,z1,z2,z496,z4,z5,z6]),(0,[z7,z330,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z497,z4,z5,z6])],[(0,[z486,z0,z1,z2,z4,z5,z6]),(0,[z7,z2,z21,z4,z5,z178,z6]),(0,[z35,z7,z1,z2,z277,z5,z6]),(1,[z182,z1,z2,z4,z5,z6])],[(0,[z0,z1,z100,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z498,z5,z6]),(0,[z7,z1,z2,z4,z498,z5,z6]),(0,[z7,z2,z4,z5,z178,z50,z6]),(1,[z7,z1,z2,z42,z5,z43])],[(0,[z37,z1,z99,z2,z4,z5,z6]),(0,[z204,z7,z1,z2,z60,z5,z6]),(0,[z7,z1,z2,z129,z4,z52,z6])],[(0,[z7,z1,z2,z4,z110,z5,z6]),(0,[z114,z7,z1,z2,z4,z5,z368]),(0,[z7,z1,z2,z499,z4,z5,z6]),(1,[z7,z418,z2,z4,z5,z6])],[(0,[z7,z374,z1,z2,z4,z5,z6])],[(0,[z1,z2,z500,z25,z4,z5,z6]),(0,[z7,z501,z72,z2,z4,z5,z6])],[(0,[z502,z7,z2,z4,z5,z6,z73]),(0,[z105,z7,z1,z21,z4,z5,z6]),(0,[z345,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z503]),(0,[z7,z1,z2,z4,z5,z6,z504]),(0,[z505,z7,z1,z2,z4,z5,z6]),(1,[z1,z2,z97,z4,z5,z6])],[(0,[z7,z1,z506,z2,z4,z5,z6]),(0,[z7,z72,z2,z4,z5,z6,z73]),(0,[z7,z1,z2,z4,z5,z6,z507])]],
   [[(0,[z7,z1,z2,z508,z4,z5,z6]),(0,[z7,z1,z509,z2,z4,z5,z6]),(0,[z7,z72,z2,z4,z5,z28,z6]),(0,[z7,z2,z71,z4,z5,z50,z6]),(0,[z7,z1,z2,z510,z4,z5,z6]),(0,[z39,z7,z1,z2,z4,z197,z6]),(0,[z7,z1,z511,z2,z4,z5,z6])],[],[(0,[z7,z1,z2,z128,z4,z5,z6])],[(0,[z512,z7,z72,z2,z4,z5,z6]),(0,[z7,z2,z129,z4,z5,z50,z6]),(0,[z285,z7,z1,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z92,z6]),(0,[z7,z119,z2,z4,z5,z50,z6]),(0,[z51,z7,z237,z2,z4,z5,z6])],[(0,[z12,z37,z7,z2,z4,z5,z6]),(0,[z229,z7,z1,z2,z4,z5,z6]),(0,[z318,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z513])],[(0,[z91,z7,z1,z2,z129,z4,z6]),(0,[z7,z1,z2,z514,z4,z5,z6]),(0,[z199,z7,z2,z4,z5,z26,z6])],[(0,[z12,z7,z1,z2,z308,z4,z5])],[(0,[z13,z1,z2,z25,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z515]),(0,[z7,z1,z2,z128,z4,z28,z6])],[(0,[z12,z7,z2,z4,z52,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z18])],[(0,[z516,z7,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z154,z109,z6]),(0,[z347,z1,z119,z2,z4,z5,z6]),(1,[z7,z371,z2,z4,z5,z6])],[(0,[z7,z2,z4,z110,z5,z50,z6]),(0,[z296,z7,z349,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z517,z6])],[(0,[z7,z1,z2,z4,z5,z6,z145])],[(1,[z33,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z518,z4,z5,z6])],[(0,[z204,z7,z2,z21,z4,z5,z6]),(1,[z7,z2,z57,z4,z5,z6])],[(1,[z12,z2,z25,z4,z5,z6]),(0,[z7,z1,z2,z4,z388,z5,z6]),(0,[z12,z7,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z53,z3,z4,z6])]],
   [[(0,[z7,z1,z2,z4,z5,z519,z6]),(0,[z12,z7,z2,z4,z5,z6,z6])],[(0,[z412,z1,z2,z25,z4,z5,z6]),(0,[z1,z2,z453,z25,z4,z5,z6]),(0,[z7,z2,z21,z4,z5,z6,z188]),(0,[z7,z1,z2,z4,z5,z6,z156])],[(1,[z7,z2,z21,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z64])],[(0,[z0,z1,z2,z4,z38,z5,z6]),(0,[z7,z1,z2,z4,z38,z5,z6]),(0,[z7,z2,z4,z5,z50,z26,z6])],[(0,[z204,z0,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z520,z6]),(0,[z521,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z522,z6]),(0,[z7,z2,z14,z4,z5,z50,z6]),(0,[z51,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z523,z4,z5,z6])],[],[(0,[z7,z1,z2,z4,z5,z5,z6]),(1,[z1,z2,z4,z5,z154,z6]),(1,[z7,z1,z2,z524,z4,z5])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z525,z0,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z526,z6])],[(0,[z479,z7,z1,z2,z4,z5,z6]),(0,[z7,z527,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z528,z6]),(0,[z7,z72,z2,z4,z5,z6,z188])],[(0,[z20,z1,z2,z25,z4,z5,z6]),(0,[z7,z529,z72,z2,z4,z5,z6]),(1,[z1,z2,z4,z161,z5,z6]),(0,[z114,z12,z7,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z416,z43])],[(0,[z0,z1,z2,z4,z5,z92,z6]),(0,[z7,z72,z100,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z73]),(0,[z7,z1,z2,z179,z4,z5,z6]),(1,[z7,z1,z36,z4,z52,z6]),(0,[z7,z1,z2,z4,z5,z530,z6])],[(0,[z59,z7,z1,z2,z4,z38,z6]),(1,[z285,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z28,z6])],[(0,[z91,z33,z1,z2,z4,z5,z6]),(0,[z7,z1,z171,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z178,z6]),(0,[z7,z49,z1,z2,z4,z5,z6])]],
   [[(0,[z531,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z532,z6])],[(0,[z7,z1,z533,z2,z4,z5,z6]),(0,[z1,z2,z4,z38,z5,z92,z6]),(0,[z204,z7,z72,z2,z4,z5,z6]),(0,[z12,z7,z2,z4,z15,z5,z6]),(0,[z7,z1,z2,z4,z534,z5,z6]),(0,[z51,z7,z2,z4,z5,z50,z6])],[(0,[z89,z7,z13,z2,z4,z5,z6]),(0,[z535,z7,z1,z2,z4,z5,z6]),(0,[z7,z536,z1,z2,z4,z5,z6]),(0,[z7,z537,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z538,z4,z5,z6]),(0,[z7,z1,z2,z539,z4,z5,z6])],[(0,[z7,z13,z2,z21,z4,z5,z6]),(0,[z296,z7,z1,z2,z4,z336,z6])],[(1,[z0,z2,z4,z5,z50,z6]),(0,[z7,z487,z2,z4,z5,z50,z6])],[(1,[z7,z72,z2,z4,z5,z6])],[(1,[z180,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z50,z6]),(0,[z7,z100,z2,z21,z4,z5,z6]),(0,[z12,z214,z7,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z540,z5,z6]),(1,[z7,z1,z2,z4,z5,z460]),(0,[z7,z1,z2,z524,z4,z5,z6])],[(0,[z20,z13,z1,z2,z4,z5,z6])],[(0,[z1,z2,z25,z308,z4,z5,z6]),(0,[z291,z1,z2,z4,z5,z109,z6])],[(0,[z7,z49,z2,z4,z5,z50,z6]),(0,[z35,z7,z1,z4,z5,z62,z6]),(1,[z7,z1,z2,z128,z129,z6]),(0,[z7,z1,z2,z4,z541,z5,z6])],[(0,[z7,z1,z2,z542,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z543,z6])],[(0,[z7,z1,z2,z544,z4,z5,z6]),(1,[z7,z330,z2,z4,z5,z6])],[(1,[z502,z7,z2,z4,z5,z6]),(0,[z7,z2,z4,z336,z5,z50,z6])],[(0,[z545,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z546,z4,z5,z6]),(0,[z7,z2,z21,z4,z38,z5,z6]),(0,[z7,z349,z2,z21,z4,z5,z6])]],
   [[(0,[z59,z1,z2,z3,z4,z5,z6]),(0,[z7,z2,z21,z4,z5,z547,z6]),(0,[z342,z7,z1,z2,z4,z5,z6]),(1,[z39,z7,z1,z4,z5,z145])],[(0,[z7,z1,z2,z4,z548,z5,z6]),(0,[z549,z12,z7,z2,z4,z5,z6]),(1,[z12,z7,z119,z2,z4,z5])],[(0,[z1,z2,z25,z69,z4,z5,z6])],[(0,[z7,z1,z2,z432,z4,z5,z6]),(0,[z7,z1,z2,z4,z550,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z551])],[(0,[z552,z0,z1,z2,z4,z5,z6]),(0,[z553,z7,z1,z2,z4,z5,z6]),(0,[z114,z7,z1,z2,z16,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z554]),(0,[z555,z7,z1,z2,z4,z5,z6])],[(1,[z37,z99,z2,z4,z5,z6]),(0,[z556,z7,z1,z2,z4,z5,z6]),(0,[z7,z13,z72,z2,z4,z5,z6]),(0,[z557,z7,z1,z2,z4,z5,z6]),(1,[z2,z25,z21,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z109,z6]),(0,[z7,z1,z119,z2,z4,z5,z145])],[(0,[z104,z7,z66,z2,z4,z5,z6]),(0,[z1,z2,z25,z4,z5,z6,z127]),(0,[z7,z1,z4,z52,z5,z62,z6]),(0,[z7,z1,z2,z4,z5,z356,z6])],[(0,[z7,z1,z2,z4,z5,z558,z6]),(0,[z7,z2,z21,z4,z5,z92,z6]),(0,[z54,z1,z2,z4,z5,z6,z73])],[(0,[z7,z1,z2,z559,z4,z5,z6]),(0,[z7,z72,z2,z4,z38,z5,z6]),(0,[z7,z1,z2,z362,z21,z4,z5]),(0,[z7,z2,z4,z5,z109,z50,z6]),(0,[z7,z1,z2,z4,z5,z6,z188]),(0,[z7,z1,z2,z560,z4,z5,z6])],[(0,[z7,z561,z1,z2,z4,z5,z6]),(0,[z12,z7,z119,z2,z4,z5,z6]),(0,[z7,z1,z2,z128,z129,z5,z6])],[(0,[z7,z1,z100,z2,z4,z5,z6]),(0,[z1,z2,z25,z4,z85,z5,z6]),(0,[z148,z7,z1,z2,z4,z5,z6]),(0,[z562,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z563,z4,z5,z6])],[(0,[z12,z296,z7,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z564,z6]),(0,[z7,z1,z2,z308,z4,z67,z5])],[(0,[z7,z565,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z336,z5,z6]),(0,[z7,z1,z2,z4,z336,z5,z6]),(1,[z7,z2,z4,z5,z6,z156]),(0,[z566,z7,z1,z2,z4,z5,z6])],[(0,[z567,z7,z1,z2,z4,z5,z6]),(1,[z7,z152,z2,z4,z5,z6]),(0,[z7,z1,z2,z568,z4,z5,z6]),(0,[z7,z209,z56,z2,z4,z5,z6]),(0,[z316,z7,z2,z4,z5,z6,z145]),(0,[z7,z569,z1,z2,z4,z5,z6])]],
   [[(1,[z89,z13,z2,z4,z5,z6]),(0,[z502,z7,z1,z2,z4,z5,z6]),(0,[z570,z7,z1,z2,z4,z5,z6])],[(0,[z0,z72,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z571,z5,z6]),(0,[z7,z1,z2,z4,z5,z572,z6]),(0,[z7,z72,z1,z2,z4,z5,z6]),(0,[z7,z1,z573,z2,z4,z5,z6]),(0,[z574,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z575,z5,z6])],[(0,[z7,z72,z2,z4,z5,z92,z6]),(0,[z7,z2,z21,z4,z5,z50,z6]),(0,[z7,z349,z72,z2,z4,z5,z6])],[(0,[z1,z2,z4,z110,z38,z5,z6]),(0,[z7,z2,z576,z21,z4,z5,z6]),(0,[z39,z196,z1,z2,z4,z5,z6])],[(0,[z37,z7,z1,z2,z4,z5,z6]),(0,[z7,z259,z2,z21,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z170])],[(0,[z7,z1,z2,z577,z4,z5,z6]),(0,[z7,z1,z2,z4,z115,z5,z6]),(0,[z7,z1,z2,z4,z5,z26,z43]),(0,[z204,z7,z1,z2,z4,z5,z6])],[],[(0,[z13,z1,z2,z3,z4,z5,z6]),(1,[z7,z1,z2,z4,z455,z6]),(0,[z7,z1,z2,z4,z415,z5,z6])],[(0,[z199,z12,z7,z2,z4,z5,z6])],[(0,[z7,z2,z44,z21,z4,z5,z6])],[(0,[z578,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z579,z4,z5,z6]),(0,[z7,z1,z580,z2,z4,z5,z6]),(0,[z7,z1,z2,z581,z4,z5,z6]),(0,[z7,z1,z582,z2,z4,z5,z6]),(0,[z7,z1,z2,z583,z4,z5,z6])],[(0,[z7,z1,z584,z2,z4,z5,z6]),(0,[z7,z274,z1,z2,z4,z5,z6]),(0,[z12,z7,z259,z2,z4,z5,z6]),(0,[z7,z1,z2,z524,z4,z336,z5])],[(1,[z7,z171,z2,z4,z5,z6]),(1,[z191,z7,z2,z21,z4,z5]),(1,[z7,z2,z4,z5,z178,z6]),(0,[z7,z72,z2,z4,z5,z50,z6]),(1,[z296,z7,z2,z4,z109,z6])],[(0,[z7,z1,z2,z4,z5,z6,z468]),(0,[z585,z7,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z25,z4,z5,z6]),(0,[z7,z1,z2,z25,z4,z5,z6]),(0,[z20,z59,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z586,z6]),(0,[z7,z2,z21,z432,z4,z5,z6]),(0,[z35,z7,z1,z2,z4,z52,z6])],[(0,[z37,z7,z2,z4,z5,z50,z6]),(0,[z7,z1,z2,z4,z587,z5,z6]),(0,[z588,z7,z2,z21,z4,z5,z6]),(0,[z7,z1,z2,z589,z4,z5,z6])]],
   [[(0,[z7,z1,z590,z2,z4,z5,z6]),(0,[z59,z7,z1,z2,z129,z4,z6]),(0,[z204,z7,z2,z4,z5,z50,z6])],[(0,[z7,z1,z591,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z592,z6])],[],[(0,[z7,z1,z2,z4,z4,z5,z6]),(0,[z91,z7,z1,z2,z4,z5,z6]),(1,[z7,z185,z2,z4,z5,z6])],[(0,[z7,z1,z2,z593,z4,z5,z6]),(0,[z7,z1,z2,z4,z594,z5,z6])],[(0,[z595,z7,z1,z2,z4,z5,z6])],[(0,[z596,z0,z1,z2,z4,z5,z6]),(0,[z597,z7,z72,z2,z4,z5,z6]),(0,[z7,z119,z2,z78,z4,z5,z6])],[(0,[z7,z259,z72,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z547,z6])],[(0,[z7,z1,z2,z319,z4,z5,z6]),(0,[z91,z7,z1,z2,z4,z28,z6]),(0,[z7,z1,z2,z4,z598,z5,z6]),(0,[z7,z2,z21,z4,z336,z5,z6]),(0,[z7,z1,z2,z362,z4,z5,z6]),(0,[z7,z1,z271,z2,z4,z5,z6]),(0,[z7,z49,z1,z119,z2,z4,z5])],[(0,[z1,z2,z25,z4,z52,z5,z6]),(0,[z0,z7,z1,z100,z4,z5,z6])],[(0,[z12,z7,z1,z2,z4,z5,z50]),(0,[z7,z1,z2,z4,z599,z5,z6]),(0,[z7,z1,z2,z42,z4,z5,z43]),(0,[z7,z1,z2,z4,z5,z600,z6])],[(0,[z7,z1,z2,z4,z601,z5,z6]),(0,[z7,z1,z2,z4,z5,z602,z6]),(0,[z7,z1,z2,z4,z603,z5,z6])],[(0,[z604,z7,z1,z2,z4,z5,z6])],[(0,[z605,z7,z1,z2,z4,z5,z6]),(0,[z91,z7,z2,z4,z5,z50,z6]),(0,[z606,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z14,z4,z5,z387]),(0,[z7,z607,z1,z2,z4,z5,z6])],[(0,[z7,z1,z1,z2,z4,z5,z6]),(0,[z39,z7,z49,z1,z2,z4,z5]),(0,[z7,z1,z2,z4,z608,z5,z6]),(0,[z122,z7,z1,z2,z4,z5,z6])]],
   [[(0,[z1,z2,z25,z3,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z92,z6]),(1,[z12,z7,z2,z308,z4,z5]),(0,[z7,z609,z1,z2,z4,z5,z6])],[(0,[z12,z105,z7,z2,z4,z5,z6]),(1,[z1,z2,z272,z4,z5,z6]),(0,[z7,z183,z1,z2,z4,z5,z6])],[(1,[z191,z7,z1,z2,z4,z5]),(0,[z596,z7,z72,z2,z4,z5,z6]),(0,[z7,z1,z2,z610,z4,z5,z6])],[(0,[z27,z0,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z611,z6]),(2,[z191,z7,z2,z4,z5]),(0,[z7,z72,z2,z4,z336,z5,z6]),(0,[z120,z1,z76,z2,z4,z5,z6])],[(0,[z552,z7,z1,z2,z4,z5,z6]),(0,[z7,z501,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z612,z6])],[(0,[z7,z613,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z614,z6]),(0,[z55,z1,z2,z25,z4,z5,z6]),(0,[z0,z349,z1,z2,z4,z5,z6]),(0,[z59,z7,z2,z21,z4,z5,z6]),(1,[z7,z2,z362,z21,z4,z5]),(0,[z12,z7,z2,z4,z67,z5,z6]),(0,[z114,z7,z1,z2,z60,z5,z6]),(0,[z7,z1,z36,z2,z4,z52,z6])],[(0,[z7,z434,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z615,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z616,z6]),(0,[z214,z7,z2,z21,z4,z5,z6])],[(0,[z486,z7,z1,z2,z4,z5,z6]),(0,[z512,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z50,z6])],[(1,[z105,z7,z21,z4,z5,z6]),(0,[z617,z7,z1,z2,z4,z5,z6])],[(0,[z12,z1,z2,z25,z4,z5,z6]),(1,[z191,z7,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z460]),(1,[z7,z1,z2,z4,z5,z299])],[(0,[z1,z2,z25,z4,z5,z198,z6]),(0,[z59,z0,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z618]),(0,[z39,z7,z1,z4,z5,z6,z145]),(0,[z7,z1,z2,z69,z5,z28,z6])],[(0,[z12,z204,z7,z2,z4,z5,z6]),(0,[z12,z7,z1,z2,z71,z4,z5]),(0,[z7,z331,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z619,z5,z6])],[(0,[z0,z1,z620,z2,z4,z5,z6]),(0,[z7,z72,z2,z581,z4,z5,z6]),(1,[z7,z1,z2,z4,z5,z411])]],
   [[(0,[z621,z7,z1,z2,z4,z5,z6]),(0,[z349,z1,z2,z25,z4,z5,z6]),(0,[z214,z0,z1,z2,z4,z5,z6])],[(0,[z7,z2,z21,z308,z4,z5,z6]),(0,[z7,z1,z2,z622,z4,z5,z6]),(0,[z196,z7,z1,z2,z4,z5,z6])],[(0,[z1,z2,z25,z4,z15,z5,z6]),(1,[z7,z317,z2,z4,z5,z6]),(0,[z54,z1,z2,z4,z38,z5,z6]),(0,[z12,z7,z2,z129,z4,z5,z6]),(0,[z623,z7,z1,z2,z4,z5,z6])],[(0,[z7,z72,z2,z25,z4,z5,z6])],[(0,[z7,z1,z2,z624,z4,z5,z6])],[(0,[z12,z7,z99,z2,z4,z5,z6]),(0,[z89,z7,z2,z21,z4,z5,z6])],[(0,[z1,z119,z2,z25,z4,z5,z6]),(0,[z12,z55,z7,z2,z4,z5,z6])],[(0,[z12,z7,z2,z4,z227,z5,z6]),(0,[z7,z475,z1,z2,z4,z5,z6])],[(1,[z2,z25,z4,z5,z50,z6])],[(0,[z33,z1,z2,z4,z38,z5,z6]),(0,[z59,z7,z72,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z625]),(0,[z7,z1,z2,z284,z4,z5,z6]),(0,[z7,z626,z1,z2,z4,z5,z6])],[(0,[z114,z7,z2,z21,z4,z5,z6]),(0,[z7,z205,z1,z2,z4,z5,z6]),(1,[z7,z237,z2,z4,z5,z6])],[(0,[z7,z1,z2,z500,z4,z5,z6]),(0,[z0,z259,z1,z2,z4,z5,z6])],[(0,[z89,z0,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z627,z4,z5,z6]),(0,[z7,z76,z2,z21,z4,z5,z6]),(0,[z214,z7,z72,z2,z4,z5,z6])],[],[(0,[z39,z1,z2,z25,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z150])],[(0,[z7,z2,z21,z4,z5,z6,z127]),(0,[z7,z1,z2,z4,z628,z5,z6])]],
   [[(0,[z401,z7,z1,z2,z4,z5,z6]),(0,[z629,z7,z1,z2,z4,z5,z6])],[(0,[z630,z7,z1,z2,z4,z5,z6]),(0,[z104,z1,z2,z25,z4,z5,z6]),(0,[z47,z1,z2,z25,z4,z5,z6]),(0,[z114,z0,z1,z2,z4,z5,z6]),(0,[z0,z55,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z631,z6])],[(0,[z37,z89,z1,z2,z4,z5,z6])],[(0,[z7,z529,z1,z2,z4,z5,z6]),(0,[z632,z7,z1,z2,z4,z5,z6])],[(0,[z12,z7,z2,z4,z5,z26,z6])],[(1,[z7,z434,z2,z4,z5,z6])],[(0,[z596,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z633,z6])],[(0,[z1,z2,z25,z4,z5,z109,z6]),(1,[z124,z1,z2,z4,z5,z6])],[(0,[z7,z1,z634,z2,z4,z5,z6]),(0,[z89,z7,z72,z2,z4,z5,z6]),(0,[z7,z1,z2,z576,z4,z5,z6]),(1,[z7,z49,z2,z4,z5,z50]),(0,[z7,z1,z2,z4,z5,z127,z145])],[(0,[z273,z7,z1,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z92,z50,z6])],[(0,[z7,z1,z2,z635,z4,z5,z6]),(0,[z7,z1,z2,z4,z636,z5,z6])],[(0,[z91,z1,z2,z4,z110,z5,z6]),(0,[z7,z1,z2,z3,z4,z455,z6]),(0,[z7,z1,z2,z4,z5,z637,z6]),(0,[z91,z1,z2,z4,z5,z111,z6]),(0,[z12,z7,z2,z14,z4,z5,z6]),(0,[z39,z12,z7,z1,z2,z4,z5])],[(1,[z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z638,z5,z6]),(0,[z7,z1,z2,z4,z638,z5,z6]),(0,[z525,z7,z1,z2,z4,z5,z6]),(0,[z639,z7,z1,z2,z4,z5,z6])],[(0,[z104,z7,z1,z100,z4,z5,z6]),(0,[z114,z7,z72,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z640,z5,z6]),(0,[z420,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z641,z4,z5,z6]),(0,[z347,z7,z1,z2,z4,z5,z6])]],
   [[(0,[z12,z7,z2,z60,z4,z5,z6])],[(1,[z7,z1,z2,z4,z115,z6])],[(0,[z7,z36,z2,z21,z4,z5,z6]),(1,[z7,z259,z2,z14,z5,z6]),(0,[z7,z1,z2,z41,z14,z4,z5]),(0,[z316,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z642,z5,z6]),(0,[z7,z1,z2,z173,z4,z5,z6])],[(0,[z7,z2,z21,z4,z5,z6,z625]),(1,[z236,z1,z2,z4,z5,z6])],[(0,[z7,z1,z643,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z298])],[(0,[z0,z1,z2,z40,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z644,z6])],[(1,[z7,z2,z4,z5,z50,z6]),(0,[z645,z7,z1,z2,z4,z5,z6])],[(0,[z35,z1,z2,z25,z4,z5,z6]),(0,[z7,z2,z4,z5,z50,z6,z145]),(0,[z7,z2,z42,z4,z5,z50,z6]),(0,[z646,z7,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z308,z4,z5,z6]),(0,[z7,z1,z2,z308,z4,z5,z6])],[(0,[z105,z7,z1,z76,z4,z5,z6]),(0,[z7,z2,z2,z21,z4,z5,z6]),(0,[z12,z7,z2,z42,z4,z5,z6]),(0,[z12,z7,z49,z2,z4,z5,z6]),(0,[z7,z1,z2,z647,z4,z5,z6])],[(0,[z648,z7,z1,z2,z4,z5,z6]),(0,[z33,z7,z1,z2,z128,z5,z6]),(0,[z7,z1,z2,z4,z649,z5,z6]),(0,[z91,z7,z1,z2,z4,z92,z6]),(0,[z650,z7,z1,z2,z4,z5,z6])],[(0,[z651,z7,z1,z2,z4,z5,z6])],[(0,[z7,z13,z1,z2,z4,z5,z6]),(0,[z0,z13,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z652,z5,z6]),(0,[z7,z1,z2,z4,z5,z653,z6]),(0,[z39,z7,z1,z119,z4,z5,z6])],[(0,[z7,z1,z2,z4,z654,z5,z6]),(0,[z7,z1,z2,z655,z4,z5,z6]),(0,[z12,z7,z1,z2,z4,z5,z43]),(0,[z7,z2,z435,z4,z5,z50,z6]),(0,[z1,z56,z2,z272,z4,z5,z6]),(0,[z656,z7,z1,z2,z4,z5,z6])],[(1,[z7,z1,z2,z4,z543,z6])]],
   [[(0,[z7,z56,z2,z21,z4,z5,z6]),(0,[z214,z7,z1,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z50,z6,z43]),(1,[z339,z1,z2,z4,z5,z6])],[(0,[z55,z7,z1,z2,z4,z5,z73]),(0,[z7,z2,z128,z4,z5,z50,z6]),(0,[z657,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z658,z4,z5,z6])],[(0,[z0,z1,z2,z69,z4,z5,z6]),(0,[z7,z1,z659,z2,z4,z5,z6]),(1,[z91,z1,z2,z4,z92,z6]),(0,[z7,z1,z2,z660,z4,z5,z6]),(0,[z51,z7,z1,z2,z308,z4,z6])],[(0,[z191,z7,z2,z21,z4,z5,z6]),(0,[z7,z72,z2,z4,z5,z661,z6]),(0,[z7,z1,z2,z71,z4,z5,z145])],[(0,[z662,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z663,z2,z4,z5,z6]),(0,[z664,z7,z1,z2,z4,z5,z6])],[(0,[z0,z1,z76,z2,z4,z5,z6]),(0,[z665,z7,z1,z2,z4,z5,z6]),(0,[z666,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z667,z4,z5,z6]),(1,[z39,z12,z7,z2,z4,z5]),(0,[z7,z1,z2,z4,z5,z6,z416])],[(0,[z0,z1,z2,z4,z5,z6,z127]),(0,[z7,z1,z2,z668,z4,z5,z6]),(0,[z669,z7,z1,z2,z4,z5,z6]),(0,[z12,z7,z2,z71,z4,z5,z6]),(0,[z7,z2,z203,z4,z5,z50,z6]),(1,[z7,z1,z2,z4,z5,z112]),(0,[z670,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z127]),(0,[z7,z1,z2,z671,z4,z5,z6])],[(0,[z7,z13,z2,z4,z5,z50,z6]),(0,[z7,z2,z21,z3,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z672,z6]),(0,[z7,z1,z673,z2,z4,z5,z6]),(0,[z39,z7,z1,z2,z4,z5,z145])],[(0,[z7,z1,z2,z4,z5,z6,z29]),(0,[z7,z349,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z674,z4,z5,z6])],[(0,[z296,z1,z2,z25,z4,z5,z6]),(0,[z7,z1,z2,z4,z675,z5,z6])],[(0,[z105,z7,z2,z21,z4,z5,z6]),(0,[z214,z7,z2,z4,z5,z50,z6]),(0,[z7,z1,z2,z4,z5,z676,z6]),(0,[z7,z1,z2,z4,z5,z677,z6]),(0,[z12,z7,z2,z4,z5,z62,z6]),(1,[z7,z2,z4,z5,z6,z150]),(1,[z7,z1,z2,z4,z356,z6])],[(0,[z54,z1,z2,z25,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z616,z6]),(0,[z7,z100,z2,z4,z5,z50,z6]),(0,[z7,z1,z678,z2,z4,z5,z6])],[(0,[z13,z1,z99,z2,z4,z5,z6]),(0,[z7,z1,z679,z2,z4,z5,z6]),(0,[z7,z349,z1,z2,z4,z336,z6])],[(0,[z49,z1,z2,z25,z4,z5,z6]),(0,[z7,z1,z2,z680,z4,z5,z6])],[(0,[z7,z1,z2,z4,z681,z5,z6]),(0,[z7,z2,z443,z21,z4,z5,z6])]],
   [[],[(0,[z7,z1,z2,z4,z5,z682,z6]),(0,[z114,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z620,z2,z4,z5,z6]),(0,[z291,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z683,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z684,z6]),(0,[z204,z7,z1,z2,z42,z5,z6])],[(0,[z33,z1,z2,z25,z4,z5,z6]),(0,[z20,z7,z1,z2,z110,z5,z6]),(0,[z7,z685,z1,z2,z4,z5,z6])],[(0,[z7,z349,z2,z4,z5,z50,z6]),(1,[z12,z7,z2,z4,z5,z50]),(0,[z7,z1,z2,z4,z5,z6,z411]),(0,[z1,z2,z129,z11,z4,z5,z6])],[],[(0,[z12,z104,z7,z2,z4,z5,z6])],[(0,[z1,z2,z25,z4,z67,z5,z6]),(0,[z296,z7,z2,z4,z5,z109,z6]),(0,[z7,z1,z60,z4,z16,z5,z6])],[(0,[z12,z59,z7,z2,z4,z5,z6]),(0,[z7,z209,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z686]),(0,[z199,z7,z72,z2,z4,z5,z6]),(1,[z7,z1,z2,z277,z5,z6])],[(0,[z12,z20,z7,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z111,z6,z73]),(0,[z191,z7,z1,z2,z21,z4,z5]),(0,[z7,z2,z4,z336,z5,z109,z6]),(0,[z687,z7,z1,z2,z4,z5,z6]),(0,[z39,z7,z374,z2,z4,z5,z6])],[(1,[z7,z1,z2,z315,z5,z6]),(0,[z296,z7,z1,z2,z4,z109,z6]),(0,[z7,z1,z2,z4,z5,z688,z6]),(0,[z7,z1,z2,z689,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z690,z6]),(0,[z7,z1,z2,z691,z4,z5,z6])],[(0,[z7,z1,z2,z692,z4,z5,z6]),(0,[z7,z2,z4,z5,z111,z50,z6]),(0,[z114,z7,z2,z4,z5,z50,z6]),(0,[z7,z1,z2,z78,z4,z5,z6])],[(0,[z7,z2,z21,z69,z4,z5,z6]),(0,[z597,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z308,z4,z5,z26])],[(0,[z105,z7,z72,z2,z4,z5,z6]),(0,[z7,z72,z2,z308,z4,z5,z6]),(0,[z7,z259,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z693,z4,z5,z6])],[(0,[z7,z1,z694,z2,z4,z5,z6]),(1,[z7,z349,z2,z4,z336,z6])]],
   [[(0,[z7,z1,z2,z4,z695,z5,z6])],[(0,[z7,z1,z696,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z661,z6])],[(0,[z697,z7,z1,z2,z4,z5,z6]),(0,[z0,z7,z1,z25,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z698]),(0,[z7,z1,z2,z4,z5,z6,z699]),(0,[z51,z7,z1,z2,z308,z4,z5])],[(0,[z1,z2,z25,z129,z4,z5,z6]),(0,[z12,z7,z1,z2,z4,z5,z188]),(0,[z7,z1,z93,z2,z4,z5,z6])],[(0,[z12,z7,z2,z439,z4,z5,z6]),(0,[z114,z7,z1,z2,z4,z543,z6]),(0,[z7,z1,z2,z4,z5,z6,z700])],[(0,[z7,z2,z4,z5,z50,z6,z188])],[(0,[z549,z7,z1,z2,z4,z5,z6]),(0,[z12,z12,z7,z2,z4,z5,z6]),(0,[z7,z1,z701,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z118,z6,z43])],[(0,[z7,z72,z2,z69,z4,z5,z6]),(1,[z12,z7,z2,z71,z4,z5])],[(0,[z7,z1,z2,z4,z702,z5,z6]),(0,[z7,z1,z2,z703,z4,z5,z6])],[(0,[z7,z1,z2,z704,z4,z5,z6]),(0,[z588,z7,z1,z2,z4,z5,z6]),(0,[z7,z259,z2,z4,z5,z50,z6])],[(0,[z0,z1,z2,z4,z52,z5,z6]),(0,[z7,z72,z76,z2,z4,z5,z6]),(0,[z289,z12,z7,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z705]),(0,[z7,z1,z2,z4,z52,z5,z6]),(0,[z7,z1,z2,z129,z4,z62,z6])],[(0,[z7,z349,z2,z4,z336,z5,z6]),(0,[z7,z49,z1,z2,z308,z4,z5]),(0,[z39,z7,z332,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z18,z127])],[(0,[z7,z72,z2,z4,z5,z6,z127])],[],[(0,[z706,z7,z1,z2,z4,z5,z6]),(0,[z264,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z231,z4,z5,z6]),(0,[z7,z2,z21,z4,z5,z109,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z634,z4,z5,z6]),(0,[z35,z7,z21,z4,z62,z6]),(0,[z707,z1,z2,z4,z5,z6]),(0,[z316,z7,z119,z2,z4,z5])],[(0,[z552,z1,z2,z4,z5,z616]),(0,[z0,z1,z36,z4,z52,z6]),(0,[z191,z91,z7,z2,z4,z5]),(0,[z12,z7,z2,z71,z113,z5]),(0,[z12,z7,z278,z2,z4,z5]),(0,[z708,z1,z2,z4,z5,z6]),(0,[z7,z2,z709,z4,z5,z6])],[(0,[z7,z1,z2,z4,z710,z6]),(0,[z7,z2,z4,z5,z310,z6]),(0,[z7,z2,z90,z5,z50,z6]),(0,[z2,z11,z4,z5,z50,z6])],[(0,[z37,z711,z2,z4,z5,z6]),(0,[z712,z7,z2,z4,z5,z6]),(0,[z199,z2,z25,z4,z5,z6]),(0,[z180,z2,z21,z4,z5,z6])],[(0,[z711,z99,z2,z4,z5,z6]),(0,[z7,z2,z713,z4,z5,z6]),(0,[z2,z21,z4,z5,z154,z6]),(0,[z7,z2,z21,z4,z5,z460]),(0,[z12,z7,z2,z4,z5,z705]),(0,[z12,z180,z2,z4,z5,z6]),(0,[z7,z49,z2,z4,z5,z714]),(0,[z715,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z716,z5,z6])],[(0,[z7,z1,z2,z4,z717,z6]),(0,[z7,z1,z2,z718,z5,z6]),(0,[z7,z1,z2,z719,z5,z6])],[(0,[z7,z1,z2,z5,z720,z6]),(0,[z7,z2,z315,z5,z50,z6]),(0,[z7,z2,z41,z4,z15,z5])],[(0,[z54,z2,z4,z5,z50,z73]),(0,[z7,z2,z21,z128,z129,z6]),(0,[z39,z199,z7,z2,z4,z5]),(0,[z7,z1,z721,z4,z5,z6])],[(0,[z7,z722,z2,z4,z5,z6]),(0,[z80,z2,z25,z4,z5,z6])],[(0,[z0,z72,z2,z4,z5,z6]),(0,[z7,z2,z439,z4,z5,z6]),(0,[z191,z7,z349,z2,z4,z5]),(0,[z214,z236,z2,z15,z5,z6]),(0,[z196,z1,z2,z4,z197,z6]),(0,[z7,z1,z2,z129,z723,z6])],[(0,[z209,z2,z25,z4,z5,z6]),(0,[z12,z0,z2,z71,z4,z5]),(0,[z12,z7,z2,z4,z5,z407]),(0,[z51,z7,z2,z308,z4,z50])],[(0,[z12,z7,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z460]),(0,[z12,z7,z2,z4,z5,z724]),(0,[z7,z1,z36,z4,z725,z6])],[(0,[z1,z2,z25,z726,z4,z5]),(0,[z7,z727,z2,z4,z5,z6]),(0,[z7,z98,z21,z4,z5,z6]),(0,[z35,z180,z1,z4,z62,z6]),(0,[z7,z374,z2,z4,z356,z6])],[(0,[z7,z72,z36,z4,z52,z6]),(0,[z7,z1,z4,z5,z6,z728])],[(0,[z0,z1,z2,z128,z129,z6]),(0,[z285,z72,z2,z4,z5,z6])],[(0,[z7,z1,z2,z53,z4,z6]),(0,[z7,z2,z4,z5,z729,z6]),(0,[z191,z7,z2,z4,z5,z73]),(0,[z730,z7,z2,z4,z5,z6]),(0,[z7,z2,z69,z28,z50,z6])]],
   [[(0,[z2,z25,z4,z5,z358,z6]),(0,[z0,z330,z2,z4,z5,z6]),(0,[z39,z7,z2,z439,z4,z5]),(0,[z12,z7,z2,z4,z115,z6]),(0,[z7,z731,z2,z4,z5,z6])],[(0,[z732,z7,z2,z4,z5,z6]),(0,[z7,z1,z2,z125,z129,z6]),(0,[z204,z7,z1,z2,z733,z5])],[(0,[z1,z2,z97,z4,z5,z6]),(0,[z191,z55,z7,z2,z4,z5]),(0,[z114,z12,z7,z16,z5,z6]),(0,[z7,z2,z4,z5,z724,z43]),(0,[z7,z734,z2,z4,z5,z6]),(0,[z735,z7,z2,z4,z5,z299]),(0,[z7,z1,z2,z610,z28,z6]),(0,[z7,z2,z4,z5,z6,z736])],[(0,[z191,z7,z2,z3,z4,z5]),(0,[z7,z737,z2,z4,z5,z6])],[(0,[z12,z0,z100,z4,z5,z6]),(0,[z0,z1,z509,z4,z5,z6]),(0,[z54,z1,z2,z4,z5,z554]),(0,[z1,z2,z4,z5,z738,z6]),(0,[z7,z434,z2,z137,z5,z6]),(0,[z7,z330,z36,z4,z52,z6])],[(0,[z20,z7,z1,z2,z455,z6]),(0,[z7,z1,z2,z4,z739,z6]),(0,[z7,z2,z4,z5,z740,z6]),(0,[z39,z7,z4,z5,z6,z150]),(0,[z1,z2,z4,z5,z6,z741])],[(0,[z180,z72,z2,z4,z5,z6]),(0,[z7,z2,z742,z4,z5,z6])],[(0,[z191,z33,z7,z2,z4,z5]),(0,[z7,z72,z2,z4,z5,z460]),(0,[z7,z1,z2,z69,z28,z6])],[(0,[z0,z743,z2,z4,z5,z6]),(0,[z39,z191,z7,z2,z4,z5]),(0,[z114,z331,z1,z16,z5,z6])],[(0,[z32,z0,z2,z4,z5,z6]),(0,[z7,z2,z21,z4,z5,z744]),(0,[z745,z7,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z312,z127])],[(0,[z7,z2,z4,z5,z746,z6]),(0,[z7,z72,z2,z128,z129,z6]),(0,[z7,z1,z2,z4,z5,z747]),(0,[z7,z1,z2,z4,z62,z411])],[(0,[z7,z1,z2,z137,z5,z6]),(0,[z7,z1,z2,z71,z733,z5])],[(0,[z7,z1,z2,z4,z5,z748]),(0,[z2,z70,z78,z4,z5,z6]),(1,[z7,z1,z2,z723,z6]),(0,[z1,z2,z749,z4,z5,z6])],[(0,[z55,z1,z2,z4,z5,z111]),(0,[z7,z750,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z751]),(0,[z7,z1,z60,z752,z5,z6]),(0,[z180,z1,z2,z4,z5,z411]),(0,[z7,z332,z2,z4,z356,z6]),(0,[z7,z1,z2,z753,z4,z6])],[(0,[z7,z72,z94,z4,z5,z6]),(0,[z59,z1,z2,z4,z601,z6]),(0,[z12,z7,z2,z4,z543,z6]),(0,[z1,z2,z754,z4,z5,z6])],[(0,[z755,z1,z2,z4,z5,z6]),(0,[z33,z1,z2,z3,z455,z6]),(0,[z54,z1,z2,z53,z4,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z744]),(0,[z7,z259,z2,z41,z4,z5])],[(0,[z316,z2,z25,z4,z5,z6]),(0,[z33,z1,z2,z3,z5,z6]),(0,[z1,z2,z4,z38,z6,z698]),(0,[z191,z7,z2,z4,z38,z5]),(0,[z7,z2,z756,z4,z5,z6])],[(0,[z0,z2,z4,z5,z6,z156]),(0,[z7,z1,z2,z757,z5,z6]),(0,[z1,z2,z258,z3,z5,z6]),(0,[z7,z2,z439,z4,z5,z127]),(0,[z2,z272,z4,z5,z50,z6]),(0,[z7,z1,z2,z90,z5,z6])],[(0,[z7,z1,z2,z758,z5,z6]),(0,[z0,z152,z2,z4,z5,z6]),(0,[z12,z2,z25,z4,z5,z6]),(0,[z7,z2,z759,z4,z5,z6]),(0,[z7,z2,z4,z5,z760,z6])],[(0,[z7,z1,z2,z761,z4,z5]),(0,[z7,z2,z21,z4,z455,z6]),(0,[z7,z762,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z763,z6])],[(0,[z7,z1,z2,z4,z764,z6]),(0,[z7,z1,z2,z4,z5,z765]),(0,[z7,z21,z4,z5,z6,z150]),(0,[z199,z7,z119,z2,z4,z5]),(0,[z7,z2,z4,z5,z766,z6]),(0,[z7,z439,z4,z16,z5,z6])],[(0,[z2,z25,z4,z5,z6,z767]),(0,[z7,z1,z2,z4,z768,z6]),(0,[z7,z2,z21,z769,z4,z6]),(0,[z770,z191,z7,z2,z4,z5]),(0,[z771,z72,z2,z4,z5,z6]),(0,[z7,z349,z2,z4,z79,z6]),(0,[z12,z7,z2,z4,z5,z112])],[(0,[z772,z1,z2,z4,z5,z6]),(0,[z1,z2,z773,z4,z5,z6])],[(0,[z105,z25,z21,z4,z5,z6]),(0,[z1,z2,z774,z4,z5,z6])],[(0,[z7,z775,z2,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z637]),(0,[z7,z776,z2,z4,z5,z6]),(0,[z347,z183,z2,z4,z5,z6])],[(0,[z296,z7,z2,z4,z661,z6]),(0,[z12,z7,z2,z4,z356,z6]),(0,[z12,z7,z2,z308,z4,z127])],[(0,[z7,z777,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z455,z6]),(0,[z778,z1,z2,z4,z5,z6]),(0,[z779,z1,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z780]),(0,[z7,z1,z48,z4,z5,z26]),(0,[z51,z7,z371,z2,z308,z4])],[(0,[z1,z2,z4,z5,z154,z6]),(0,[z7,z1,z2,z524,z4,z5]),(0,[z7,z216,z2,z4,z5,z411]),(0,[z1,z2,z781,z4,z5,z6])],[(0,[z104,z66,z25,z4,z5,z6]),(0,[z59,z2,z4,z38,z50,z6]),(0,[z7,z2,z21,z782,z4,z6]),(0,[z7,z2,z21,z783,z4,z5]),(0,[z7,z784,z2,z4,z5,z6]),(0,[z549,z7,z2,z113,z5,z6]),(0,[z785,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z786,z5,z6])],[(0,[z49,z2,z25,z4,z5,z50]),(0,[z20,z1,z2,z598,z5,z6]),(0,[z236,z2,z21,z4,z5,z6]),(0,[z787,z1,z2,z4,z5,z6])],[(0,[z13,z1,z2,z315,z5,z6]),(0,[z788,z7,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z358,z6]),(0,[z7,z1,z2,z4,z789,z6]),(0,[z12,z790,z2,z4,z5,z6])]],
   [[(0,[z1,z2,z4,z161,z5,z6]),(0,[z0,z2,z4,z5,z178,z6]),(0,[z0,z171,z2,z4,z5,z6]),(0,[z2,z284,z21,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z714]),(0,[z791,z7,z2,z4,z5,z6])],[(0,[z403,z1,z25,z4,z5,z6]),(0,[z12,z439,z25,z4,z5,z6]),(0,[z2,z439,z25,z4,z5,z6]),(0,[z7,z21,z4,z636,z5,z6])],[(0,[z12,z7,z2,z4,z5,z519]),(0,[z105,z229,z21,z4,z5,z6]),(0,[z7,z2,z792,z4,z5,z6]),(0,[z7,z2,z4,z5,z793,z6])],[(0,[z1,z2,z25,z46,z5,z6]),(0,[z0,z1,z2,z794,z4,z6]),(0,[z1,z2,z315,z110,z5,z6]),(0,[z1,z2,z315,z5,z111,z6]),(0,[z790,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z437,z5,z43]),(0,[z7,z36,z4,z52,z50,z6])],[(0,[z7,z2,z4,z5,z795,z6]),(0,[z86,z7,z2,z4,z109,z6]),(0,[z12,z7,z2,z796,z5,z6]),(0,[z35,z12,z7,z4,z62,z6]),(0,[z797,z1,z2,z4,z5,z6])],[(0,[z54,z1,z2,z4,z5,z765]),(0,[z798,z1,z2,z4,z5,z6]),(0,[z799,z7,z2,z5,z50,z6]),(0,[z7,z2,z4,z197,z50,z6]),(0,[z1,z2,z800,z4,z5,z6])],[(0,[z7,z1,z2,z16,z543,z6])],[(0,[z0,z185,z2,z4,z5,z6]),(0,[z1,z2,z459,z4,z38,z6]),(0,[z7,z72,z2,z4,z455,z6]),(0,[z91,z1,z2,z4,z768,z6]),(0,[z72,z2,z97,z4,z5,z6]),(0,[z7,z801,z2,z4,z5,z6]),(0,[z656,z7,z1,z4,z5,z145])],[(0,[z0,z1,z22,z4,z5,z6]),(0,[z191,z191,z7,z2,z4,z5]),(0,[z12,z7,z2,z277,z5,z6]),(0,[z12,z7,z2,z802,z4,z5]),(0,[z39,z7,z4,z5,z156,z145]),(0,[z7,z1,z4,z5,z26,z803])],[(0,[z7,z1,z2,z4,z804,z6]),(0,[z1,z2,z805,z4,z5,z6]),(0,[z7,z1,z2,z128,z622,z6])],[(0,[z180,z1,z2,z4,z5,z6]),(0,[z12,z0,z2,z4,z5,z43]),(0,[z12,z7,z2,z315,z5,z6])],[(0,[z7,z72,z2,z4,z5,z806]),(0,[z807,z1,z2,z4,z5,z6]),(0,[z7,z349,z2,z4,z227,z6]),(0,[z7,z2,z4,z50,z6,z808]),(0,[z342,z93,z2,z4,z5,z6])],[(0,[z12,z7,z2,z4,z5,z247]),(0,[z12,z2,z25,z4,z5,z127]),(0,[z7,z809,z2,z4,z5,z6]),(0,[z597,z7,z2,z379,z5,z6])],[(0,[z27,z1,z2,z4,z447,z6]),(0,[z12,z7,z2,z431,z4,z5]),(0,[z55,z2,z4,z5,z111,z50]),(0,[z7,z1,z2,z753,z4,z5])],[(0,[z20,z1,z2,z459,z5,z6]),(0,[z7,z1,z2,z128,z129,z6])],[(0,[z7,z1,z2,z5,z810,z6]),(0,[z7,z2,z4,z5,z6,z811])]],
   [[(0,[z7,z330,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z812]),(1,[z813,z7,z2,z4,z5])],[(0,[z502,z7,z2,z4,z5,z6]),(0,[z7,z2,z814,z4,z5,z6]),(0,[z236,z72,z2,z4,z5,z6]),(0,[z382,z7,z2,z84,z5,z6]),(0,[z7,z815,z2,z4,z5,z6]),(0,[z7,z1,z2,z90,z356,z6])],[(0,[z12,z7,z2,z4,z5,z147])],[(0,[z33,z1,z2,z173,z5,z6]),(0,[z1,z2,z4,z67,z18,z127])],[(0,[z1,z2,z25,z4,z197,z6]),(0,[z7,z1,z2,z816,z5,z6]),(0,[z7,z259,z2,z581,z5,z6]),(0,[z7,z2,z4,z5,z714,z188]),(0,[z7,z1,z2,z399,z28,z6]),(0,[z39,z7,z1,z4,z5,z145]),(0,[z32,z7,z2,z4,z67,z127])],[(0,[z7,z2,z4,z5,z6,z767]),(0,[z191,z7,z2,z576,z4,z5]),(0,[z7,z2,z21,z4,z5,z817]),(0,[z12,z7,z119,z2,z4,z5]),(0,[z180,z2,z4,z5,z50,z6])],[(0,[z2,z25,z57,z4,z5,z6]),(0,[z1,z25,z4,z5,z644,z6]),(0,[z12,z7,z2,z4,z5,z153]),(0,[z7,z2,z4,z5,z50,z460]),(0,[z12,z347,z2,z4,z5,z6]),(0,[z7,z1,z2,z90,z5,z26])],[(0,[z246,z99,z2,z4,z5,z6]),(0,[z1,z2,z53,z4,z92,z6])],[(0,[z7,z743,z2,z4,z5,z6]),(1,[z191,z7,z2,z4,z5])],[(0,[z7,z2,z21,z4,z5,z299]),(0,[z7,z216,z2,z4,z5,z6]),(0,[z7,z1,z2,z818,z5,z6])],[(0,[z2,z25,z21,z4,z5,z6]),(0,[z1,z2,z25,z819,z5,z6]),(0,[z0,z2,z362,z21,z4,z5]),(0,[z771,z1,z2,z4,z5,z6]),(0,[z1,z2,z820,z4,z5,z6]),(0,[z7,z821,z2,z4,z5,z6])],[(0,[z822,z1,z2,z4,z5,z6]),(0,[z7,z823,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z824]),(0,[z2,z21,z4,z161,z5,z6]),(0,[z246,z2,z4,z5,z230,z6]),(0,[z7,z2,z5,z50,z6,z825])],[(0,[z0,z826,z2,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z167]),(0,[z7,z2,z21,z4,z5,z411]),(0,[z7,z72,z2,z4,z543,z6]),(0,[z827,z7,z1,z4,z5,z6])],[(0,[z99,z2,z508,z4,z5,z6]),(0,[z13,z711,z2,z4,z5,z6]),(0,[z828,z1,z2,z4,z5,z6])],[(0,[z182,z1,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z829]),(0,[z12,z2,z284,z4,z5,z6]),(0,[z7,z537,z2,z4,z5,z50]),(0,[z7,z93,z2,z4,z5,z368])],[(0,[z830,z1,z2,z4,z5,z6]),(0,[z7,z2,z84,z41,z4,z5])]],
   [[(0,[z7,z1,z2,z4,z5,z744]),(0,[z0,z1,z2,z4,z5,z299]),(0,[z7,z2,z4,z5,z831,z6]),(0,[z7,z2,z832,z5,z50,z6]),(0,[z7,z1,z2,z42,z5,z43])],[(0,[z7,z833,z2,z4,z5,z6]),(0,[z2,z97,z21,z4,z5,z6]),(0,[z7,z49,z2,z4,z5,z358]),(0,[z72,z2,z4,z5,z154,z6]),(0,[z12,z7,z2,z834,z5,z6]),(0,[z7,z205,z2,z71,z4,z5])],[(0,[z7,z418,z2,z4,z5,z6]),(0,[z2,z4,z5,z154,z50,z6]),(0,[z12,z835,z2,z4,z5,z6]),(0,[z2,z836,z4,z5,z50,z6])],[(0,[z7,z152,z2,z4,z5,z6]),(0,[z1,z488,z25,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z411]),(0,[z7,z2,z4,z5,z358,z26])],[(0,[z293,z1,z25,z4,z5,z6]),(0,[z199,z7,z2,z308,z4,z5]),(0,[z2,z837,z4,z5,z50,z6]),(0,[z7,z838,z2,z4,z5,z6])],[(0,[z148,z2,z432,z4,z5,z6]),(0,[z1,z2,z25,z4,z839,z6]),(0,[z1,z25,z610,z4,z5,z6]),(0,[z59,z1,z2,z315,z5,z6]),(0,[z72,z2,z4,z161,z5,z6]),(0,[z285,z1,z2,z4,z5,z299])],[(0,[z214,z2,z25,z15,z5,z6]),(0,[z0,z317,z2,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z363]),(0,[z191,z7,z2,z4,z106,z5]),(0,[z191,z7,z49,z2,z4,z5]),(0,[z7,z259,z2,z179,z5,z6])],[(0,[z204,z7,z418,z2,z71,z5])],[(0,[z37,z245,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z765,z73]),(0,[z7,z840,z2,z4,z5,z6]),(0,[z7,z2,z841,z21,z4,z5]),(0,[z199,z7,z2,z4,z5,z297]),(0,[z12,z7,z2,z41,z4,z5]),(0,[z285,z1,z2,z4,z5,z411])],[(0,[z7,z842,z2,z4,z5,z6]),(1,[z1,z2,z843,z5,z6]),(0,[z33,z7,z1,z2,z455,z6]),(0,[z12,z7,z2,z202,z4,z5]),(0,[z182,z2,z4,z5,z50,z6]),(0,[z7,z844,z2,z4,z5,z6]),(0,[z7,z845,z2,z4,z5,z6]),(0,[z7,z846,z2,z4,z5,z6])],[(0,[z39,z12,z2,z25,z4,z5]),(0,[z7,z1,z2,z627,z28,z6]),(0,[z7,z2,z21,z847,z4,z5]),(1,[z39,z7,z439,z4,z5])],[(0,[z1,z2,z4,z5,z6,z848]),(0,[z7,z349,z2,z524,z4,z5]),(0,[z7,z2,z4,z849,z50,z6])],[(0,[z7,z72,z2,z4,z5,z299]),(0,[z39,z316,z7,z4,z5,z145])],[(0,[z12,z0,z2,z4,z5,z616]),(0,[z12,z33,z2,z3,z5,z6]),(0,[z7,z2,z4,z5,z850,z6]),(0,[z7,z851,z2,z4,z5,z6]),(0,[z199,z7,z2,z4,z5,z358]),(0,[z7,z491,z2,z4,z5,z50]),(0,[z180,z1,z2,z4,z5,z299])],[(0,[z152,z2,z25,z4,z5,z6]),(0,[z852,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z853]),(0,[z0,z237,z2,z4,z5,z6]),(0,[z7,z1,z2,z308,z4,z227])],[(0,[z7,z2,z4,z5,z854,z6]),(0,[z12,z0,z2,z4,z5,z188]),(0,[z7,z72,z2,z4,z5,z411]),(0,[z7,z1,z2,z4,z5,z855])]],
   [[(0,[z7,z171,z2,z4,z5,z6]),(0,[z296,z7,z2,z4,z109,z6]),(0,[z7,z856,z2,z4,z5,z6]),(0,[z7,z1,z2,z857,z4,z6]),(0,[z858,z1,z2,z4,z5,z6]),(0,[z7,z2,z859,z4,z5,z6]),(0,[z80,z2,z4,z5,z6,z416])],[(0,[z1,z2,z860,z4,z5,z6]),(0,[z20,z1,z2,z638,z5,z6]),(0,[z7,z371,z2,z4,z5,z6])],[(0,[z105,z7,z439,z4,z5,z6]),(0,[z191,z7,z2,z4,z5,z28])],[(0,[z861,z7,z2,z4,z5,z6]),(0,[z7,z1,z2,z841,z4,z5]),(0,[z7,z1,z2,z4,z862,z6]),(0,[z863,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z864]),(0,[z124,z2,z21,z4,z5,z6]),(0,[z191,z7,z2,z4,z15,z5]),(0,[z7,z1,z2,z783,z4,z5]),(0,[z199,z7,z439,z4,z5,z6]),(0,[z296,z7,z2,z4,z865,z6]),(0,[z7,z1,z752,z16,z5,z6]),(0,[z339,z1,z2,z42,z5,z43])],[(0,[z866,z7,z2,z4,z5,z6]),(0,[z7,z2,z57,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z867])],[(0,[z7,z1,z2,z450,z28,z6])],[(0,[z7,z185,z2,z4,z5,z6]),(0,[z0,z1,z590,z4,z5,z6]),(0,[z191,z7,z2,z4,z67,z5]),(0,[z7,z2,z868,z57,z4,z5]),(0,[z180,z1,z2,z277,z5,z6]),(0,[z7,z1,z2,z753,z4,z67])],[(0,[z91,z1,z2,z4,z447,z6]),(0,[z7,z2,z869,z4,z5,z6]),(0,[z12,z2,z173,z4,z5,z6]),(0,[z7,z1,z2,z60,z543,z6]),(0,[z7,z870,z2,z4,z5,z6])],[(0,[z7,z2,z21,z4,z5,z6]),(0,[z332,z2,z25,z4,z5,z6]),(0,[z7,z1,z2,z871,z5,z6]),(0,[z0,z434,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z872]),(0,[z7,z873,z2,z4,z5,z6]),(0,[z874,z1,z2,z4,z5,z6])],[(0,[z7,z2,z4,z5,z6,z875]),(0,[z7,z876,z2,z4,z5,z6]),(0,[z122,z1,z2,z4,z67,z127])],[(0,[z191,z7,z2,z4,z5,z625]),(0,[z12,z124,z2,z4,z5,z6])],[(0,[z0,z49,z2,z4,z5,z50]),(0,[z7,z2,z877,z4,z5,z6]),(0,[z191,z486,z7,z2,z4,z5]),(0,[z7,z216,z2,z4,z5,z299]),(0,[z7,z1,z2,z878,z4,z5])],[(0,[z12,z7,z2,z4,z5,z219]),(0,[z114,z7,z348,z16,z5,z6]),(0,[z182,z1,z2,z4,z356,z6])],[(0,[z7,z2,z21,z4,z115,z6]),(0,[z7,z56,z57,z60,z5,z6]),(0,[z285,z434,z2,z4,z5,z6]),(0,[z39,z316,z7,z2,z4,z5])],[(0,[z7,z2,z4,z5,z6,z879]),(0,[z124,z1,z36,z4,z52,z6]),(0,[z7,z374,z2,z46,z5,z6]),(0,[z51,z7,z1,z2,z753,z4])]],
   [[(0,[z0,z1,z2,z4,z5,z6]),(0,[z13,z2,z231,z4,z5,z6]),(0,[z114,z1,z25,z16,z5,z6]),(0,[z7,z2,z21,z4,z5,z880]),(0,[z12,z51,z7,z2,z308,z4]),(0,[z1,z2,z4,z5,z6,z881])],[(0,[z1,z2,z25,z362,z4,z5]),(0,[z7,z882,z2,z4,z5,z6]),(0,[z7,z2,z21,z883,z5,z6]),(0,[z884,z1,z2,z4,z5,z6]),(0,[z34,z367,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z885,z368]),(1,[z7,z1,z752,z5,z6]),(0,[z7,z2,z4,z5,z6,z886])],[(0,[z7,z56,z21,z60,z5,z6]),(0,[z12,z122,z2,z4,z5,z127]),(0,[z7,z1,z2,z71,z179,z5]),(0,[z316,z7,z2,z308,z4,z5]),(0,[z122,z2,z4,z5,z310,z6])],[(0,[z37,z186,z2,z4,z5,z6]),(0,[z1,z2,z25,z887,z5,z6]),(0,[z596,z620,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z740,z112])],[(0,[z1,z25,z4,z5,z631,z6]),(0,[z1,z2,z4,z5,z6,z888]),(0,[z1,z2,z53,z4,z110,z6]),(0,[z7,z2,z4,z5,z889,z6]),(0,[z7,z2,z44,z14,z5,z6]),(0,[z12,z7,z2,z890,z5,z6]),(0,[z7,z1,z36,z4,z52,z6])],[(0,[z7,z1,z2,z4,z5,z891]),(0,[z285,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z115,z6]),(0,[z235,z7,z2,z4,z661,z6]),(0,[z1,z2,z892,z4,z5,z6]),(0,[z401,z7,z2,z4,z208,z6]),(0,[z12,z331,z2,z4,z5,z6])],[(0,[z893,z7,z2,z4,z5,z6]),(0,[z2,z25,z4,z5,z6,z156]),(0,[z0,z259,z2,z14,z5,z6]),(0,[z7,z894,z2,z4,z5,z6]),(0,[z895,z1,z2,z4,z5,z6]),(0,[z191,z7,z1,z2,z4,z5]),(0,[z12,z204,z7,z2,z71,z5]),(0,[z39,z7,z1,z439,z4,z5]),(0,[z180,z434,z2,z4,z5,z6]),(0,[z7,z216,z2,z277,z5,z6]),(0,[z7,z1,z2,z4,z5,z896]),(0,[z1,z2,z897,z4,z5,z6])],[(0,[z7,z898,z2,z4,z5,z6]),(0,[z204,z1,z2,z25,z71,z5]),(0,[z0,z1,z2,z4,z5,z880]),(0,[z140,z1,z2,z40,z5,z6]),(0,[z899,z7,z2,z4,z5,z6]),(0,[z124,z72,z2,z4,z5,z6]),(0,[z12,z119,z2,z70,z4,z5]),(0,[z7,z1,z2,z4,z5,z900])],[(0,[z901,z1,z2,z4,z5,z6]),(0,[z20,z59,z1,z2,z28,z6]),(0,[z12,z7,z2,z4,z5,z297]),(0,[z12,z7,z2,z84,z4,z5]),(0,[z2,z4,z5,z118,z6,z416]),(0,[z902,z1,z2,z4,z5,z6])],[(0,[z799,z7,z1,z2,z5,z6]),(0,[z7,z1,z2,z903,z4,z6]),(0,[z7,z1,z2,z904,z5,z6]),(0,[z905,z1,z2,z4,z5,z6]),(0,[z7,z906,z2,z4,z5,z6])],[(0,[z7,z49,z2,z4,z5,z310])],[(0,[z0,z2,z4,z5,z50,z6]),(0,[z121,z1,z2,z110,z5,z6]),(0,[z7,z2,z4,z5,z907,z6]),(0,[z7,z1,z2,z4,z5,z908]),(0,[z909,z7,z2,z4,z5,z6]),(0,[z12,z2,z4,z5,z6,z416])],[(0,[z7,z72,z2,z4,z5,z6]),(0,[z12,z0,z25,z4,z5,z6]),(0,[z7,z2,z21,z4,z543,z6]),(0,[z7,z119,z21,z4,z5,z26]),(0,[z7,z1,z2,z4,z5,z817]),(0,[z7,z2,z4,z910,z5,z6]),(0,[z1,z911,z2,z4,z5,z6]),(0,[z12,z7,z48,z2,z4,z5]),(0,[z912,z1,z2,z4,z5,z6])],[(0,[z89,z412,z2,z4,z5,z6]),(0,[z104,z25,z21,z4,z5,z6]),(0,[z51,z1,z2,z25,z308,z4]),(0,[z1,z2,z843,z110,z5,z6]),(0,[z339,z2,z21,z4,z5,z6]),(0,[z7,z1,z2,z913,z4,z5]),(0,[z12,z7,z2,z4,z5,z358]),(0,[z914,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z915]),(0,[z916,z1,z2,z4,z5,z6])],[(0,[z375,z7,z2,z4,z5,z50]),(0,[z7,z917,z2,z4,z5,z6]),(0,[z191,z7,z72,z21,z4,z5]),(0,[z7,z1,z2,z4,z5,z460]),(0,[z124,z330,z2,z4,z5,z6])],[(0,[z1,z2,z25,z5,z200,z6]),(0,[z91,z2,z21,z4,z92,z6]),(0,[z105,z7,z21,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z918]),(0,[z919,z2,z21,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z250]),(0,[z656,z7,z1,z16,z5,z6])]],
   [[(0,[z1,z2,z25,z4,z5,z387]),(0,[z920,z7,z2,z4,z5,z6]),(0,[z191,z105,z7,z2,z4,z5]),(0,[z12,z347,z119,z2,z4,z5]),(0,[z285,z2,z4,z5,z50,z6]),(0,[z196,z374,z2,z4,z5,z6]),(0,[z7,z332,z2,z46,z5,z6]),(0,[z7,z374,z2,z4,z197,z6])],[(0,[z13,z2,z4,z58,z5,z6]),(1,[z1,z2,z4,z5,z765]),(0,[z7,z72,z2,z4,z115,z6]),(0,[z7,z205,z2,z4,z5,z43])],[(1,[z1,z2,z4,z768,z6])],[(0,[z104,z1,z921,z4,z5,z6]),(0,[z0,z1,z2,z4,z543,z6]),(0,[z12,z7,z2,z4,z922,z6]),(0,[z12,z7,z2,z71,z5,z43]),(0,[z7,z56,z60,z5,z50,z6]),(0,[z7,z183,z119,z4,z5,z26]),(0,[z923,z1,z2,z4,z5,z6])],[(0,[z924,z7,z1,z2,z4,z5]),(0,[z7,z925,z2,z4,z5,z6]),(0,[z2,z25,z4,z5,z178,z6]),(0,[z7,z926,z2,z4,z5,z6]),(0,[z7,z2,z21,z4,z5,z112]),(0,[z191,z7,z2,z254,z4,z5]),(0,[z7,z2,z4,z5,z50,z633])],[(0,[z12,z2,z319,z25,z4,z5]),(0,[z1,z2,z25,z4,z927,z6]),(0,[z7,z1,z2,z928,z5,z6]),(0,[z1,z2,z4,z5,z929,z6]),(0,[z7,z72,z172,z4,z5,z6])],[(0,[z7,z1,z2,z4,z930,z6]),(0,[z0,z25,z21,z4,z5,z6]),(0,[z931,z1,z2,z4,z5,z6]),(0,[z7,z2,z248,z4,z5,z50]),(0,[z12,z7,z2,z308,z4,z208])],[(0,[z7,z1,z2,z5,z6,z825]),(0,[z1,z2,z932,z4,z5,z6]),(0,[z933,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z128,z723,z6])],[(0,[z7,z2,z21,z4,z356,z6]),(0,[z7,z1,z2,z910,z5,z6])],[(0,[z191,z934,z7,z2,z4,z5]),(0,[z7,z211,z21,z4,z5,z6]),(0,[z331,z348,z2,z4,z5,z6]),(0,[z7,z935,z2,z4,z5,z6]),(0,[z936,z1,z2,z4,z5,z6])],[],[(0,[z7,z937,z2,z4,z5,z6]),(0,[z1,z2,z921,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z112])],[(0,[z7,z1,z938,z4,z5,z6]),(0,[z0,z1,z921,z4,z5,z6])],[(0,[z37,z99,z2,z4,z5,z6]),(0,[z89,z2,z443,z4,z5,z6]),(0,[z0,z1,z207,z4,z5,z6]),(0,[z7,z939,z2,z4,z5,z6]),(0,[z1,z2,z4,z940,z5,z6]),(0,[z12,z7,z2,z46,z5,z6]),(0,[z1,z2,z837,z4,z5,z6]),(0,[z941,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z619,z127]),(0,[z1,z2,z942,z4,z5,z6])],[(0,[z66,z2,z25,z4,z5,z6]),(0,[z7,z1,z2,z129,z668,z6]),(0,[z7,z1,z2,z4,z5,z943]),(0,[z12,z7,z2,z16,z5,z43]),(0,[z12,z339,z2,z4,z5,z43]),(0,[z7,z2,z4,z5,z50,z411]),(0,[z944,z1,z2,z4,z5,z6])],[(0,[z237,z2,z25,z4,z5,z6]),(0,[z0,z1,z311,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z150]),(0,[z0,z1,z2,z4,z356,z6]),(0,[z1,z2,z3,z5,z6,z96]),(0,[z7,z1,z2,z945,z4,z5]),(0,[z7,z1,z2,z674,z28,z6])]],
   [[(0,[z339,z72,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z118,z387]),(0,[z12,z2,z754,z4,z5,z6])],[(0,[z7,z946,z2,z4,z5,z6]),(0,[z7,z1,z2,z947,z5,z6]),(0,[z7,z1,z134,z60,z5,z6]),(0,[z196,z332,z2,z4,z5,z6]),(0,[z7,z332,z2,z4,z197,z6])],[(0,[z7,z2,z948,z4,z5,z6]),(0,[z91,z72,z2,z4,z92,z6]),(0,[z949,z7,z2,z4,z5,z6]),(0,[z7,z2,z950,z4,z5,z6]),(0,[z951,z1,z2,z4,z5,z6]),(0,[z1,z2,z128,z129,z11,z6])],[(0,[z83,z1,z2,z4,z92,z6]),(0,[z952,z7,z2,z4,z5,z6]),(0,[z7,z72,z2,z4,z5,z953]),(0,[z12,z2,z954,z4,z5,z6]),(0,[z2,z97,z4,z5,z50,z6])],[(0,[z955,z1,z2,z4,z5,z6])],[(0,[z7,z2,z4,z5,z6,z156]),(0,[z2,z4,z5,z50,z6,z416]),(0,[z331,z1,z2,z4,z5,z368])],[(0,[z7,z2,z21,z277,z5,z6]),(0,[z191,z7,z2,z129,z4,z5]),(0,[z316,z7,z2,z71,z4,z5])],[(0,[z89,z13,z2,z4,z5,z6]),(0,[z956,z1,z2,z4,z5,z6]),(0,[z12,z91,z2,z4,z92,z6]),(0,[z7,z72,z2,z4,z5,z112]),(0,[z12,z285,z2,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z287]),(0,[z7,z1,z2,z4,z957,z6]),(0,[z35,z7,z1,z4,z725,z6])],[(0,[z7,z958,z2,z4,z5,z6]),(0,[z1,z2,z315,z5,z92,z6]),(0,[z7,z2,z21,z315,z5,z6]),(0,[z959,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z960]),(0,[z12,z55,z2,z4,z5,z111]),(0,[z105,z274,z21,z4,z5,z6]),(0,[z191,z7,z2,z4,z5,z127]),(0,[z7,z72,z309,z4,z5,z6]),(0,[z7,z961,z2,z4,z5,z6]),(0,[z114,z7,z16,z5,z50,z6]),(0,[z962,z1,z2,z4,z5,z6])],[(0,[z114,z0,z1,z16,z5,z6]),(0,[z72,z2,z272,z4,z5,z6]),(0,[z218,z12,z7,z2,z4,z5]),(0,[z963,z1,z2,z4,z5,z6]),(0,[z12,z7,z2,z964,z5,z6]),(0,[z7,z1,z2,z868,z4,z5])],[(0,[z7,z72,z2,z4,z356,z6]),(0,[z2,z965,z4,z5,z50,z6])],[(0,[z502,z2,z25,z4,z5,z6]),(0,[z7,z72,z2,z966,z4,z5]),(0,[z7,z36,z439,z4,z5,z6]),(0,[z12,z122,z2,z4,z5,z6]),(0,[z122,z32,z2,z4,z5,z6])],[(0,[z967,z7,z1,z2,z4,z6]),(0,[z0,z1,z2,z277,z5,z6])],[(0,[z2,z25,z362,z21,z4,z5]),(0,[z1,z2,z968,z4,z5,z6]),(0,[z7,z1,z2,z4,z455,z6]),(0,[z12,z7,z2,z4,z197,z6]),(0,[z86,z7,z2,z435,z4,z6])],[(0,[z7,z181,z2,z4,z5,z50]),(0,[z1,z2,z4,z5,z6,z969]),(0,[z0,z1,z2,z315,z5,z6]),(0,[z970,z1,z2,z4,z5,z6]),(0,[z35,z285,z1,z4,z62,z6]),(0,[z7,z1,z2,z137,z52,z6])]],
   [[(0,[z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z769,z4,z6]),(0,[z1,z2,z4,z5,z111,z765]),(0,[z2,z21,z4,z5,z929,z6]),(0,[z7,z56,z439,z4,z5,z6]),(0,[z971,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z268,z5,z43])],[(0,[z12,z7,z2,z4,z5,z75]),(0,[z1,z25,z94,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z972]),(0,[z39,z12,z196,z2,z4,z5]),(0,[z813,z7,z2,z107,z4,z5])],[(0,[z7,z1,z2,z4,z973,z6]),(0,[z7,z1,z2,z4,z5,z806]),(0,[z7,z1,z2,z4,z5,z974]),(0,[z285,z1,z2,z277,z5,z6])],[(0,[z191,z37,z7,z2,z4,z5]),(0,[z0,z349,z2,z4,z336,z6]),(0,[z191,z7,z2,z21,z4,z5]),(0,[z7,z2,z4,z5,z178,z6]),(0,[z975,z191,z7,z2,z4,z5]),(0,[z7,z2,z137,z5,z50,z6]),(0,[z7,z1,z2,z4,z976,z6]),(0,[z977,z7,z2,z4,z5,z6])],[(0,[z1,z2,z4,z978,z5,z6])],[(0,[z1,z2,z315,z173,z5,z6]),(0,[z12,z2,z11,z4,z5,z6])],[(0,[z7,z1,z2,z794,z4,z6]),(0,[z7,z1,z2,z4,z979,z6]),(0,[z7,z980,z2,z4,z5,z6]),(0,[z981,z1,z2,z4,z5,z6]),(0,[z7,z21,z4,z5,z131,z6]),(0,[z12,z7,z2,z4,z5,z310]),(0,[z39,z7,z1,z4,z356,z145])],[(0,[z7,z1,z2,z4,z5,z880]),(0,[z191,z204,z7,z2,z4,z5]),(0,[z7,z1,z2,z782,z4,z6]),(0,[z175,z7,z439,z4,z5,z6]),(0,[z7,z237,z2,z4,z5,z127])],[(0,[z236,z1,z2,z4,z5,z6]),(0,[z7,z72,z334,z4,z5,z6]),(0,[z12,z7,z2,z4,z52,z127]),(0,[z7,z2,z4,z5,z982,z6]),(0,[z7,z983,z2,z4,z5,z6])],[(0,[z191,z0,z7,z2,z4,z5]),(0,[z7,z2,z5,z200,z50,z6]),(0,[z7,z72,z2,z277,z5,z6]),(0,[z7,z119,z2,z439,z4,z5])],[(0,[z588,z2,z432,z4,z5,z6]),(0,[z7,z2,z984,z4,z5,z6]),(0,[z1,z2,z4,z5,z985,z6]),(0,[z7,z1,z2,z986,z5,z6]),(0,[z987,z7,z2,z4,z5,z6])],[(0,[z7,z2,z4,z5,z50,z6]),(0,[z7,z988,z2,z4,z5,z6]),(0,[z91,z2,z4,z92,z50,z6]),(0,[z7,z72,z2,z315,z5,z6]),(0,[z7,z1,z341,z4,z52,z6]),(0,[z39,z7,z1,z4,z5,z803]),(0,[z7,z1,z2,z733,z5,z43])],[(0,[z1,z580,z25,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z989])],[(0,[z1,z584,z25,z4,z5,z6]),(0,[z7,z21,z4,z5,z144,z6]),(0,[z990,z1,z2,z4,z5,z6]),(0,[z656,z12,z7,z2,z4,z5]),(0,[z991,z1,z2,z4,z5,z6])],[(0,[z91,z1,z2,z4,z520,z6])],[(0,[z1,z2,z992,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z993]),(0,[z994,z1,z2,z4,z5,z6]),(0,[z39,z12,z7,z2,z90,z5]),(0,[z114,z342,z1,z16,z5,z6])]],
   [[(0,[z7,z1,z2,z995,z5,z6]),(0,[z33,z1,z2,z668,z5,z6])],[(0,[z996,z7,z2,z4,z5,z6]),(0,[z924,z7,z2,z21,z4,z5]),(0,[z7,z349,z2,z4,z336,z460])],[(0,[z72,z2,z4,z940,z5,z6])],[(0,[z343,z7,z2,z4,z109,z6]),(0,[z214,z7,z2,z379,z5,z6]),(0,[z236,z2,z4,z5,z50,z6]),(0,[z7,z1,z2,z4,z543,z6]),(0,[z7,z2,z4,z5,z997,z6])],[(0,[z91,z1,z2,z4,z528,z6]),(0,[z998,z7,z2,z4,z5,z6]),(0,[z12,z7,z2,z45,z4,z5]),(0,[z7,z999,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z1000,z6]),(0,[z1001,z1,z2,z4,z5,z6])],[(0,[z1,z25,z4,z141,z5,z6]),(0,[z0,z100,z324,z4,z5,z6]),(0,[z2,z284,z4,z5,z50,z6]),(0,[z7,z2,z439,z308,z4,z5]),(0,[z114,z7,z1,z16,z5,z368]),(0,[z196,z1,z2,z90,z5,z6]),(0,[z7,z1,z2,z90,z197,z6]),(0,[z1,z2,z4,z5,z6,z1002])],[(0,[z7,z2,z21,z41,z4,z5]),(0,[z7,z119,z4,z5,z178,z26]),(0,[z7,z1,z2,z4,z1003,z6]),(0,[z1,z2,z4,z5,z1004,z6])],[(0,[z1,z2,z4,z5,z111,z618]),(0,[z39,z7,z21,z4,z5,z145]),(0,[z12,z7,z2,z308,z4,z5])],[(0,[z7,z1,z2,z4,z1005,z6]),(0,[z1,z2,z25,z4,z5,z368]),(0,[z1,z2,z272,z4,z5,z6]),(0,[z1,z2,z1006,z4,z5,z6]),(0,[z7,z1,z4,z725,z62,z6])],[(0,[z39,z12,z7,z2,z4,z356])],[(0,[z0,z2,z4,z5,z6,z29]),(0,[z1,z2,z4,z38,z768,z6])],[(0,[z191,z2,z25,z21,z4,z5]),(0,[z296,z2,z25,z4,z109,z6]),(0,[z1,z271,z25,z4,z5,z6]),(0,[z7,z1,z2,z4,z1007,z6]),(0,[z199,z7,z2,z71,z4,z5]),(1,[z7,z2,z910,z5,z6]),(0,[z7,z1008,z2,z4,z5,z6])],[(0,[z7,z386,z21,z4,z5,z6]),(0,[z2,z21,z4,z1009,z5,z6]),(0,[z7,z2,z910,z15,z5,z6]),(0,[z7,z1,z1010,z4,z5,z6]),(0,[z12,z196,z2,z4,z5,z6]),(0,[z7,z434,z2,z4,z5,z299]),(0,[z7,z1,z4,z52,z725,z6])],[(0,[z7,z1,z2,z1011,z5,z6]),(0,[z12,z104,z25,z4,z5,z6]),(0,[z0,z1,z2,z41,z4,z5]),(0,[z7,z1,z2,z4,z1012,z6]),(0,[z7,z2,z362,z21,z4,z5]),(0,[z7,z1013,z2,z4,z5,z6]),(0,[z32,z2,z4,z5,z6,z18])],[(0,[z0,z1,z386,z4,z5,z6]),(0,[z1,z2,z1014,z4,z5,z6]),(0,[z1,z2,z4,z5,z768,z6]),(0,[z12,z7,z56,z60,z5,z6]),(0,[z1015,z7,z2,z4,z5,z6]),(0,[z1016,z1,z2,z4,z5,z6]),(0,[z7,z119,z4,z5,z50,z26]),(0,[z7,z1,z2,z1017,z5,z6]),(0,[z155,z1,z2,z128,z129,z6])],[(0,[z7,z1018,z2,z4,z5,z6]),(0,[z104,z25,z4,z5,z50,z6]),(0,[z7,z826,z2,z4,z5,z6]),(0,[z339,z2,z4,z5,z50,z6]),(0,[z7,z2,z4,z5,z1019,z6]),(0,[z7,z434,z2,z4,z5,z411]),(0,[z7,z1,z2,z4,z356,z6])]],
   [[(0,[z7,z396,z21,z4,z5,z6]),(0,[z12,z7,z2,z60,z5,z43]),(0,[z35,z7,z216,z4,z62,z6]),(0,[z7,z1020,z2,z4,z5,z6]),(0,[z7,z2,z1021,z4,z5,z6])],[(0,[z1022,z1,z2,z4,z5,z6]),(0,[z1,z56,z272,z60,z5,z6])],[(0,[z1023,z1,z2,z4,z5,z6]),(0,[z7,z49,z2,z78,z4,z5])],[(0,[z7,z1024,z2,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z352]),(0,[z191,z7,z2,z4,z5,z6]),(0,[z7,z1025,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z299])],[(0,[z7,z1,z2,z1026,z5,z6]),(0,[z7,z1,z2,z4,z5,z1027]),(0,[z7,z2,z21,z726,z4,z5]),(0,[z1,z2,z1028,z4,z5,z6]),(1,[z7,z1,z2,z753,z4])],[(0,[z7,z1029,z2,z4,z5,z6]),(0,[z7,z624,z21,z4,z5,z6]),(0,[z1030,z7,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z411]),(0,[z316,z7,z2,z4,z5,z43])],[(0,[z12,z7,z2,z4,z5,z451]),(0,[z12,z2,z97,z4,z5,z6])],[(0,[z1,z36,z25,z4,z52,z6]),(0,[z1031,z2,z25,z4,z5,z6]),(0,[z1,z2,z25,z4,z67,z127]),(0,[z1032,z7,z2,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z50])],[(0,[z7,z317,z2,z4,z5,z6]),(0,[z191,z7,z2,z44,z4,z5]),(0,[z7,z72,z2,z41,z4,z5]),(0,[z12,z7,z2,z4,z5,z365]),(0,[z12,z7,z2,z523,z4,z5]),(0,[z7,z1033,z2,z4,z5,z6])],[(0,[z7,z1,z2,z1034,z5,z6]),(0,[z7,z2,z4,z5,z6,z1035])],[(0,[z191,z7,z2,z42,z4,z5])],[(0,[z191,z7,z13,z2,z4,z5]),(0,[z1,z2,z1036,z4,z5,z6]),(0,[z7,z2,z4,z5,z1037,z6])],[(0,[z367,z13,z2,z4,z5,z6]),(0,[z0,z2,z78,z4,z5,z6]),(0,[z7,z2,z4,z5,z1038,z6]),(0,[z12,z182,z2,z4,z5,z6]),(0,[z7,z2,z128,z129,z50,z6]),(0,[z1039,z1,z2,z4,z5,z6])],[(0,[z7,z2,z4,z5,z50,z299])],[(0,[z2,z25,z4,z5,z50,z6]),(0,[z12,z2,z25,z308,z4,z5])]],
   [[(0,[z1,z2,z4,z843,z5,z6]),(0,[z7,z2,z4,z5,z50,z714]),(0,[z182,z1,z2,z46,z5,z6])],[(0,[z7,z1040,z2,z4,z5,z6]),(0,[z191,z7,z2,z128,z4,z5]),(0,[z7,z237,z2,z4,z5,z6]),(0,[z1041,z1,z2,z4,z5,z6]),(0,[z51,z7,z237,z2,z308,z4])],[(0,[z121,z1,z2,z388,z5,z6]),(0,[z136,z7,z21,z4,z5,z6]),(0,[z318,z7,z2,z179,z5,z6]),(0,[z342,z348,z2,z4,z5,z6]),(0,[z7,z1042,z2,z4,z5,z6]),(0,[z7,z1,z2,z389,z5,z43])],[(0,[z105,z7,z362,z21,z4,z5]),(0,[z7,z349,z2,z4,z336,z6]),(0,[z7,z36,z107,z4,z52,z6])],[(0,[z1,z2,z25,z5,z720,z6]),(0,[z0,z93,z2,z4,z5,z6]),(0,[z7,z1,z2,z847,z4,z5])],[(0,[z35,z1,z25,z4,z62,z6]),(0,[z7,z2,z1043,z4,z5,z6]),(0,[z1044,z191,z7,z2,z4,z5]),(0,[z7,z1,z2,z4,z5,z1045])],[(0,[z7,z1,z2,z4,z1046,z6]),(0,[z7,z2,z4,z5,z6,z1047]),(0,[z7,z1,z56,z752,z5,z6]),(0,[z7,z2,z4,z5,z6,z1048]),(0,[z1049,z1,z2,z4,z5,z6])],[(0,[z7,z1031,z2,z4,z5,z6]),(0,[z199,z0,z2,z4,z5,z6]),(0,[z39,z7,z1,z4,z197,z145])],[(0,[z7,z2,z4,z115,z50,z6])],[(0,[z1,z2,z500,z4,z38,z6]),(0,[z0,z1,z463,z4,z5,z6]),(0,[z12,z7,z2,z5,z200,z6]),(0,[z122,z2,z21,z4,z5,z6]),(0,[z1,z2,z1050,z4,z5,z6])],[(0,[z191,z7,z36,z2,z4,z5]),(0,[z12,z7,z2,z4,z5,z387]),(0,[z12,z7,z2,z4,z5,z564]),(0,[z296,z2,z4,z154,z109,z6]),(0,[z39,z12,z7,z439,z4,z5])],[(0,[z191,z2,z25,z4,z5,z6]),(0,[z1051,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z1052,z6]),(0,[z7,z1,z2,z4,z5,z1053]),(0,[z12,z7,z2,z4,z1054,z6]),(0,[z12,z7,z2,z71,z4,z5]),(0,[z12,z7,z2,z484,z4,z5]),(0,[z7,z2,z1055,z4,z5,z6]),(1,[z7,z1,z4,z5,z803])],[(0,[z80,z0,z2,z4,z5,z6]),(0,[z7,z434,z2,z4,z5,z6]),(0,[z7,z1,z4,z752,z5,z6])],[(0,[z1,z2,z25,z53,z4,z6]),(0,[z0,z1,z2,z1056,z5,z6]),(0,[z39,z12,z7,z2,z4,z197]),(0,[z1,z2,z1057,z4,z5,z6])],[(0,[z124,z1,z2,z4,z5,z6]),(0,[z33,z1,z2,z315,z5,z6]),(0,[z342,z1,z2,z4,z5,z368]),(0,[z7,z2,z4,z5,z6,z1058])],[(0,[z1,z25,z4,z5,z6,z213]),(0,[z51,z0,z1,z2,z308,z4]),(1,[z12,z7,z2,z90,z5]),(0,[z7,z49,z2,z4,z5,z50])]],
   [[(0,[z1059,z7,z1,z2,z4,z6]),(0,[z7,z439,z25,z4,z5,z6]),(0,[z7,z1060,z2,z4,z5,z6]),(0,[z7,z2,z1061,z4,z5,z6]),(0,[z7,z501,z2,z4,z5,z358]),(0,[z114,z7,z72,z16,z5,z6]),(0,[z39,z12,z7,z2,z46,z5]),(0,[z7,z2,z802,z4,z5,z6]),(0,[z1062,z7,z1,z2,z4,z5]),(0,[z7,z1063,z2,z4,z5,z6]),(0,[z39,z7,z374,z4,z5,z145])],[(0,[z0,z1,z413,z4,z5,z6]),(0,[z12,z2,z4,z5,z154,z6]),(0,[z12,z7,z2,z4,z5,z780]),(0,[z182,z1,z2,z4,z197,z6])],[(0,[z37,z1,z2,z53,z4,z6]),(0,[z7,z1,z2,z4,z1064,z6]),(0,[z0,z72,z21,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z400]),(0,[z7,z101,z2,z581,z5,z6])],[(0,[z2,z25,z4,z5,z6,z150]),(0,[z0,z72,z100,z4,z5,z6]),(0,[z420,z7,z2,z4,z227,z6]),(0,[z12,z664,z7,z2,z4,z5]),(0,[z7,z2,z1065,z4,z5,z6])],[(0,[z7,z1,z2,z5,z1066,z6]),(0,[z89,z410,z2,z4,z5,z6]),(0,[z1,z2,z4,z1009,z5,z6])],[(0,[z1,z2,z25,z69,z28,z6]),(0,[z7,z1067,z2,z4,z5,z6]),(0,[z12,z2,z4,z161,z5,z6]),(0,[z12,z7,z1068,z4,z5,z6]),(0,[z7,z348,z2,z4,z5,z368]),(0,[z7,z1069,z2,z4,z5,z6])],[(0,[z317,z2,z25,z4,z5,z6]),(0,[z7,z72,z326,z4,z5,z6]),(0,[z1,z2,z836,z4,z5,z6]),(0,[z7,z1,z2,z834,z5,z6])],[(0,[z191,z7,z2,z4,z5,z26]),(0,[z7,z2,z1070,z5,z50,z6])],[(0,[z7,z1071,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z115,z6])],[(0,[z1,z2,z25,z137,z5,z6]),(0,[z155,z2,z21,z4,z5,z6]),(0,[z7,z259,z2,z14,z5,z6]),(1,[z12,z7,z2,z4,z356]),(0,[z124,z2,z4,z5,z50,z6])],[(0,[z191,z104,z7,z2,z4,z5]),(0,[z1,z2,z453,z3,z5,z6]),(0,[z191,z7,z100,z2,z4,z5]),(0,[z59,z2,z21,z4,z38,z6]),(0,[z32,z7,z2,z4,z5,z6]),(0,[z1062,z7,z2,z4,z5,z6]),(0,[z1072,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z1073]),(0,[z7,z2,z21,z46,z5,z6]),(0,[z7,z1,z2,z883,z5,z6]),(0,[z199,z7,z2,z4,z5,z43]),(0,[z39,z12,z7,z4,z5,z145]),(0,[z1074,z1,z2,z4,z5,z6]),(0,[z155,z1,z2,z5,z28,z6])],[(0,[z7,z72,z56,z60,z5,z6]),(0,[z122,z72,z2,z4,z5,z6]),(0,[z1075,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z41,z4,z5]),(0,[z12,z7,z1076,z4,z5,z6]),(0,[z12,z7,z2,z206,z4,z5]),(0,[z1077,z1,z2,z4,z5,z6]),(0,[z7,z1078,z2,z4,z5,z6])],[(0,[z7,z2,z4,z455,z50,z6]),(0,[z7,z1,z1079,z4,z5,z6]),(0,[z1080,z7,z2,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z444]),(0,[z12,z7,z2,z78,z4,z5]),(0,[z347,z1,z119,z4,z5,z26])],[(0,[z7,z72,z2,z1081,z4,z5]),(0,[z7,z72,z406,z4,z5,z6]),(0,[z1,z2,z1082,z4,z5,z6]),(0,[z7,z349,z2,z524,z4,z336])]],
   [[(0,[z191,z89,z7,z2,z4,z5]),(0,[z1,z2,z25,z90,z5,z6]),(0,[z59,z1,z2,z38,z200,z6]),(0,[z7,z1,z2,z277,z5,z299]),(0,[z1,z2,z1083,z4,z5,z6])],[(0,[z93,z2,z25,z4,z5,z6]),(0,[z274,z2,z21,z4,z5,z6]),(0,[z7,z1,z2,z4,z1084,z6])],[(0,[z0,z1,z2,z46,z5,z6]),(0,[z7,z2,z4,z356,z50,z6]),(0,[z1,z2,z1085,z4,z5,z6])],[(0,[z479,z1,z2,z4,z498,z6]),(0,[z7,z1086,z2,z4,z5,z6]),(0,[z7,z1,z2,z277,z5,z411])],[(0,[z0,z66,z2,z4,z5,z6]),(0,[z33,z2,z3,z5,z50,z6])],[(0,[z316,z0,z2,z4,z5,z6]),(0,[z7,z72,z439,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z503]),(0,[z566,z7,z1,z4,z5,z145])],[(0,[z1087,z7,z2,z4,z5,z6]),(0,[z7,z1088,z2,z4,z5,z6]),(0,[z7,z21,z4,z263,z5,z6]),(0,[z286,z12,z7,z2,z4,z5]),(0,[z7,z2,z42,z5,z50,z43]),(0,[z7,z1,z2,z4,z1089,z6])],[(0,[z12,z0,z2,z4,z5,z6]),(0,[z339,z1,z2,z4,z5,z6]),(0,[z114,z191,z7,z2,z4,z5]),(0,[z7,z1090,z2,z4,z5,z6])],[(0,[z1,z2,z3,z283,z5,z6]),(0,[z59,z1,z2,z4,z498,z6])],[(0,[z7,z1091,z2,z4,z5,z6]),(0,[z91,z1,z2,z4,z92,z6]),(0,[z291,z2,z21,z4,z5,z6]),(0,[z919,z1,z2,z4,z5,z6]),(0,[z12,z7,z2,z4,z594,z5]),(0,[z39,z7,z4,z5,z50,z145]),(0,[z7,z1092,z2,z4,z5,z6])],[(0,[z1,z2,z25,z524,z4,z5]),(0,[z1,z2,z70,z4,z5,z6]),(0,[z191,z7,z2,z1093,z4,z5]),(0,[z7,z21,z4,z268,z5,z6]),(0,[z7,z1,z2,z4,z5,z953]),(0,[z7,z1,z2,z4,z1094,z6]),(0,[z39,z12,z7,z271,z4,z5]),(0,[z7,z2,z1095,z4,z5,z6])],[(0,[z7,z1,z2,z726,z4,z5]),(0,[z13,z2,z386,z4,z5,z6]),(0,[z835,z1,z2,z4,z5,z6]),(0,[z7,z2,z1096,z4,z5,z6])],[(0,[z191,z7,z2,z4,z5,z111]),(0,[z196,z2,z21,z4,z5,z6]),(0,[z7,z2,z21,z4,z197,z6]),(0,[z155,z72,z2,z4,z5,z6]),(0,[z7,z1,z2,z832,z5,z6]),(0,[z199,z7,z119,z4,z5,z26])],[(0,[z7,z1097,z2,z4,z5,z6]),(0,[z59,z72,z2,z4,z38,z6]),(0,[z191,z7,z119,z2,z4,z5]),(0,[z7,z2,z78,z4,z5,z6]),(0,[z39,z12,z7,z2,z4,z5])],[(0,[z7,z72,z2,z46,z5,z6]),(0,[z7,z49,z332,z2,z4,z5]),(0,[z7,z1,z2,z4,z5,z112]),(0,[z9,z2,z57,z4,z5,z6]),(0,[z7,z1,z2,z4,z725,z6])],[(0,[z7,z1,z2,z1098,z4,z6]),(0,[z12,z7,z2,z4,z5,z436]),(0,[z7,z1,z921,z4,z5,z6]),(0,[z35,z0,z1,z4,z62,z6]),(0,[z0,z183,z2,z4,z5,z6]),(0,[z191,z7,z2,z4,z5,z547]),(0,[z7,z2,z21,z1099,z4,z5]),(0,[z12,z7,z485,z2,z4,z5]),(0,[z7,z1,z2,z4,z1100,z6]),(0,[z1101,z1,z2,z4,z5,z6]),(0,[z7,z2,z1102,z4,z5,z6])]],
   [[(0,[z7,z1,z2,z1103,z5,z6]),(0,[z7,z1104,z2,z4,z5,z6]),(0,[z191,z1,z2,z25,z4,z5]),(0,[z585,z1,z25,z4,z5,z6])],[(0,[z191,z7,z2,z4,z426,z5]),(0,[z2,z21,z4,z5,z6,z18])],[(0,[z7,z2,z1105,z4,z5,z6]),(0,[z9,z2,z21,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z150])],[(0,[z1,z2,z319,z4,z5,z198]),(0,[z0,z1,z2,z4,z197,z6]),(0,[z7,z1,z2,z966,z4,z5]),(0,[z7,z1,z2,z4,z115,z112])],[(0,[z1,z659,z25,z4,z5,z6]),(0,[z7,z1106,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z1107]),(0,[z274,z72,z2,z4,z5,z6]),(0,[z12,z7,z2,z660,z4,z5])],[(0,[z7,z1,z2,z4,z5,z1108]),(0,[z7,z1,z2,z4,z5,z1109]),(0,[z7,z1,z2,z4,z1110,z6])],[(0,[z89,z2,z4,z5,z6,z170]),(0,[z7,z1,z2,z1111,z4,z6])],[(0,[z7,z1112,z2,z4,z5,z6]),(0,[z55,z1,z2,z4,z5,z616]),(0,[z12,z7,z2,z464,z4,z5]),(0,[z7,z1113,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z714]),(0,[z7,z1114,z2,z4,z5,z6])],[(0,[z1115,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z890,z5,z6]),(0,[z7,z72,z467,z4,z5,z6]),(0,[z7,z2,z4,z5,z50,z112]),(0,[z7,z434,z2,z277,z5,z6]),(0,[z39,z7,z1,z46,z5,z145])],[(0,[z1116,z1,z2,z4,z5,z6])],[(0,[z0,z25,z4,z5,z50,z6]),(0,[z0,z2,z4,z5,z118,z6]),(0,[z7,z487,z21,z4,z5,z6]),(0,[z72,z2,z4,z5,z6,z18]),(0,[z12,z7,z2,z4,z5,z43]),(0,[z7,z1117,z2,z4,z5,z6])],[(0,[z996,z2,z25,z4,z5,z6]),(0,[z7,z2,z1118,z4,z5,z6]),(0,[z7,z1,z2,z1119,z5,z6]),(0,[z7,z1,z2,z796,z5,z6]),(0,[z291,z72,z2,z4,z5,z6]),(0,[z12,z342,z2,z4,z5,z6]),(0,[z7,z1120,z2,z4,z5,z6]),(0,[z1121,z7,z2,z4,z5,z6])],[(0,[z7,z1122,z2,z4,z5,z6]),(0,[z1059,z7,z2,z21,z4,z6]),(0,[z1,z119,z70,z4,z5,z26])],[(0,[z924,z1,z2,z25,z4,z5]),(0,[z2,z25,z4,z5,z6,z29]),(0,[z0,z209,z2,z4,z5,z6]),(0,[z0,z205,z2,z4,z5,z6]),(0,[z191,z7,z56,z2,z4,z5]),(0,[z12,z7,z2,z362,z4,z5]),(0,[z12,z7,z2,z4,z5,z457]),(0,[z1123,z7,z2,z4,z5,z6])],[(0,[z7,z2,z1124,z4,z5,z6]),(0,[z7,z1125,z2,z4,z5,z6]),(0,[z196,z72,z2,z4,z5,z6]),(0,[z7,z72,z2,z4,z197,z6]),(0,[z7,z1,z511,z60,z5,z6]),(0,[z1,z2,z1126,z4,z5,z6])]],
   [[(0,[z12,z0,z2,z4,z5,z127]),(0,[z7,z1127,z2,z4,z5,z6]),(0,[z7,z2,z1128,z4,z5,z6]),(0,[z1129,z1,z2,z4,z5,z6]),(0,[z7,z2,z576,z4,z336,z6]),(0,[z1,z2,z1130,z4,z5,z6]),(0,[z7,z1,z2,z277,z5,z6]),(0,[z7,z119,z78,z4,z5,z26]),(0,[z1131,z1,z2,z4,z5,z6])],[(0,[z214,z7,z2,z910,z5,z6]),(0,[z1,z2,z4,z1132,z5,z6]),(0,[z7,z1,z2,z4,z543,z112]),(0,[z209,z2,z272,z4,z5,z6])],[(0,[z7,z1,z2,z315,z5,z6]),(0,[z7,z72,z21,z4,z5,z6]),(0,[z1133,z1,z2,z4,z5,z6]),(0,[z1134,z1,z2,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z368])],[(0,[z191,z105,z7,z21,z4,z5])],[(0,[z606,z1,z25,z4,z5,z6]),(0,[z0,z1,z2,z5,z1135,z6]),(0,[z7,z1136,z2,z4,z5,z6]),(0,[z331,z2,z21,z4,z5,z6]),(0,[z1,z2,z1137,z4,z5,z6])],[(0,[z148,z99,z2,z4,z5,z6]),(0,[z191,z7,z2,z4,z110,z5]),(0,[z7,z1,z2,z1138,z5,z6]),(0,[z9,z72,z2,z4,z5,z6])],[(0,[z229,z2,z21,z4,z5,z6]),(0,[z1,z1139,z2,z4,z5,z6])],[],[(1,[z1,z921,z4,z5,z6]),(0,[z20,z2,z110,z5,z50,z6]),(0,[z12,z7,z2,z4,z5,z158]),(0,[z7,z2,z4,z5,z1140,z6])],[(0,[z104,z152,z25,z4,z5,z6]),(0,[z1,z2,z1141,z4,z5,z6])],[(0,[z191,z7,z2,z25,z4,z5]),(0,[z7,z509,z21,z4,z5,z6]),(0,[z7,z1142,z2,z4,z5,z6])],[(0,[z7,z1143,z2,z4,z5,z6]),(0,[z122,z2,z4,z5,z50,z6])],[(0,[z7,z1,z2,z1144,z5,z6]),(0,[z204,z0,z1,z2,z71,z5]),(0,[z7,z2,z439,z71,z4,z5]),(0,[z7,z2,z4,z5,z1145,z6]),(0,[z204,z7,z205,z2,z71,z5])],[(0,[z1146,z1,z2,z4,z5,z6])],[(0,[z1,z2,z25,z42,z5,z43]),(0,[z1147,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1148])],[(0,[z59,z1,z2,z4,z166,z6]),(0,[z72,z2,z70,z4,z5,z6]),(0,[z7,z1,z2,z723,z69,z6])]],
   [[(0,[z155,z1,z2,z4,z5,z6]),(0,[z191,z7,z2,z4,z16,z5]),(0,[z596,z186,z2,z4,z5,z6]),(0,[z114,z7,z1,z752,z5,z6]),(0,[z1149,z1,z2,z4,z5,z6])],[(0,[z2,z25,z78,z4,z5,z6]),(0,[z59,z1,z2,z4,z38,z6]),(0,[z7,z1,z2,z1150,z5,z6])],[(0,[z54,z1,z2,z315,z5,z6]),(0,[z7,z2,z41,z4,z5,z50]),(0,[z7,z1,z2,z46,z5,z6]),(0,[z7,z1,z2,z733,z42,z5])],[(0,[z12,z2,z25,z4,z5,z50]),(0,[z0,z1,z56,z60,z5,z6]),(0,[z12,z7,z2,z4,z5,z558]),(0,[z12,z7,z1151,z4,z5,z6])],[(0,[z2,z25,z1152,z4,z5,z6])],[(0,[z7,z2,z4,z5,z392,z50]),(0,[z0,z100,z21,z4,z5,z6]),(0,[z7,z1153,z2,z4,z5,z6]),(0,[z1154,z1,z2,z4,z5,z6]),(0,[z2,z173,z4,z5,z50,z6]),(0,[z7,z1,z2,z4,z1155,z6]),(0,[z7,z1,z2,z723,z4,z6])],[(0,[z1,z2,z1156,z4,z5,z6]),(0,[z259,z2,z25,z14,z5,z6]),(0,[z7,z2,z203,z5,z6,z64]),(0,[z7,z1,z2,z4,z356,z26])],[(0,[z12,z119,z2,z25,z4,z5]),(0,[z191,z588,z7,z2,z4,z5]),(0,[z7,z2,z4,z5,z358,z145]),(0,[z331,z72,z2,z4,z5,z6])],[(0,[z1157,z1,z2,z4,z5,z6])],[(0,[z1,z25,z4,z5,z6,z329]),(0,[z1,z2,z4,z5,z6,z18]),(0,[z229,z72,z2,z4,z5,z6]),(0,[z191,z214,z7,z2,z4,z5]),(0,[z220,z7,z1,z16,z5,z6])],[(0,[z1158,z7,z1,z2,z5,z6]),(0,[z214,z0,z2,z15,z5,z6]),(0,[z7,z2,z4,z5,z6,z1159]),(0,[z33,z1,z2,z5,z166,z6]),(0,[z7,z2,z576,z4,z426,z6]),(0,[z7,z2,z1160,z4,z5,z6]),(0,[z191,z7,z2,z4,z336,z5]),(0,[z12,z2,z272,z4,z5,z6]),(0,[z12,z7,z332,z2,z4,z5]),(0,[z7,z1,z2,z16,z5,z368]),(0,[z7,z2,z4,z67,z310,z127])],[(0,[z12,z273,z2,z25,z4,z5]),(0,[z7,z2,z21,z887,z5,z6]),(0,[z1161,z72,z2,z4,z5,z6]),(0,[z7,z1,z2,z1162,z5,z6]),(0,[z7,z2,z4,z5,z1163,z6]),(0,[z155,z2,z4,z5,z50,z6]),(0,[z1,z2,z1164,z4,z5,z6])],[(0,[z13,z1,z2,z53,z4,z6]),(0,[z72,z76,z25,z4,z5,z6]),(0,[z7,z374,z2,z90,z5,z6])],[(0,[z7,z2,z4,z5,z6,z29]),(0,[z1,z2,z4,z38,z445,z6]),(0,[z1,z921,z25,z4,z5,z6]),(0,[z12,z7,z2,z10,z4,z5]),(0,[z1165,z1,z2,z4,z5,z6])],[(0,[z7,z1166,z2,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z616]),(0,[z7,z2,z4,z5,z50,z269])],[(0,[z7,z1,z2,z964,z5,z6]),(0,[z7,z183,z2,z4,z5,z6]),(0,[z7,z21,z4,z5,z249,z6]),(0,[z7,z2,z21,z4,z1167,z5]),(0,[z1168,z1,z2,z4,z5,z6]),(0,[z7,z1,z119,z4,z5,z803]),(0,[z1169,z1,z2,z4,z5,z6])]],
   [[(0,[z7,z711,z2,z4,z5,z6]),(0,[z0,z317,z100,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z188]),(0,[z1154,z2,z4,z5,z50,z6])],[(0,[z1170,z1,z2,z4,z5,z6]),(0,[z1171,z1,z2,z4,z5,z6]),(1,[z7,z1,z2,z733,z5])],[(0,[z12,z7,z2,z635,z4,z5]),(0,[z7,z2,z46,z5,z50,z6]),(0,[z1172,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z197,z6])],[(0,[z191,z7,z99,z2,z4,z5]),(0,[z1,z2,z500,z4,z85,z6]),(0,[z54,z1,z2,z4,z5,z167]),(0,[z1,z2,z1173,z4,z5,z6])],[(0,[z1062,z7,z56,z2,z4,z5])],[(0,[z12,z2,z25,z71,z4,z5]),(0,[z0,z1,z2,z1174,z5,z6])],[(0,[z7,z1,z2,z1175,z5,z6]),(0,[z1,z2,z25,z871,z5,z6]),(0,[z12,z7,z2,z53,z4,z6]),(0,[z7,z2,z21,z5,z200,z6]),(0,[z664,z7,z21,z4,z5,z6]),(0,[z12,z7,z2,z4,z408,z5])],[(0,[z185,z2,z25,z4,z5,z6]),(0,[z7,z100,z439,z4,z5,z6]),(0,[z7,z2,z21,z4,z5,z387]),(0,[z39,z196,z1,z4,z5,z145])],[(0,[z9,z1,z2,z4,z5,z6]),(0,[z191,z7,z2,z4,z1176,z5]),(0,[z7,z2,z4,z5,z1177,z6]),(0,[z7,z1178,z2,z4,z5,z6])],[(0,[z596,z99,z2,z4,z5,z6]),(0,[z348,z2,z25,z4,z5,z6]),(0,[z12,z2,z4,z5,z416,z43]),(0,[z7,z237,z2,z308,z4,z5])],[(0,[z13,z2,z4,z5,z378,z6]),(0,[z345,z7,z2,z15,z5,z6]),(0,[z1179,z1,z2,z4,z5,z6]),(1,[z7,z2,z4,z5,z714]),(0,[z813,z7,z1,z2,z4,z5])],[(1,[z439,z25,z4,z5,z6]),(0,[z7,z72,z2,z362,z4,z5]),(0,[z1,z2,z4,z5,z1180,z6])],[(0,[z191,z7,z2,z4,z5,z92]),(0,[z7,z2,z1181,z4,z5,z6]),(0,[z12,z7,z320,z2,z4,z5]),(0,[z220,z7,z1,z4,z62,z6]),(0,[z7,z1182,z2,z4,z5,z6]),(0,[z1183,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z5,z200,z6]),(0,[z7,z209,z2,z4,z5,z6])],[(0,[z1184,z1,z2,z4,z5,z6]),(0,[z12,z7,z2,z69,z28,z6]),(0,[z183,z2,z70,z4,z5,z6])]],
   [[(0,[z47,z191,z7,z2,z4,z5]),(0,[z12,z807,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z780,z127])],[(0,[z91,z1,z2,z4,z672,z6]),(0,[z59,z1,z2,z11,z4,z6]),(0,[z7,z1,z2,z1185,z5,z6])],[(0,[z104,z72,z25,z4,z5,z6]),(0,[z191,z7,z76,z2,z4,z5]),(0,[z12,z7,z2,z4,z5,z515]),(0,[z12,z7,z2,z4,z1186,z6]),(0,[z12,z1134,z2,z4,z5,z6])],[(0,[z7,z2,z1187,z4,z5,z6]),(0,[z7,z2,z1152,z4,z5,z6]),(0,[z12,z7,z2,z137,z5,z6]),(0,[z7,z1188,z2,z4,z5,z6])],[(0,[z12,z120,z2,z4,z5,z6]),(0,[z1189,z1,z2,z4,z5,z6]),(0,[z7,z49,z1,z2,z90,z5]),(0,[z9,z2,z4,z5,z50,z6]),(0,[z7,z1190,z2,z4,z5,z6])],[(0,[z32,z2,z25,z4,z5,z6]),(0,[z7,z2,z1191,z4,z5,z6]),(0,[z35,z7,z72,z4,z62,z6]),(0,[z7,z487,z4,z5,z178,z6]),(0,[z7,z1192,z2,z4,z5,z6]),(0,[z813,z7,z2,z4,z5,z6])],[(0,[z12,z155,z2,z4,z5,z6]),(0,[z1179,z2,z4,z5,z50,z6]),(0,[z1193,z7,z2,z4,z5,z6]),(0,[z7,z1,z2,z733,z4,z5])],[(0,[z1,z2,z25,z903,z4,z6]),(0,[z1194,z191,z7,z2,z4,z5]),(0,[z7,z93,z2,z4,z5,z6]),(0,[z264,z1,z2,z128,z129,z6]),(0,[z7,z1,z2,z308,z753,z4])],[(0,[z330,z2,z25,z4,z5,z6]),(0,[z1195,z1,z2,z4,z5,z6]),(0,[z35,z191,z7,z2,z4,z5]),(0,[z1196,z1,z2,z4,z5,z6])],[(1,[z711,z2,z4,z5,z6]),(0,[z39,z1,z25,z4,z5,z145]),(0,[z0,z1,z2,z4,z1197,z6]),(0,[z1,z2,z4,z5,z1198,z6]),(0,[z0,z2,z107,z4,z5,z6]),(0,[z120,z2,z21,z4,z5,z6]),(0,[z39,z182,z1,z4,z5,z145])],[(0,[z0,z1,z100,z4,z5,z6]),(0,[z7,z72,z2,z5,z200,z6]),(0,[z12,z7,z2,z90,z5,z6]),(0,[z7,z1,z2,z4,z52,z411]),(0,[z390,z7,z1,z2,z308,z4])],[(0,[z0,z72,z25,z4,z5,z6]),(0,[z0,z1,z2,z4,z1199,z6]),(0,[z7,z72,z2,z4,z5,z387]),(0,[z7,z259,z2,z41,z14,z5]),(0,[z12,z7,z2,z758,z5,z6]),(0,[z35,z7,z1,z137,z62,z6])],[(0,[z1,z2,z25,z4,z5,z460]),(0,[z7,z21,z4,z5,z6,z395]),(0,[z1200,z1,z2,z4,z5,z6]),(0,[z7,z2,z439,z4,z5,z43]),(0,[z409,z2,z4,z5,z6,z170]),(0,[z7,z93,z2,z4,z115,z6]),(0,[z7,z1201,z2,z4,z5,z6]),(0,[z1202,z1,z2,z4,z5,z6]),(0,[z7,z1203,z2,z4,z5,z6])],[(0,[z7,z1204,z2,z4,z5,z6]),(0,[z1,z2,z3,z843,z5,z6]),(0,[z12,z7,z2,z4,z5,z64]),(0,[z7,z2,z4,z5,z6,z1205]),(0,[z339,z80,z2,z4,z5,z6])],[(0,[z374,z2,z25,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1206]),(0,[z1207,z1,z2,z4,z5,z6])],[(0,[z1,z2,z25,z128,z129,z6]),(0,[z7,z1,z2,z647,z28,z6]),(0,[z1,z2,z4,z5,z1208,z6]),(0,[z7,z2,z1209,z4,z5,z6])]],
   [[(0,[z7,z1,z2,z1056,z5,z6]),(0,[z7,z2,z1210,z4,z5,z6])],[(0,[z191,z7,z2,z4,z5,z1211]),(0,[z7,z1,z2,z4,z194,z127]),(0,[z7,z1,z2,z4,z1212,z6]),(0,[z566,z7,z1,z4,z62,z6])],[(0,[z59,z1,z2,z53,z4,z6]),(0,[z1213,z191,z7,z2,z4,z5])],[(0,[z0,z1,z232,z4,z5,z6]),(0,[z122,z1,z2,z4,z5,z6]),(0,[z54,z2,z4,z5,z29,z73]),(0,[z191,z7,z2,z4,z1214,z5]),(0,[z7,z1,z2,z4,z5,z1215]),(0,[z7,z1,z56,z60,z5,z6])],[(0,[z1216,z1,z2,z4,z5,z6]),(0,[z296,z7,z2,z4,z208,z6]),(0,[z12,z7,z2,z524,z4,z5])],[(0,[z12,z7,z2,z319,z4,z5]),(0,[z7,z1,z2,z1217,z5,z6]),(0,[z1218,z1,z2,z4,z5,z6]),(0,[z7,z72,z381,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z724])],[(0,[z1219,z7,z2,z4,z5,z6]),(0,[z20,z2,z21,z110,z5,z6]),(0,[z7,z2,z1220,z4,z5,z6]),(0,[z7,z1,z2,z1081,z4,z5]),(0,[z12,z7,z2,z689,z4,z5]),(1,[z1062,z7,z2,z4,z5])],[(0,[z0,z1,z2,z4,z1221,z6]),(0,[z1158,z7,z2,z21,z5,z6]),(0,[z7,z1222,z2,z4,z5,z6])],[(0,[z7,z2,z4,z5,z6,z1223]),(0,[z229,z2,z4,z5,z50,z6]),(0,[z12,z7,z2,z4,z90,z5]),(0,[z182,z374,z2,z4,z5,z6]),(0,[z7,z1,z4,z5,z803,z145])],[(0,[z191,z7,z2,z4,z5,z178]),(0,[z12,z7,z2,z4,z1224,z6])],[(0,[z2,z25,z107,z4,z5,z6]),(0,[z1,z2,z4,z1225,z5,z6]),(0,[z7,z93,z2,z4,z543,z6])],[(0,[z1,z2,z1226,z4,z5,z6]),(0,[z7,z1,z2,z4,z922,z6]),(0,[z12,z7,z2,z4,z238,z5]),(0,[z732,z7,z2,z4,z5,z368])],[(0,[z120,z72,z2,z4,z5,z6]),(0,[z967,z7,z2,z4,z50,z6]),(0,[z7,z1,z2,z60,z5,z368]),(0,[z264,z1,z2,z129,z4,z6]),(0,[z7,z1227,z2,z4,z5,z6])],[(0,[z1,z2,z53,z11,z4,z6]),(0,[z342,z2,z21,z4,z5,z6]),(0,[z7,z1,z2,z90,z5,z145]),(0,[z7,z2,z4,z5,z1228,z6]),(0,[z80,z7,z2,z42,z5,z43]),(0,[z7,z1,z2,z4,z131,z127])],[(0,[z1229,z7,z2,z4,z5,z6]),(0,[z12,z54,z2,z4,z5,z73]),(0,[z7,z2,z4,z5,z6,z1230]),(0,[z7,z2,z4,z1231,z50,z6]),(0,[z7,z1232,z2,z4,z5,z6]),(0,[z7,z1233,z2,z4,z5,z6])],[(0,[z2,z25,z4,z5,z118,z6]),(0,[z39,z7,z439,z4,z5,z6]),(0,[z12,z7,z119,z4,z5,z26])]],
   [[(0,[z199,z191,z7,z2,z4,z5]),(0,[z12,z7,z2,z162,z4,z5]),(0,[z51,z7,z1,z2,z10,z4]),(0,[z7,z1,z2,z658,z5,z43])],[(0,[z12,z59,z2,z4,z38,z6]),(0,[z59,z7,z1,z2,z200,z6]),(0,[z72,z2,z4,z5,z1180,z6]),(0,[z12,z7,z355,z2,z4,z5]),(0,[z2,z97,z107,z4,z5,z6]),(0,[z7,z1234,z2,z4,z5,z6])],[(0,[z1235,z1,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z1236,z6]),(0,[z204,z7,z72,z2,z71,z5]),(0,[z1,z2,z1237,z4,z5,z6]),(0,[z1238,z1,z2,z4,z5,z6]),(0,[z7,z93,z2,z4,z5,z112]),(0,[z1239,z7,z2,z4,z5,z6])],[(0,[z347,z2,z21,z4,z5,z6]),(0,[z12,z798,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z1240]),(0,[z1241,z1,z2,z4,z5,z6])],[(0,[z0,z1,z508,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z1242])],[(0,[z7,z584,z21,z4,z5,z6]),(1,[z191,z0,z2,z4,z5]),(0,[z12,z7,z2,z4,z67,z127])],[(0,[z104,z1,z25,z4,z5,z6]),(0,[z12,z2,z25,z4,z5,z43]),(0,[z7,z72,z362,z21,z4,z5]),(0,[z7,z2,z4,z543,z50,z6]),(0,[z7,z2,z1243,z4,z5,z6])],[(0,[z7,z66,z2,z4,z5,z6]),(0,[z0,z100,z4,z5,z50,z6]),(0,[z7,z2,z1244,z4,z5,z6])],[(0,[z7,z1079,z21,z4,z5,z6]),(0,[z51,z7,z72,z2,z308,z4]),(0,[z7,z2,z4,z540,z5,z50]),(0,[z7,z2,z524,z4,z5,z50]),(0,[z1,z2,z1245,z4,z5,z6])],[(0,[z651,z7,z1,z2,z28,z6]),(0,[z20,z72,z2,z110,z5,z6]),(0,[z59,z1,z2,z4,z768,z6]),(0,[z55,z1,z2,z4,z5,z765]),(0,[z7,z2,z1246,z4,z50,z6])],[(0,[z588,z99,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z885,z6]),(0,[z1247,z1,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z1248])],[(0,[z274,z1,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z1249,z6]),(0,[z171,z2,z25,z4,z5,z6]),(0,[z0,z348,z2,z4,z5,z6]),(0,[z566,z12,z7,z2,z4,z5]),(0,[z114,z7,z1,z16,z5,z6])],[(0,[z1,z2,z25,z4,z455,z6]),(0,[z54,z502,z2,z4,z5,z73]),(0,[z1250,z1,z2,z4,z5,z6]),(0,[z1,z36,z97,z4,z52,z6])],[(0,[z12,z7,z2,z4,z5,z551])],[(0,[z89,z711,z2,z4,z5,z6]),(0,[z1,z2,z25,z769,z4,z6]),(0,[z7,z1,z2,z1070,z5,z6])],[(0,[z12,z7,z2,z4,z5,z554]),(0,[z191,z7,z2,z308,z4,z5]),(0,[z191,z7,z259,z2,z4,z5]),(0,[z1,z2,z1251,z4,z5,z6]),(0,[z114,z7,z93,z16,z5,z6])]],
   [[(0,[z7,z72,z508,z4,z5,z6]),(0,[z1252,z7,z2,z4,z5,z6]),(0,[z12,z271,z25,z4,z5,z6]),(0,[z502,z0,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z1253,z6]),(0,[z7,z2,z21,z4,z5,z368]),(0,[z342,z72,z2,z4,z5,z6]),(0,[z12,z7,z2,z4,z717,z6]),(0,[z12,z7,z1,z2,z90,z5]),(0,[z7,z1254,z2,z4,z5,z6])],[(0,[z7,z2,z4,z5,z6,z1255]),(0,[z12,z7,z2,z818,z5,z6]),(0,[z39,z12,z182,z2,z4,z5])],[(0,[z119,z25,z21,z4,z5,z6]),(0,[z12,z20,z2,z110,z5,z6]),(0,[z264,z2,z21,z4,z5,z6]),(0,[z12,z7,z721,z4,z5,z6])],[(0,[z291,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z362,z4,z5]),(0,[z39,z0,z1,z4,z5,z145]),(0,[z7,z2,z362,z4,z5,z178]),(0,[z1,z2,z4,z5,z6,z1256])],[(0,[z12,z0,z119,z2,z4,z5]),(0,[z191,z7,z2,z14,z4,z5]),(0,[z12,z7,z2,z435,z4,z5]),(0,[z7,z2,z1185,z5,z50,z6]),(0,[z124,z2,z107,z4,z5,z6])],[(0,[z1,z169,z25,z4,z5,z6]),(0,[z7,z2,z14,z910,z5,z6]),(0,[z7,z1257,z2,z4,z5,z6])],[(0,[z196,z1,z2,z4,z5,z6]),(0,[z7,z1258,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z765]),(0,[z274,z2,z4,z5,z50,z6]),(0,[z7,z2,z1259,z4,z5,z6]),(0,[z345,z7,z2,z106,z5,z6]),(0,[z347,z72,z2,z4,z5,z6])],[(0,[z486,z13,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z368]),(0,[z1,z100,z921,z4,z5,z6])],[(0,[z7,z259,z2,z910,z5,z6]),(0,[z12,z7,z2,z4,z62,z127]),(0,[z12,z7,z2,z42,z5,z43]),(0,[z7,z2,z1260,z4,z5,z6])],[(0,[z7,z1261,z2,z4,z5,z6]),(0,[z7,z2,z21,z4,z5,z1262]),(0,[z7,z2,z107,z4,z5,z6]),(0,[z7,z1,z2,z1099,z4,z5]),(0,[z1,z2,z1263,z4,z5,z6]),(0,[z7,z2,z1264,z5,z50,z6]),(0,[z7,z2,z4,z1094,z50,z6]),(0,[z1,z2,z1265,z4,z5,z6])],[(0,[z0,z374,z2,z4,z5,z6]),(0,[z1266,z7,z2,z4,z5,z6]),(0,[z1267,z1,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z714]),(0,[z12,z7,z1,z2,z4,z356])],[(0,[z12,z0,z2,z4,z5,z167]),(0,[z7,z1,z2,z4,z1199,z6])],[(0,[z7,z2,z4,z5,z1268,z6]),(0,[z1,z439,z25,z4,z5,z6]),(0,[z7,z1,z2,z819,z5,z6]),(0,[z191,z20,z7,z2,z4,z5]),(0,[z7,z2,z1269,z4,z5,z6])],[(0,[z7,z1,z2,z1246,z4,z6]),(0,[z1270,z7,z2,z4,z5,z6]),(0,[z1,z2,z1271,z4,z5,z6]),(0,[z1,z2,z1272,z4,z5,z6])],[(0,[z7,z2,z913,z21,z4,z5]),(0,[z7,z2,z4,z5,z118,z6]),(0,[z291,z2,z4,z5,z50,z6]),(0,[z114,z7,z1,z16,z543,z6]),(0,[z1,z2,z4,z5,z6,z1273]),(0,[z1274,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z1275]),(0,[z1,z2,z1276,z4,z5,z6]),(0,[z7,z2,z4,z5,z865,z6]),(0,[z7,z1,z2,z1277,z5,z6])]],
   [[(0,[z25,z21,z4,z5,z6,z145]),(0,[z1278,z1,z2,z4,z5,z6]),(0,[z7,z36,z21,z4,z52,z6]),(0,[z7,z2,z21,z1279,z4,z6]),(0,[z7,z2,z21,z4,z67,z127]),(0,[z12,z191,z7,z2,z4,z5]),(0,[z191,z7,z2,z4,z5,z50]),(0,[z7,z332,z2,z90,z5,z6])],[(0,[z1,z2,z25,z4,z543,z6]),(0,[z91,z1,z2,z258,z4,z6]),(0,[z191,z54,z7,z2,z4,z5]),(0,[z7,z205,z2,z4,z5,z6]),(0,[z196,z2,z4,z5,z50,z6]),(0,[z7,z216,z2,z137,z5,z6]),(0,[z1280,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z387]),(0,[z7,z2,z1281,z4,z5,z6]),(0,[z54,z2,z21,z4,z5,z73]),(0,[z7,z1,z1076,z4,z5,z6]),(0,[z7,z2,z4,z336,z6,z298])],[(0,[z7,z1282,z2,z4,z5,z6]),(0,[z191,z7,z2,z362,z4,z5]),(0,[z7,z72,z2,z4,z5,z368]),(0,[z7,z2,z4,z865,z109,z6]),(0,[z12,z7,z2,z4,z5,z366])],[(0,[z7,z2,z44,z254,z5,z6]),(0,[z7,z1,z2,z46,z356,z6])],[(0,[z371,z2,z25,z4,z5,z6]),(0,[z1283,z1,z2,z4,z5,z6]),(0,[z20,z1,z2,z843,z5,z6]),(0,[z7,z2,z1284,z4,z5,z6]),(0,[z264,z72,z2,z4,z5,z6])],[(0,[z0,z2,z324,z4,z5,z6]),(0,[z91,z33,z1,z2,z28,z6]),(0,[z7,z1,z2,z4,z1285,z6]),(0,[z1286,z1,z2,z4,z5,z6]),(0,[z12,z7,z2,z308,z4,z227]),(0,[z7,z2,z42,z5,z118,z43])],[(0,[z7,z1,z2,z4,z839,z6]),(0,[z7,z1,z2,z5,z1135,z6]),(0,[z7,z1,z2,z4,z1287,z6]),(0,[z1288,z7,z2,z4,z5,z6]),(0,[z1,z2,z1289,z4,z5,z6]),(0,[z7,z1290,z2,z4,z5,z6])],[(0,[z20,z1,z2,z417,z5,z6]),(0,[z2,z70,z21,z4,z5,z6]),(0,[z1291,z7,z2,z4,z5,z6])],[(0,[z7,z1,z1292,z4,z5,z6]),(0,[z12,z7,z313,z2,z4,z5]),(0,[z7,z2,z1293,z4,z5,z6])],[(0,[z37,z2,z432,z4,z5,z6]),(0,[z1294,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z1295,z5,z6]),(0,[z1296,z1,z2,z4,z5,z6])],[(0,[z12,z2,z25,z4,z5,z188]),(0,[z0,z332,z2,z4,z5,z6]),(0,[z2,z21,z173,z4,z5,z6]),(0,[z7,z2,z4,z415,z6,z298])],[(0,[z191,z7,z2,z69,z4,z5])],[(0,[z20,z1,z2,z110,z5,z6]),(0,[z191,z345,z7,z2,z4,z5]),(0,[z1,z2,z42,z5,z416,z43])],[(0,[z331,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z1297,z4,z6]),(0,[z12,z339,z2,z4,z5,z6]),(0,[z7,z1,z1298,z2,z4,z5])],[(0,[z191,z0,z2,z21,z4,z5]),(0,[z296,z0,z2,z4,z109,z6]),(0,[z1299,z1,z2,z4,z5,z6])]],
   [[(0,[z229,z1,z2,z4,z5,z6]),(0,[z1,z2,z1300,z4,z5,z6]),(0,[z7,z2,z14,z5,z6,z64]),(0,[z7,z1,z119,z309,z4,z5])],[(0,[z1,z2,z25,z4,z5,z299]),(0,[z1,z2,z4,z5,z6,z1301]),(0,[z7,z1,z2,z128,z601,z6]),(0,[z7,z1302,z2,z4,z5,z6]),(0,[z7,z49,z1,z2,z4,z356])],[(0,[z0,z2,z4,z5,z6,z1303]),(0,[z1,z2,z4,z1304,z5,z6]),(0,[z1161,z1,z2,z4,z5,z6]),(0,[z1305,z1,z2,z4,z5,z6]),(0,[z339,z2,z4,z5,z118,z6]),(0,[z1306,z1,z2,z4,z5,z6])],[(0,[z72,z2,z25,z4,z5,z6]),(0,[z0,z1,z546,z4,z5,z6]),(0,[z59,z1,z2,z315,z38,z6]),(0,[z191,z343,z7,z2,z4,z5]),(0,[z191,z7,z2,z71,z4,z5]),(0,[z7,z72,z2,z4,z67,z127]),(0,[z331,z1,z2,z4,z115,z6])],[(0,[z1,z2,z25,z4,z5,z411]),(0,[z7,z439,z4,z5,z26,z6]),(0,[z1307,z7,z2,z4,z5,z6]),(0,[z1,z2,z1308,z4,z5,z6])],[(0,[z0,z1,z624,z4,z5,z6]),(0,[z7,z1,z2,z4,z1309,z6]),(0,[z7,z2,z21,z53,z4,z6]),(0,[z54,z72,z2,z4,z5,z73]),(0,[z72,z2,z173,z4,z5,z6]),(0,[z12,z7,z2,z683,z4,z5]),(0,[z1310,z1,z2,z4,z5,z6]),(0,[z196,z1,z2,z4,z356,z6])],[],[(0,[z1,z221,z25,z4,z5,z6]),(0,[z7,z1311,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z1312,z5]),(0,[z7,z2,z1313,z4,z5,z6])],[(0,[z1,z2,z25,z1034,z5,z6]),(0,[z253,z1,z2,z638,z5,z6])],[(0,[z83,z1,z2,z4,z108,z6]),(0,[z1314,z1,z2,z4,z5,z6]),(0,[z331,z2,z4,z5,z50,z6])],[(0,[z347,z1,z2,z4,z5,z6]),(0,[z12,z7,z2,z4,z789,z6]),(0,[z12,z7,z2,z71,z179,z5]),(0,[z1315,z7,z2,z4,z5,z6])],[(0,[z33,z1,z2,z40,z5,z6]),(0,[z7,z2,z4,z5,z6,z1316]),(0,[z645,z7,z1,z2,z28,z6]),(0,[z1317,z1,z2,z4,z5,z6]),(0,[z7,z2,z1318,z4,z5,z6])],[(0,[z0,z1,z2,z53,z4,z6]),(0,[z12,z7,z36,z4,z52,z6]),(0,[z7,z2,z878,z107,z4,z5]),(0,[z316,z7,z2,z4,z5,z127])],[(0,[z7,z2,z21,z69,z28,z6]),(0,[z7,z2,z4,z5,z310,z460])],[(0,[z1,z2,z4,z1319,z5,z6])],[(0,[z403,z7,z21,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z1320]),(0,[z7,z1,z2,z1321,z5,z6]),(0,[z191,z7,z332,z2,z4,z5]),(0,[z12,z1051,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z1322,z6]),(0,[z813,z7,z36,z2,z4,z5])]],
   [[(0,[z1323,z1,z2,z4,z5,z6])],[(0,[z7,z2,z21,z137,z5,z6]),(0,[z331,z1,z2,z4,z543,z6]),(0,[z1324,z7,z2,z4,z5,z6])],[(0,[z37,z584,z2,z4,z5,z6]),(0,[z7,z634,z21,z4,z5,z6])],[(0,[z7,z2,z4,z5,z6,z1325]),(0,[z12,z0,z2,z308,z4,z5]),(0,[z55,z2,z21,z4,z5,z111]),(0,[z7,z1,z2,z362,z4,z5]),(0,[z1326,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z69,z28,z6]),(0,[z7,z1,z2,z4,z1231,z6]),(0,[z1327,z7,z2,z4,z5,z6])],[(0,[z7,z1,z2,z887,z5,z6]),(0,[z412,z2,z231,z4,z5,z6]),(0,[z191,z0,z1,z2,z4,z5]),(0,[z347,z2,z4,z5,z50,z6]),(0,[z7,z2,z4,z5,z6,z1328])],[(0,[z0,z1,z354,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z460]),(0,[z473,z12,z7,z2,z4,z5]),(0,[z12,z2,z4,z5,z18,z127]),(0,[z1,z2,z1329,z4,z5,z6])],[(0,[z7,z1330,z2,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z618]),(0,[z7,z1331,z2,z4,z5,z6]),(0,[z1332,z7,z2,z4,z5,z6])],[(0,[z0,z1,z2,z137,z5,z6]),(0,[z7,z72,z2,z53,z4,z6]),(0,[z199,z7,z2,z4,z5,z6]),(0,[z7,z2,z21,z90,z5,z6])],[(0,[z7,z1,z2,z1174,z5,z6]),(0,[z264,z1,z2,z4,z5,z6]),(0,[z191,z51,z7,z2,z4,z5]),(0,[z7,z1,z2,z4,z1167,z5]),(0,[z12,z291,z2,z4,z5,z6]),(0,[z12,z7,z2,z128,z129,z6]),(0,[z331,z1,z2,z4,z5,z112]),(0,[z7,z1,z2,z4,z5,z1333])],[(0,[z273,z1,z2,z4,z5,z73]),(0,[z191,z7,z2,z4,z52,z5])],[(0,[z7,z1,z2,z1334,z5,z6]),(0,[z7,z1,z2,z733,z5,z6])],[(0,[z7,z119,z2,z802,z4,z5]),(0,[z182,z332,z2,z4,z5,z6])],[(0,[z1059,z1,z2,z25,z4,z6]),(0,[z80,z7,z2,z4,z5,z6]),(0,[z285,z1,z2,z137,z5,z6])],[(0,[z105,z0,z21,z4,z5,z6]),(0,[z1,z2,z4,z768,z92,z6]),(0,[z7,z49,z2,z4,z5,z118])],[(0,[z20,z1,z2,z461,z5,z6]),(0,[z191,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z90,z5,z6]),(0,[z7,z1,z2,z1335,z5,z6]),(0,[z12,z2,z70,z4,z5,z6]),(0,[z7,z2,z4,z5,z1336,z6])]],
   [[(0,[z1337,z7,z2,z4,z5,z6]),(0,[z486,z2,z443,z4,z5,z6]),(0,[z7,z72,z2,z69,z28,z6]),(0,[z7,z2,z277,z5,z50,z6]),(0,[z39,z7,z332,z4,z5,z145]),(0,[z7,z1,z278,z4,z5,z26])],[(0,[z1,z2,z25,z4,z5,z6]),(0,[z7,z1,z2,z5,z200,z6]),(0,[z35,z7,z4,z62,z50,z6])],[(0,[z0,z1,z25,z4,z5,z6]),(0,[z1,z2,z319,z4,z5,z111]),(0,[z7,z2,z21,z524,z4,z5]),(0,[z7,z1,z2,z4,z5,z387]),(0,[z7,z1,z2,z137,z62,z6]),(0,[z7,z1,z126,z4,z52,z6])],[(0,[z89,z2,z94,z4,z5,z6]),(0,[z1,z2,z173,z4,z5,z6]),(0,[z7,z1,z2,z4,z1054,z6]),(0,[z114,z7,z1,z16,z115,z6]),(0,[z35,z7,z1,z4,z62,z411])],[(0,[z418,z2,z25,z4,z5,z6]),(0,[z7,z72,z2,z137,z5,z6]),(0,[z264,z2,z4,z5,z50,z6])],[(0,[z7,z2,z53,z4,z50,z6]),(0,[z1338,z1,z2,z4,z5,z6]),(0,[z180,z1,z2,z137,z5,z6]),(0,[z7,z1,z2,z46,z197,z6]),(0,[z7,z1339,z2,z4,z5,z6])],[(0,[z1,z2,z25,z4,z115,z6]),(0,[z55,z72,z2,z4,z5,z111])],[(0,[z7,z1,z2,z4,z927,z6])],[(0,[z7,z259,z2,z14,z5,z387])],[(0,[z39,z7,z72,z4,z5,z145])],[(0,[z0,z1,z694,z4,z5,z6]),(0,[z72,z25,z21,z4,z5,z6]),(0,[z1,z56,z25,z60,z5,z6]),(0,[z1340,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z1341]),(0,[z7,z1,z2,z4,z543,z368]),(0,[z7,z1,z2,z4,z5,z1342])],[(0,[z191,z7,z2,z4,z5,z145]),(0,[z7,z72,z2,z90,z5,z6]),(0,[z1343,z1,z2,z4,z5,z6]),(0,[z7,z1344,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z1345,z411])],[(0,[z1,z2,z4,z1346,z5,z6]),(0,[z0,z2,z4,z5,z358,z6]),(0,[z7,z1,z2,z4,z1197,z6])],[(0,[z7,z1,z1068,z4,z5,z6]),(0,[z7,z2,z4,z5,z50,z387]),(0,[z7,z1,z2,z1347,z5,z6])],[(0,[z12,z229,z2,z4,z5,z6]),(0,[z72,z2,z284,z4,z5,z6]),(0,[z7,z2,z4,z5,z1348,z6]),(0,[z7,z1349,z2,z4,z5,z6])],[(0,[z7,z1,z2,z1350,z5,z6]),(0,[z632,z7,z21,z4,z5,z6]),(0,[z1351,z1,z2,z4,z5,z6])]],
   [[(0,[z7,z1,z2,z4,z5,z1352]),(0,[z7,z2,z362,z78,z4,z5])],[(0,[z216,z2,z25,z4,z5,z6]),(0,[z199,z7,z2,z4,z5,z127]),(0,[z7,z1,z2,z4,z5,z1353])],[(0,[z7,z2,z4,z5,z6,z1303]),(0,[z7,z673,z21,z4,z5,z6])],[(0,[z120,z1,z2,z4,z5,z6]),(0,[z191,z7,z2,z4,z5,z43])],[(0,[z1,z119,z25,z4,z5,z26]),(0,[z486,z410,z2,z4,z5,z6]),(0,[z0,z1,z119,z4,z5,z26]),(0,[z1354,z1,z2,z4,z5,z6]),(0,[z214,z2,z161,z15,z5,z6]),(0,[z1355,z7,z2,z4,z5,z6]),(0,[z7,z1,z4,z5,z6,z803])],[(0,[z7,z72,z2,z524,z4,z5]),(0,[z7,z1356,z2,z4,z5,z6])],[(0,[z7,z72,z694,z4,z5,z6]),(0,[z37,z620,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z50,z402]),(0,[z1,z2,z4,z5,z6,z416]),(0,[z12,z7,z2,z4,z455,z6]),(0,[z316,z7,z2,z4,z5,z6]),(0,[z7,z529,z2,z4,z79,z6]),(0,[z7,z1,z2,z4,z865,z6]),(0,[z12,z2,z4,z1132,z5,z6]),(0,[z39,z7,z1,z90,z5,z145]),(0,[z7,z1,z2,z4,z429,z127])],[(0,[z525,z1,z2,z4,z5,z167]),(0,[z7,z2,z524,z4,z5,z109]),(0,[z289,z475,z2,z4,z5,z6]),(0,[z204,z7,z1,z2,z202,z5]),(0,[z7,z1,z4,z5,z725,z6])],[(0,[z2,z21,z11,z4,z5,z6]),(0,[z7,z1357,z2,z4,z5,z6])],[(0,[z33,z1,z2,z843,z5,z6]),(0,[z114,z7,z1,z16,z5,z112]),(0,[z7,z2,z4,z5,z1358,z6])],[(0,[z0,z1,z2,z4,z67,z127]),(0,[z7,z1,z2,z4,z1221,z6]),(0,[z54,z1,z2,z4,z5,z400]),(0,[z7,z2,z21,z816,z5,z6]),(0,[z2,z70,z4,z5,z50,z6]),(0,[z1327,z7,z2,z4,z5,z411])],[(0,[z33,z1,z2,z53,z3,z6]),(0,[z12,z264,z2,z4,z5,z6]),(0,[z7,z2,z1359,z4,z5,z6])],[(0,[z1,z711,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z1360,z6]),(0,[z1,z2,z25,z4,z5,z112]),(0,[z205,z2,z25,z4,z5,z6]),(0,[z1361,z7,z2,z4,z5,z6]),(0,[z91,z1,z2,z11,z4,z6]),(0,[z1,z2,z1362,z4,z5,z6])],[(0,[z7,z1363,z2,z4,z5,z6]),(0,[z191,z7,z2,z2,z4,z5]),(0,[z12,z1147,z2,z4,z5,z6]),(0,[z35,z7,z434,z4,z62,z6])],[(0,[z12,z273,z7,z2,z4,z5]),(0,[z120,z2,z4,z5,z50,z6]),(0,[z12,z7,z2,z4,z312,z5])],[(0,[z7,z1,z2,z4,z1364,z6]),(0,[z214,z7,z2,z113,z5,z6]),(0,[z1,z2,z4,z5,z1365,z6]),(0,[z12,z7,z2,z4,z5,z298])]],
   [[(0,[z1,z2,z25,z4,z356,z6]),(0,[z191,z7,z2,z60,z4,z5]),(0,[z191,z7,z1366,z2,z4,z5]),(0,[z512,z412,z2,z4,z5,z6]),(0,[z7,z72,z119,z4,z5,z26]),(0,[z1,z2,z4,z1367,z5,z6]),(0,[z35,z7,z1,z4,z62,z6]),(0,[z182,z1,z2,z90,z5,z6])],[(0,[z343,z7,z2,z4,z547,z6]),(0,[z1368,z1,z2,z4,z5,z6]),(0,[z1,z2,z1369,z4,z5,z6])],[(0,[z0,z2,z4,z5,z310,z6]),(0,[z72,z2,z11,z4,z5,z6]),(0,[z7,z1,z2,z683,z5,z43]),(0,[z7,z2,z4,z5,z1336,z299]),(0,[z1,z2,z1370,z4,z5,z6])],[(0,[z7,z1,z2,z1371,z4,z5]),(0,[z7,z2,z4,z67,z50,z127]),(0,[z1372,z1,z2,z4,z5,z6])],[(0,[z1,z2,z25,z1111,z4,z6]),(0,[z182,z2,z21,z4,z5,z6]),(0,[z7,z2,z435,z524,z4,z5])],[(0,[z191,z59,z7,z2,z4,z5]),(0,[z830,z2,z21,z4,z5,z6]),(0,[z12,z1310,z2,z4,z5,z6]),(0,[z1373,z1,z2,z4,z5,z6]),(0,[z7,z1374,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z1375])],[(0,[z1,z2,z453,z304,z5,z6]),(0,[z0,z216,z2,z4,z5,z6]),(0,[z7,z2,z21,z42,z5,z43]),(0,[z12,z236,z2,z4,z5,z6]),(0,[z155,z1,z2,z128,z5,z6])],[(0,[z342,z1,z2,z4,z5,z6]),(0,[z39,z12,z0,z2,z4,z5]),(0,[z1,z2,z4,z5,z111,z451]),(0,[z7,z1,z2,z1376,z5,z6]),(0,[z204,z7,z2,z21,z71,z5]),(0,[z1377,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z1186,z6]),(0,[z9,z209,z2,z4,z5,z6]),(0,[z7,z1378,z2,z4,z5,z6])],[(0,[z1379,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z752,z5,z6]),(0,[z7,z2,z4,z5,z1345,z6])],[(0,[z0,z2,z439,z4,z5,z6]),(0,[z1,z2,z965,z4,z5,z6]),(0,[z1380,z1,z2,z4,z5,z6])],[(0,[z91,z1,z2,z4,z242,z6]),(0,[z1,z2,z4,z5,z1381,z6]),(0,[z273,z1,z2,z4,z5,z468]),(0,[z2,z25,z324,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z118]),(0,[z1062,z7,z2,z57,z4,z5]),(1,[z7,z1,z4,z725,z6])],[(0,[z33,z1,z2,z53,z4,z6]),(0,[z191,z7,z2,z432,z4,z5]),(0,[z285,z216,z2,z4,z5,z6])],[(0,[z1,z2,z284,z4,z5,z6]),(0,[z7,z1382,z2,z4,z5,z6]),(0,[z7,z4,z5,z178,z6,z150]),(0,[z1383,z1,z2,z4,z5,z6]),(0,[z1384,z1,z2,z4,z5,z6]),(0,[z12,z1238,z2,z4,z5,z6]),(0,[z342,z1,z2,z4,z115,z6]),(0,[z2,z272,z57,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z1385]),(0,[z0,z1,z2,z42,z5,z43]),(0,[z7,z1,z1386,z4,z5,z6]),(0,[z55,z171,z2,z4,z5,z111]),(0,[z51,z7,z2,z21,z308,z4]),(0,[z7,z2,z362,z4,z5,z50])],[(0,[z1,z2,z25,z277,z5,z6]),(0,[z7,z348,z2,z4,z5,z6]),(0,[z7,z2,z1079,z4,z5,z6]),(0,[z114,z7,z21,z16,z5,z6]),(0,[z12,z2,z4,z5,z6,z18]),(0,[z1,z2,z954,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z1387]),(0,[z1388,z1,z2,z4,z5,z6])],[(0,[z0,z418,z2,z4,z5,z6]),(0,[z191,z7,z2,z4,z5,z109])]],
   [[(0,[z1,z2,z25,z315,z5,z6]),(0,[z1389,z1,z2,z4,z5,z6]),(0,[z2,z272,z21,z4,z5,z6]),(0,[z1373,z2,z4,z5,z50,z6])],[(0,[z7,z1390,z2,z4,z5,z6]),(0,[z2,z21,z4,z5,z6,z416]),(0,[z12,z7,z2,z4,z5,z127]),(0,[z1,z2,z128,z173,z129,z6])],[(0,[z1087,z0,z2,z4,z5,z6]),(0,[z1,z2,z53,z4,z111,z6]),(0,[z7,z1391,z2,z4,z5,z6]),(0,[z12,z274,z2,z4,z5,z6]),(0,[z342,z2,z4,z5,z50,z6])],[(0,[z7,z1,z2,z4,z6,z808]),(0,[z2,z25,z4,z5,z310,z6]),(0,[z7,z2,z4,z5,z1392,z6]),(0,[z7,z348,z2,z4,z115,z6]),(0,[z1393,z1,z2,z4,z5,z6]),(0,[z180,z216,z2,z4,z5,z6]),(0,[z7,z1394,z2,z4,z5,z6])],[(0,[z1395,z1,z2,z4,z5,z6]),(0,[z55,z185,z2,z4,z5,z111]),(0,[z12,z7,z1010,z4,z5,z6])],[(0,[z37,z1,z2,z315,z5,z6]),(0,[z7,z1396,z2,z4,z5,z6])],[(0,[z1397,z7,z2,z4,z5,z6])],[(0,[z182,z72,z2,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z356]),(0,[z1384,z2,z4,z5,z50,z6])],[(0,[z37,z23,z2,z4,z5,z6]),(1,[z191,z2,z25,z4,z5]),(0,[z7,z1,z2,z4,z5,z1398]),(0,[z191,z7,z2,z443,z4,z5]),(0,[z191,z7,z2,z4,z5,z188]),(0,[z1,z2,z1399,z4,z5,z6]),(0,[z7,z2,z4,z336,z865,z6]),(0,[z1400,z1,z2,z4,z5,z6]),(0,[z204,z7,z2,z71,z5,z50]),(0,[z7,z1,z2,z1401,z5,z6]),(0,[z1,z2,z1402,z4,z5,z6])],[(0,[z7,z2,z4,z5,z6,z1403]),(0,[z1404,z7,z2,z4,z5,z6]),(0,[z7,z1405,z2,z4,z5,z6]),(0,[z7,z72,z2,z42,z5,z43])],[(0,[z512,z13,z2,z4,z5,z6]),(0,[z0,z1,z704,z4,z5,z6]),(0,[z33,z2,z21,z3,z5,z6]),(0,[z191,z296,z7,z2,z4,z5]),(0,[z342,z1,z2,z4,z543,z6]),(0,[z7,z1,z2,z4,z5,z368]),(0,[z1406,z7,z2,z4,z5,z6])],[(0,[z191,z7,z72,z2,z4,z5]),(0,[z72,z2,z4,z5,z6,z416]),(0,[z12,z7,z2,z4,z5,z299]),(0,[z1,z2,z1407,z4,z5,z6]),(0,[z7,z2,z1408,z4,z5,z6])],[(0,[z91,z7,z1,z2,z200,z6]),(0,[z12,z7,z487,z2,z4,z5]),(0,[z9,z1,z56,z60,z5,z6]),(0,[z330,z2,z97,z4,z5,z6])],[(0,[z7,z374,z2,z4,z5,z6]),(0,[z191,z7,z2,z439,z4,z5]),(0,[z7,z1409,z2,z4,z5,z6]),(0,[z7,z1,z2,z723,z5,z6]),(0,[z204,z7,z1,z2,z71,z5])],[(0,[z7,z1,z2,z4,z1224,z6]),(0,[z0,z371,z2,z4,z5,z6]),(0,[z7,z1410,z2,z4,z5,z6]),(0,[z1411,z191,z7,z2,z4,z5]),(0,[z12,z7,z2,z4,z5,z411]),(0,[z1412,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z849,z6]),(0,[z735,z7,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z115,z368]),(0,[z1413,z1,z2,z4,z5,z6]),(0,[z2,z4,z5,z310,z6,z18])]],
   [[(0,[z20,z1,z2,z5,z528,z6]),(0,[z1,z2,z11,z4,z5,z6]),(0,[z1414,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z1415,z6]),(0,[z1,z25,z4,z571,z5,z6]),(0,[z12,z7,z2,z65,z4,z5]),(0,[z7,z348,z2,z4,z543,z6]),(0,[z7,z209,z56,z60,z5,z6]),(0,[z1,z2,z1416,z4,z5,z6]),(0,[z1,z2,z1417,z4,z5,z6])],[(0,[z0,z1,z2,z757,z5,z6]),(0,[z0,z2,z57,z4,z5,z6]),(0,[z2,z4,z161,z5,z50,z6]),(0,[z331,z93,z2,z4,z5,z6]),(0,[z342,z1,z2,z4,z5,z112]),(0,[z264,z1,z2,z4,z28,z6])],[(0,[z7,z1,z2,z1418,z5,z6]),(0,[z7,z1,z2,z4,z5,z1262]),(0,[z1419,z1,z2,z4,z5,z6]),(0,[z1420,z7,z2,z4,z5,z6]),(0,[z1421,z1,z2,z4,z5,z6]),(0,[z35,z7,z1,z4,z62,z299]),(0,[z1422,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z723,z28,z6]),(0,[z51,z7,z1,z2,z308,z4]),(0,[z7,z1,z2,z753,z4,z127])],[(0,[z105,z7,z1079,z4,z5,z6]),(0,[z7,z72,z678,z4,z5,z6]),(0,[z7,z1,z119,z4,z5,z26]),(0,[z646,z7,z1,z2,z71,z5])],[(0,[z7,z349,z2,z4,z865,z6]),(0,[z7,z2,z4,z5,z50,z368]),(0,[z7,z1,z2,z4,z5,z1423])],[(0,[z0,z2,z21,z4,z5,z6]),(0,[z183,z2,z25,z4,z5,z6]),(0,[z12,z9,z2,z4,z5,z6]),(0,[z7,z1424,z2,z4,z5,z6])],[(0,[z1158,z1,z2,z25,z5,z6]),(0,[z12,z0,z2,z4,z5,z50]),(0,[z191,z7,z2,z4,z5,z62]),(0,[z12,z7,z938,z4,z5,z6]),(0,[z1425,z7,z2,z4,z5,z6]),(0,[z347,z2,z78,z4,z5,z6])],[(0,[z7,z1426,z2,z4,z5,z6]),(0,[z218,z191,z7,z2,z4,z5]),(0,[z2,z4,z5,z50,z6,z18]),(0,[z1315,z7,z2,z4,z5,z112]),(0,[z196,z1,z2,z46,z5,z6])],[(0,[z7,z2,z324,z4,z5,z6]),(0,[z7,z1,z2,z1264,z5,z6]),(0,[z12,z7,z2,z4,z5,z135]),(1,[z7,z2,z4,z865,z6]),(0,[z12,z7,z2,z4,z5,z688]),(0,[z7,z348,z2,z4,z5,z112])],[(0,[z7,z1,z2,z1279,z4,z6]),(0,[z7,z1,z2,z4,z356,z145]),(0,[z7,z1,z2,z4,z67,z127])],[(0,[z1427,z7,z2,z4,z5,z6]),(0,[z285,z2,z21,z4,z5,z6]),(0,[z214,z7,z2,z15,z5,z6]),(0,[z7,z1,z1151,z4,z5,z6]),(0,[z7,z1,z2,z137,z5,z299]),(0,[z7,z1428,z2,z4,z5,z6])],[(0,[z434,z2,z25,z4,z5,z6]),(0,[z0,z1,z2,z524,z4,z5]),(0,[z7,z1429,z2,z4,z5,z6]),(0,[z54,z1,z2,z4,z5,z73]),(0,[z7,z4,z5,z26,z6,z150])],[(0,[z37,z475,z2,z4,z5,z6]),(0,[z7,z1,z2,z843,z5,z6]),(0,[z33,z72,z2,z3,z5,z6]),(0,[z39,z12,z7,z119,z4,z5]),(0,[z35,z7,z1,z277,z62,z6]),(0,[z7,z1,z2,z1430,z5,z6])],[(0,[z1,z2,z25,z41,z4,z5]),(0,[z7,z332,z2,z4,z5,z6]),(0,[z382,z7,z2,z15,z5,z6]),(0,[z296,z291,z2,z4,z109,z6]),(0,[z7,z439,z4,z5,z62,z6]),(0,[z12,z7,z2,z4,z5,z700]),(0,[z1419,z2,z4,z5,z50,z6]),(0,[z7,z1,z2,z137,z5,z411]),(0,[z1431,z7,z2,z4,z5,z6])],[(0,[z349,z2,z25,z4,z336,z6]),(0,[z20,z1,z2,z173,z5,z6]),(0,[z7,z1,z2,z4,z5,z803])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 483) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 483).take 482) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 965).take 480) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1445).take 123) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1568)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [483, 482, 480, 123] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 90).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 90).take 79).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 169).take 81).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 250).take 92).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 342).take 98).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 440).take 72).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [90, 79, 81, 92, 98, 72] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_nil pcend))))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38963

theorem PEqualNP.Outside.L_meta_38963 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4241018056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4241018056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38963.solve