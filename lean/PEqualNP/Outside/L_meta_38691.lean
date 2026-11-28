import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38691

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
  Nat.testBit (4276808392 * 2 ^ 32 + 4241025224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0011989c71111b15#64 ++ 0x40011989c71111b1#64 ++ 0x3033f9fcf1133f3f#64 ++ 0xa3033f9fcf1133f3#64 : BitVec 256),
   (0x00c4424180664468#64 ++ 0x800c442418066446#64 ++ 0xd1cc4647c1ffc7ff#64 ++ 0x7d1cc4647c1ffc7f#64 : BitVec 256),
   (0x160b85861618a981#64 ++ 0x0160b85861618a98#64 ++ 0xfe0f87873e1cf9ce#64 ++ 0xefe0f87873e1cf9c#64 : BitVec 256),
   (0x2b7007682ba0f60e#64 ++ 0x02b7007682ba0f60#64 ++ 0xfff007f83fe0fe0d#64 ++ 0xffff007f83fe0fe0#64 : BitVec 256),
   (0x4dbee8003ddf0000#64 ++ 0x04dbee8003ddf000#64 ++ 0x6ffff8003fff000b#64 ++ 0xf6ffff8003fff000#64 : BitVec 256),
   (0x8fef77f7c0000000#64 ++ 0x08fef77f7c000000#64 ++ 0x8fffffffc0000007#64 ++ 0xf8fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [10, 3]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [13, 8]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0001989450110911 0x4000198945011091 0x0003f804c0130132 0x00003f804c013013

def z1 : W := mkw 0x00c4424180664468 0x800c442418066446 0xd1cc4647c1ffc7ff 0x7d1cc4647c1ffc7f

def z2 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xfe0f87873e1cf9ce 0xefe0f87873e1cf9c

def z3 : W := mkw 0x2b6007600aa0e40a 0x02b6007600aa0e40 0xcfc006000ee0c000 0x5cfc006000ee0c00

def z4 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x6ffff8003fff000b 0xf6ffff8003fff000

def z5 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8fffffffc0000007 0xf8fffffffc000000

def z6 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x3033f9fcf1133f3f 0xa3033f9fcf1133f3

def z7 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfff007f83fe0fe0d 0xffff007f83fe0fe0

def z8 : W := mkw 0x3f6a07620ea8e48a 0x03f6a07620ea8e48 0xcfcc06030eecc0c0 0x5cfcc06030eecc0c

def z9 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x9fffffffc113073f 0xf9fffffffc113073

def z10 : W := mkw 0x0010880831775f7d 0xc0010880831775f7 0x7000000031fffff8 0x07000000031fffff

def z11 : W := mkw 0x2b6007600aa0e40a 0x02b6007600aa0e40 0xffc007803ee0f80c 0xfffc007803ee0f80

def z12 : W := mkw 0x89e572f5c0000000 0x089e572f5c000000 0x01f3f9fcc0000007 0xb01f3f9fcc000000

def z13 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0xdfffffffc1ffc7ff 0xfdfffffffc1ffc7f

def z14 : W := mkw 0x060b058600000000 0x0060b05860000000 0x8e0f878700000006 0xe8e0f87870000000

def z15 : W := mkw 0x0001808410100901 0x0000180841010090 0xf00f8787301cf9ce 0xef00f8787301cf9c

def z16 : W := mkw 0x8feff7f7d0100901 0x08feff7f7d010090 0xbffffffff010390f 0xfbffffffff010390

def z17 : W := mkw 0x0001109440000000 0x0000110944000000 0x0033f9fcc0000007 0xa0033f9fcc000000

def z18 : W := mkw 0x160a05020608a080 0x0160a05020608a08 0xce0c06030e0cc0c0 0x4ce0c06030e0cc0c

def z19 : W := mkw 0x0000000000000000 0x0000000000000000 0xd00c0607001cc1ce 0x6d00c0607001cc1c

def z20 : W := mkw 0x16cfc7c7967eede9 0x816cfc7c7967eede 0xffcfc7c7ffffffff 0xfffcfc7c7fffffff

def z21 : W := mkw 0x101088083719bb95 0x4101088083719bb9 0x700000003f1ffff8 0x0700000003f1ffff

def z22 : W := mkw 0x161b9d9e7719bb95 0x4161b9d9e7719bb9 0xfe3fffffff1fffff 0xefe3fffffff1ffff

def z23 : W := mkw 0x0010181861011214 0x4001018186101121 0x00307878c1030631 0x000307878c103063

def z24 : W := mkw 0x0000880010110000 0x0000088001011000 0x0003f80000130002 0x00003f8000013000

def z25 : W := mkw 0x0040024180204468 0x8004002418020446 0x00000040c0000630 0x000000040c000063

def z26 : W := mkw 0x040a800014180000 0x0040a80001418000 0x2e0380003e000000 0x82e0380003e00000

def z27 : W := mkw 0x120105860200a981 0x0120105860200a98 0xfe0007873e00f9cc 0xefe0007873e00f9c

def z28 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xeff007b83ee0f800 0xdeff007b83ee0f80

def z29 : W := mkw 0x0001008400000901 0x0000100840000090 0x1000018400003904 0x0100001840000390

def z30 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x6fcc00003fff0008 0x56fcc00003fff000

def z31 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0x0e33b9b800000000 0x80e33b9b80000000

def z32 : W := mkw 0x8ffffffff1111b15 0x48ffffffff1111b1 0xbffffffff1133f3f 0xfbffffffff1133f3

def z33 : W := mkw 0x0000000000664468 0x8000000000066446 0x5000000001ffc7f8 0x05000000001ffc7f

def z34 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x3000000031133f38 0x03000000031133f3

def z35 : W := mkw 0x2b319dbc7b91bb17 0x42b319dbc7b91bb1 0x3e33f9fcff133f3f 0xa3e33f9fcff133f3

def z36 : W := mkw 0x6ffeef683ffff60e 0x06ffeef683ffff60 0xfffffff83ffffe0f 0xffffffff83ffffe0

def z37 : W := mkw 0x5fbffd9e7fdfbb95 0x45fbffd9e7fdfbb9 0xffffffffffffffff 0xffffffffffffffff

def z38 : W := mkw 0x201000082ba0f60e 0x0201000082ba0f60 0x700000003fe0fe08 0x0700000003fe0fe0

def z39 : W := mkw 0x0084400180460060 0x8008440018046006 0x000c4007c01f01f2 0x0000c4007c01f01f

def z40 : W := mkw 0x8fef77f7c0460060 0x88fef77f7c046006 0x8fffffffc01f01f7 0xf8fffffffc01f01f

def z41 : W := mkw 0x0001109440000000 0x0000110944000000 0x1033f9fcc113073f 0xa1033f9fcc113073

def z42 : W := mkw 0x2b7007682b80b206 0x02b7007682b80b20 0xaff007f83e003805 0xfaff007f83e00380

def z43 : W := mkw 0x82c557f7c0000000 0x082c557f7c000000 0x81cc47ffc0000007 0x781cc47ffc000000

def z44 : W := mkw 0x060a85001618a000 0x0060a85001618a00 0xfe0f87803e1cf80e 0xefe0f87803e1cf80

def z45 : W := mkw 0xa24117ffc220f60e 0x0a24117ffc220f60 0x900007ffc000fe04 0x0900007ffc000fe0

def z46 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xee0f87833e0cf8c0 0xcee0f87833e0cf8c

def z47 : W := mkw 0x00c552d5c0000000 0x000c552d5c000000 0x81ffffffc0000007 0xf81ffffffc000000

def z48 : W := mkw 0x00d5daddf1775f7d 0xc00d5daddf1775f7 0xf1fffffff1ffffff 0xff1fffffff1fffff

def z49 : W := mkw 0xaffe676baba0f60e 0x0affe676baba0f60 0xfffc07fb3fe0fe0d 0xffffc07fb3fe0fe0

def z50 : W := mkw 0x0011989c71775f7d 0xc0011989c71775f7 0x7033f9fcf1ffffff 0xa7033f9fcf1fffff

def z51 : W := mkw 0x0b60076000000000 0x00b6007600000000 0x8ff007f800000005 0xf8ff007f80000000

def z52 : W := mkw 0x0dae600000000000 0x00dae60000000000 0x0ffff80000000003 0xf0ffff8000000000

def z53 : W := mkw 0x0001109c40001b15 0x40001109c40001b1 0x100001fcc0003f34 0x0100001fcc0003f3

def z54 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x2033f9f8f1033e31 0x82033f9f8f1033e3

def z55 : W := mkw 0x00c4424180664468 0x800c442418066446 0x01c04040c1e30631 0x101c04040c1e3063

def z56 : W := mkw 0x0040024180204468 0x8004002418020446 0x90000647c000c7f4 0x090000647c000c7f

def z57 : W := mkw 0x2b3005282b80b206 0x02b3005282b80b20 0x6ff001b83fe03809 0xf6ff001b83fe0380

def z58 : W := mkw 0x848f7097c0000000 0x0848f7097c000000 0x000ff807c0000002 0x0000ff807c000000

def z59 : W := mkw 0x89e47271c0000000 0x089e47271c000000 0x01f07878c0000001 0x101f07878c000000

def z60 : W := mkw 0x0fee676000000000 0x00fee67600000000 0x8ffffff800000007 0xf8ffffff80000000

def z61 : W := mkw 0x8fff7fffe1011214 0x48fff7fffe101121 0x8fffffffc1030637 0xf8fffffffc103063

def z62 : W := mkw 0x160b9d965619a991 0x4160b9d965619a99 0xfe0fff87fe1ff9fe 0xefe0fff87fe1ff9f

def z63 : W := mkw 0x2b3005282b80b206 0x02b3005282b80b20 0x2e3001b83e003800 0x82e3001b83e00380

def z64 : W := mkw 0x5fbfed863fdfa981 0x05fbfed863fdfa98 0xffffff873ffff9cf 0xfffffff873ffff9c

def z65 : W := mkw 0x0011888431110901 0x0001188843111090 0x3033f9843113390f 0xa3033f9843113390

def z66 : W := mkw 0x005002482120560c 0x0005002482120560 0xf1f007f831e0fe0d 0xff1f007f831e0fe0

def z67 : W := mkw 0x8ffffffff1111b15 0x48ffffffff1111b1 0xaffffffff0003807 0xfaffffffff000380

def z68 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x2033b9b830003800 0x82033b9b83000380

def z69 : W := mkw 0x0000000800001204 0x0000000080000120 0x100001f800003e04 0x0100001f800003e0

def z70 : W := mkw 0xafef77f7caa0e40a 0x0afef77f7caa0e40 0xcfffffffcee0c007 0xfcfffffffcee0c00

def z71 : W := mkw 0x2b7117fc6ba0ff1f 0x42b7117fc6ba0ff1 0xfff007fcffe0ff3d 0xffff007fcffe0ff3

def z72 : W := mkw 0x040a800014180000 0x0040a80001418000 0x6e0f80003e1c000a 0xe6e0f80003e1c000

def z73 : W := mkw 0x060b058600000000 0x0060b05860000000 0xde0f8787001cc1ce 0xede0f8787001cc1c

def z74 : W := mkw 0x0dbff89c71111b15 0x40dbff89c71111b1 0x3ffff9fcf1133f3f 0xf3ffff9fcf1133f3

def z75 : W := mkw 0x0001808410100901 0x0000180841010090 0x300381843010390e 0xa300381843010390

def z76 : W := mkw 0x224117fc4220ff1f 0x4224117fc4220ff1 0x900007fcc000ff34 0x0900007fcc000ff3

def z77 : W := mkw 0x4dbee8003d990000 0x04dbee8003d99000 0x2ffff8003e000003 0xf2ffff8003e00000

def z78 : W := mkw 0x4094c8003ddf0000 0x04094c8003ddf000 0x61cc40003fff000b 0x761cc40003fff000

def z79 : W := mkw 0x02119d9c7311bb15 0x402119d9c7311bb1 0xfe33fffcff13ff3f 0xefe33fffcff13ff3

def z80 : W := mkw 0x4dbe60002dce0000 0x04dbe60002dce000 0x6ffc00003fec0009 0xf6ffc00003fec000

def z81 : W := mkw 0x4dbff89c7ddf1b15 0x44dbff89c7ddf1b1 0x7ffff9fcffff3f3f 0xf7ffff9fcffff3f3

def z82 : W := mkw 0x00c552d5c0664468 0x800c552d5c066446 0xd1ffffffc1ffc7ff 0xfd1ffffffc1ffc7f

def z83 : W := mkw 0x0930000029800000 0x0093000002980000 0x6ff000003fe00009 0xf6ff000003fe0000

def z84 : W := mkw 0x2bf44769abe6f66e 0x82bf44769abe6f66 0xfffc47ffffffffff 0xffffc47fffffffff

def z85 : W := mkw 0xafff77ffeba0f60e 0x0afff77ffeba0f60 0xffffffffffe0fe0f 0xfffffffffffe0fe0

def z86 : W := mkw 0x0010000821001204 0x0001000082100120 0x303001f831003e0d 0xa303001f831003e0

def z87 : W := mkw 0x8fee676380000000 0x08fee67638000000 0x8ffc07fb00000005 0xf8ffc07fb0000000

def z88 : W := mkw 0x0b60076000000000 0x00b6007600000000 0x8fc0060000000000 0x58fc006000000000

def z89 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0x2ff001f83fe03e01 0x92ff001f83fe03e0

def z90 : W := mkw 0x0040024000204408 0x0004002400020440 0xd1c0064001e0c60d 0x7d1c0064001e0c60

def z91 : W := mkw 0x224007680220f60e 0x0224007680220f60 0x900007f80000fe04 0x0900007f80000fe0

def z92 : W := mkw 0x824117f7c0000000 0x0824117f7c000000 0x800007ffc0000004 0x0800007ffc000000

def z93 : W := mkw 0x8fef77ffc0001b15 0x48fef77ffc0001b1 0x9fffffffc0003f37 0xf9fffffffc0003f3

def z94 : W := mkw 0x9feff7f7d618a981 0x09feff7f7d618a98 0xaffffffffe003807 0xfaffffffffe00380

def z95 : W := mkw 0x0001109c40001b15 0x40001109c40001b1 0x000001b800003800 0x0000001b80000380

def z96 : W := mkw 0x0084400180460060 0x8008440018046006 0x000c0003000c00c0 0x0000c0003000c00c

def z97 : W := mkw 0x448ee800145f0000 0x0448ee800145f000 0x000ff800001f0002 0x0000ff800001f000

def z98 : W := mkw 0x4dae60000cce0000 0x04dae60000cce000 0x4fcc00000eec0000 0x54fcc00000eec000

def z99 : W := mkw 0x0095d89df1571b75 0xc0095d89df1571b7 0x303ff9fff11f3fff 0xa303ff9fff11f3ff

def z100 : W := mkw 0x401088003d990000 0x0401088003d99000 0x200000003e000000 0x0200000003e00000

def z101 : W := mkw 0x100080001618a981 0x0100080001618a98 0x700000003e1cf9c8 0x0700000003e1cf9c

def z102 : W := mkw 0x0dbee80031110000 0x00dbee8003111000 0x2ffff8003113000b 0xf2ffff8003113000

def z103 : W := mkw 0x020005000200a000 0x0020005000200a00 0xfe0c07873e1cf9ce 0xefe0c07873e1cf9c

def z104 : W := mkw 0x4dfeea41bdff4468 0x84dfeea41bdff446 0xfffffe47ffffc7ff 0xffffffe47ffffc7f

def z105 : W := mkw 0x140b808614180981 0x0140b80861418098 0x000f8007001c01c2 0x0000f8007001c01c

def z106 : W := mkw 0x0000000000000000 0x0000000000000000 0x10004044c113073f 0x210004044c113073

def z107 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfff047fcfff3ff3f 0xffff047fcfff3ff3

def z108 : W := mkw 0x4dbef8187ddf1214 0x44dbef8187ddf121 0x6ffff878ffff063b 0xf6ffff878ffff063

def z109 : W := mkw 0x0000000000000000 0x0000000000000000 0x00004044c0000007 0x200004044c000000

def z110 : W := mkw 0x0001109440000000 0x0000110944000000 0x0003f804c0000002 0x00003f804c000000

def z111 : W := mkw 0x2bf44769abe6f66e 0x82bf44769abe6f66 0xfff047f8ffe3fe3d 0xffff047f8ffe3fe3

def z112 : W := mkw 0x8faf75b7c0000000 0x08faf75b7c000000 0x0e3ff9bfc0000002 0x80e3ff9bfc000000

def z113 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xbe0387873e00f9c4 0x8be0387873e00f9c

def z114 : W := mkw 0x04cec241947e4468 0x804cec241947e446 0xffcfc647ffffc7ff 0xfffcfc647ffffc7f

def z115 : W := mkw 0x9ffffffff719bb95 0x49ffffffff719bb9 0xffffffffff1fffff 0xfffffffffff1ffff

def z116 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0x91f007f801e0fe05 0x191f007f801e0fe0

def z117 : W := mkw 0x2b719ffc7bb1ff1f 0x42b719ffc7bb1ff1 0xfff3fffcfff3ff3f 0xffff3fffcfff3ff3

def z118 : W := mkw 0x0000000000664468 0x8000000000066446 0x50004044c1ffc7ff 0x250004044c1ffc7f

def z119 : W := mkw 0x0000000000000000 0x0000000000000000 0xd00006000000c00c 0x6d00006000000c00

def z120 : W := mkw 0x8920303040000000 0x0892030304000000 0x0030383800000000 0x0003038380000000

def z121 : W := mkw 0x8be47771c0000000 0x08be47771c000000 0x8ff07ff8c0000005 0xf8ff07ff8c000000

def z122 : W := mkw 0x49b4e8003ddf0000 0x049b4e8003ddf000 0x61f078003fff0009 0x161f078003fff000

def z123 : W := mkw 0x848f7097c0000000 0x0848f7097c000000 0x003ff9ffc0000007 0xa003ff9ffc000000

def z124 : W := mkw 0x2b708f683bb1f60e 0x02b708f683bb1f60 0xfff3fff83ff3fe0f 0xffff3fff83ff3fe0

def z125 : W := mkw 0xafff77ffebe6f66e 0x8afff77ffebe6f66 0xffffffffffffffff 0xffffffffffffffff

def z126 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x2033f9b83113380b 0xa2033f9b83113380

def z127 : W := mkw 0x0010000821001204 0x0001000082100120 0x203001b830003800 0x8203001b83000380

def z128 : W := mkw 0x060b159640000000 0x0060b15964000000 0x8e3fffffc0000007 0xe8e3fffffc000000

def z129 : W := mkw 0x00c4424180664468 0x800c442418066446 0xc1cc060300ecc0c0 0x5c1cc060300ecc0c

def z130 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0xcfffffffc0ecc0c7 0xfcfffffffc0ecc0c

def z131 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0x8e3fbfbf00000006 0xe8e3fbfbf0000000

def z132 : W := mkw 0x0dae600000460000 0x00dae60000046000 0x4ffff80001ff000b 0xf4ffff80001ff000

def z133 : W := mkw 0x4fbfed863ddf0000 0x04fbfed863ddf000 0xefffff873fff000f 0xfefffff873fff000

def z134 : W := mkw 0x8fee7773c0000000 0x08fee7773c000000 0x8ffc7e7bc0000001 0x58ffc7e7bc000000

def z135 : W := mkw 0x2b319dbc7b91bb17 0x42b319dbc7b91bb1 0x2e33b9b83e003800 0x82e33b9b83e00380

def z136 : W := mkw 0x140a000204080080 0x0140a00020408008 0x000c0003000c00c0 0x0000c0003000c00c

def z137 : W := mkw 0x160b95965618a981 0x0160b95965618a98 0xfe3ffffffe1cf9cf 0xefe3ffffffe1cf9c

def z138 : W := mkw 0xcffffff7fddf0000 0x0cffffff7fddf000 0xefffffffffff000f 0xfefffffffffff000

def z139 : W := mkw 0x0001109440000000 0x0000110944000000 0x000001fcc0000004 0x0000001fcc000000

def z140 : W := mkw 0x8f3bbdbe71111b15 0x48f3bbdbe71111b1 0x3e33f9fcf1133f3f 0xa3e33f9fcf1133f3

def z141 : W := mkw 0xeffffffffffff60e 0x0effffffffffff60 0xfffffffffffffe0f 0xffffffffffffffe0

def z142 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x2000000030003800 0x0200000003000380

def z143 : W := mkw 0x0000800010100000 0x0000080001010000 0x200380003010000a 0xa200380003010000

def z144 : W := mkw 0x0010181861011214 0x4001018186101121 0x1030787cc113073f 0x21030787cc113073

def z145 : W := mkw 0x2970026829a0560e 0x02970026829a0560 0x01f0007801e00601 0x101f0007801e0060

def z146 : W := mkw 0x3f7b87ee3fb8ff8f 0x03f7b87ee3fb8ff8 0xffff87ff3ffcffcf 0xfffff87ff3ffcffc

def z147 : W := mkw 0x3b7107ee2ba0ff8f 0x03b7107ee2ba0ff8 0xfff007ff3fe0ffcd 0xffff007ff3fe0ffc

def z148 : W := mkw 0x140b808614180981 0x0140b80861418098 0x6e0f80073e1c01ca 0xe6e0f80073e1c01c

def z149 : W := mkw 0xaf3b35be6b80b206 0x0af3b35be6b80b20 0x2e33b9b83e003800 0x82e33b9b83e00380

def z150 : W := mkw 0x5fbfed863fdfa981 0x05fbfed863fdfa98 0x6ffff9803fff380b 0xf6ffff9803fff380

def z151 : W := mkw 0x4dbee801bddf0060 0x84dbee801bddf006 0x6ffff807ffff01fb 0xf6ffff807ffff01f

def z152 : W := mkw 0x0930000029800000 0x0093000002980000 0x01f0000001e00001 0x101f0000001e0000

def z153 : W := mkw 0x0001989450110911 0x4000198945011091 0x0033f9fcc0130137 0xa0033f9fcc013013

def z154 : W := mkw 0x0040024000664468 0x8004002400066446 0xd1c0064001ffc7fd 0x7d1c0064001ffc7f

def z155 : W := mkw 0x401088003ddf0000 0x0401088003ddf000 0x6033f8003fff000b 0xa6033f8003fff000

def z156 : W := mkw 0x2bf44769aba0f60e 0x02bf44769aba0f60 0xfffc47ffffe0fe0f 0xffffc47ffffe0fe0

def z157 : W := mkw 0x0011109c61001204 0x00011109c6100120 0x3033f9fcf1003e0f 0xa3033f9fcf1003e0

def z158 : W := mkw 0x2b6007680aa0f60e 0x02b6007680aa0f60 0xdfc007f80ee0fe04 0x5dfc007f80ee0fe0

def z159 : W := mkw 0x9fefe7e79618a981 0x09fefe7e79618a98 0xffcf87873e1cf9ce 0xfffcf87873e1cf9c

def z160 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0x2e0381803e003800 0x82e0381803e00380

def z161 : W := mkw 0x6ffeef69bffff66e 0x86ffeef69bffff66 0xffffffffffffffff 0xffffffffffffffff

def z162 : W := mkw 0x0be4476180000000 0x00be447618000000 0x8ffc47ffc0000007 0xf8ffc47ffc000000

def z163 : W := mkw 0x201000082be6f66e 0x8201000082be6f66 0x700000003ffffff8 0x0700000003ffffff

def z164 : W := mkw 0x0dbe600029800000 0x00dbe60002980000 0x6ffff8003fe0000b 0xf6ffff8003fe0000

def z165 : W := mkw 0x4dfeea41bdff4468 0x84dfeea41bdff446 0xeffffe033fffc0cb 0xfeffffe033fffc0c

def z166 : W := mkw 0x9feff7f7d618a981 0x09feff7f7d618a98 0xfffffffffe1cf9cf 0xffffffffffe1cf9c

def z167 : W := mkw 0x3f7b9ffe7fb9ff9f 0x43f7b9ffe7fb9ff9 0xffffffffffffffff 0xffffffffffffffff

def z168 : W := mkw 0x0b6117f440000000 0x00b6117f44000000 0x8ff3fffcc0000007 0xf8ff3fffcc000000

def z169 : W := mkw 0x2b6007600aa0e40a 0x02b6007600aa0e40 0xcff007f80ee0c005 0xfcff007f80ee0c00

def z170 : W := mkw 0x401088003ddf0000 0x0401088003ddf000 0x600000003fff0008 0x0600000003fff000

def z171 : W := mkw 0x0011989471110000 0x0001198947111000 0x2033f9fcf113000f 0xa2033f9fcf113000

def z172 : W := mkw 0x0000800010100901 0x0000080001010090 0x3000000030103908 0x0300000003010390

def z173 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xae0f87873e003806 0xeae0f87873e00380

def z174 : W := mkw 0x7fffefee3fffff8f 0x07fffefee3fffff8 0xffffffff3fffffcf 0xfffffffff3fffffc

def z175 : W := mkw 0x0001989450110911 0x4000198945011091 0x3003f984f013393e 0xa3003f984f013393

def z176 : W := mkw 0x0084400180664468 0x8008440018066446 0x500c4007c1ffc7fa 0x0500c4007c1ffc7f

def z177 : W := mkw 0x2b6007680220f60e 0x02b6007680220f60 0x9ff007f80000fe05 0xf9ff007f80000fe0

def z178 : W := mkw 0x0000000800001b15 0x40000000800001b1 0x1000000000003f30 0x01000000000003f3

def z179 : W := mkw 0x1f6b87e61618a981 0x01f6b87e61618a98 0xffff87ff3e1cf9cf 0xfffff87ff3e1cf9c

def z180 : W := mkw 0x561b8d863fdfa981 0x0561b8d863fdfa98 0xfe0f87873ffff9ce 0xefe0f87873ffff9c

def z181 : W := mkw 0x4d3aa8003d990000 0x04d3aa8003d99000 0x6ff3b8003fe00009 0xf6ff3b8003fe0000

def z182 : W := mkw 0x2b700769aba0f66e 0x82b700769aba0f66 0xfff007ffffe0fffd 0xffff007ffffe0fff

def z183 : W := mkw 0x8fee676380000000 0x08fee67638000000 0x8fcc060300000000 0x58fcc06030000000

def z184 : W := mkw 0x0040024000204408 0x0004002400020440 0x01c0004001e00601 0x101c0004001e0060

def z185 : W := mkw 0x020005000200a000 0x0020005000200a00 0xfe0007803e00f80c 0xefe0007803e00f80

def z186 : W := mkw 0x0010000821001204 0x0001000082100120 0x3000000031003e08 0x03000000031003e0

def z187 : W := mkw 0xcfef77f7ccce0000 0x0cfef77f7ccce000 0xcfffffffceec0007 0xfcfffffffceec000

def z188 : W := mkw 0x6f7aaf683fb9f60e 0x06f7aaf683fb9f60 0xfff3bff83fe0fe0d 0xffff3bff83fe0fe0

def z189 : W := mkw 0x00c4424180664468 0x800c442418066446 0x01cc4047c1ff07f3 0x101cc4047c1ff07f

def z190 : W := mkw 0x0010000029800000 0x0001000002980000 0x600000003fe00008 0x0600000003fe0000

def z191 : W := mkw 0x0084400000664468 0x8008440000066446 0x51cc400001ffc7fb 0x751cc400001ffc7f

def z192 : W := mkw 0x0001808410100901 0x0000180841010090 0x2003818030003800 0x8200381803000380

def z193 : W := mkw 0x4dae60000cce0000 0x04dae60000cce000 0x4ffff8000eec0003 0xf4ffff8000eec000

def z194 : W := mkw 0x0011189c61011b15 0x40011189c61011b1 0x103079fcc1033f35 0x0103079fcc1033f3

def z195 : W := mkw 0x00c4424180664468 0x800c442418066446 0xd1cc060700fcc1ce 0x7d1cc060700fcc1c

def z196 : W := mkw 0x0084400000460000 0x0008440000046000 0x41cc400001ff000b 0x741cc400001ff000

def z197 : W := mkw 0x120085001618a981 0x0120085001618a98 0xfe0007803e1cf9cc 0xefe0007803e1cf9c

def z198 : W := mkw 0x8ffffffff1775f7d 0xc8ffffffff1775f7 0xfffffffff1ffffff 0xffffffffff1fffff

def z199 : W := mkw 0x0010880031110000 0x0001088003111000 0x2033f8003113000b 0xa2033f8003113000

def z200 : W := mkw 0x000000000200a000 0x0000000000200a00 0x700000003e00f808 0x0700000003e00f80

def z201 : W := mkw 0x8fff77f7e9800000 0x08fff77f7e980000 0xefffffffffe0000f 0xfefffffffffe0000

def z202 : W := mkw 0xafef77ffc220f60e 0x0afef77ffc220f60 0x9fffffffc000fe07 0xf9fffffffc000fe0

def z203 : W := mkw 0xafee67638aa0e40a 0x0afee67638aa0e40 0xcfcc06030ee0c000 0x5cfcc06030ee0c00

def z204 : W := mkw 0x0001989450110911 0x4000198945011091 0x1003f844c113073f 0x21003f844c113073

def z205 : W := mkw 0x0b20052000000000 0x00b2005200000000 0x0e3001b800000000 0x80e3001b80000000

def z206 : W := mkw 0x0d2a200000000000 0x00d2a20000000000 0x0e33b80000000000 0x80e33b8000000000

def z207 : W := mkw 0xcfbffdb67ddf0000 0x0cfbffdb67ddf000 0x6ffff9b83fff000b 0xf6ffff9b83fff000

def z208 : W := mkw 0x0b6007600200a000 0x00b6007600200a00 0xfff007f83e00f80d 0xffff007f83e00f80

def z209 : W := mkw 0x84cf72d7c0664468 0x884cf72d7c066446 0xd1cffe47c1ffc7ff 0x7d1cffe47c1ffc7f

def z210 : W := mkw 0x0000000000000000 0x0000000000000000 0x10000044c0000734 0x010000044c000073

def z211 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000000001cc1c8 0x050000000001cc1c

def z212 : W := mkw 0x2970026829a0560e 0x02970026829a0560 0xd1f0067801e0c60d 0x7d1f0067801e0c60

def z213 : W := mkw 0x9feff7f7d67eede9 0x89feff7f7d67eede 0xffffffffffffffff 0xffffffffffffffff

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z215 : W := mkw 0x205002482ba0f60e 0x0205002482ba0f60 0xf1c006403fe0fe0d 0x7f1c006403fe0fe0

def z216 : W := mkw 0x6dfeea683dff560e 0x06dfeea683dff560 0x6ffff8783fff060b 0xf6ffff8783fff060

def z217 : W := mkw 0x16dfdfdff77ffffd 0xc16dfdfdff77ffff 0xffffffffffffffff 0xffffffffffffffff

def z218 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0xdfffffffc01cc1cf 0xfdfffffffc01cc1c

def z219 : W := mkw 0x00c4424180000000 0x000c442418000000 0xd1cc4647c01cc1cf 0x7d1cc4647c01cc1c

def z220 : W := mkw 0x221005082ba0f60e 0x0221005082ba0f60 0xfe0007803fe0fe0c 0xefe0007803fe0fe0

def z221 : W := mkw 0xc48ff897d45f0000 0x0c48ff897d45f000 0x000ff807c01f0002 0x0000ff807c01f000

def z222 : W := mkw 0x4daee0001cde0000 0x04daee0001cde000 0x6fcf80003efc000a 0xf6fcf80003efc000

def z223 : W := mkw 0x0001109440000911 0x4000110944000091 0x00000004c0000130 0x000000004c000013

def z224 : W := mkw 0x8fef77f7c0204408 0x08fef77f7c020440 0xdfffffffc1e0c60f 0xfdfffffffc1e0c60

def z225 : W := mkw 0x2f7b07ee2ba0f60e 0x02f7b07ee2ba0f60 0xffff87ff3fe0fe0f 0xfffff87ff3fe0fe0

def z226 : W := mkw 0x44ceea41947f4468 0x844ceea41947f446 0xd1cffe47c1ffc7ff 0x7d1cffe47c1ffc7f

def z227 : W := mkw 0x4dbfe8843ddf0901 0x04dbfe8843ddf090 0x7ffff9843fff390f 0xf7ffff9843fff390

def z228 : W := mkw 0xa9f47279e9a0560e 0x0a9f47279e9a0560 0x01f07878c1e00601 0x101f07878c1e0060

def z229 : W := mkw 0x3f7a076a2fa8f68e 0x03f7a076a2fa8f68 0xfffc07fb3fecfecd 0xffffc07fb3fecfec

def z230 : W := mkw 0x5dbfe8863ddf0981 0x05dbfe8863ddf098 0x6ffff8073fff01cb 0xf6ffff8073fff01c

def z231 : W := mkw 0x204002680020560e 0x0204002680020560 0x0000007800000600 0x0000000780000060

def z232 : W := mkw 0x140b808614180981 0x0140b80861418098 0x300f8187301c39ce 0xa300f8187301c39c

def z233 : W := mkw 0xab7117ffeba0f60e 0x0ab7117ffeba0f60 0xfff007ffffe0fe0d 0xffff007ffffe0fe0

def z234 : W := mkw 0x8def72f7c0000000 0x08def72f7c000000 0x01fff87fc0000003 0x101fff87fc000000

def z235 : W := mkw 0x601088083ffff60e 0x0601088083ffff60 0x700000003ffffe08 0x0700000003ffffe0

def z236 : W := mkw 0x449ee8003ddf0000 0x0449ee8003ddf000 0x600ff8003fff000a 0x0600ff8003fff000

def z237 : W := mkw 0x4d2a20000c880000 0x04d2a20000c88000 0x0e0000000e000000 0x00e0000000e00000

def z238 : W := mkw 0x2b3005282ba0f60e 0x02b3005282ba0f60 0x7e3001b83fe0fe08 0x87e3001b83fe0fe0

def z239 : W := mkw 0x40008800145f0000 0x040008800145f000 0x00000000001f0000 0x000000000001f000

def z240 : W := mkw 0x2b3005282b80b206 0x02b3005282b80b20 0x3e3001f83f003e0d 0xa3e3001f83f003e0

def z241 : W := mkw 0x0011989471110911 0x4001198947111091 0x2033f804f113013b 0xa2033f804f113013

def z242 : W := mkw 0x0000101840001214 0x4000010184000121 0x00000078c0000630 0x000000078c000063

def z243 : W := mkw 0x2b7187ec3bb0ff0f 0x02b7187ec3bb0ff0 0xfff387fc3ff0ff0f 0xffff387fc3ff0ff0

def z244 : W := mkw 0x09b4400029c60000 0x009b4400029c6000 0x6ffc40003fff000b 0xf6ffc40003fff000

def z245 : W := mkw 0x0daee00014180000 0x00daee0001418000 0x6ffff8003e1c000b 0xf6ffff8003e1c000

def z246 : W := mkw 0x0094c80031570000 0x00094c8003157000 0x61fff80031ff000b 0xf61fff80031ff000

def z247 : W := mkw 0x2b719ffc7bb1ff1f 0x42b719ffc7bb1ff1 0xfff3bff83fe0fe0d 0xffff3bff83fe0fe0

def z248 : W := mkw 0x9fef77f7c608a080 0x09fef77f7c608a08 0xcfffffffce0cc0c7 0xfcfffffffce0cc0c

def z249 : W := mkw 0x8f3bbdbe71111b15 0x48f3bbdbe71111b1 0x2e33b9b830003800 0x82e33b9b83000380

def z250 : W := mkw 0x3b7087683fb8ff8f 0x03b7087683fb8ff8 0xfff007f83ffcffcd 0xffff007f83ffcffc

def z251 : W := mkw 0x964b97f7d618a981 0x0964b97f7d618a98 0xfe0f87fffe1cf9ce 0xefe0f87fffe1cf9c

def z252 : W := mkw 0x00c4424180664468 0x800c442418066446 0xd1cc060301ffc7f8 0x5d1cc060301ffc7f

def z253 : W := mkw 0x49f46a41a9e74468 0x849f46a41a9e7446 0x01f07840c1e30631 0x101f07840c1e3063

def z254 : W := mkw 0x364b87ee1638ff8f 0x0364b87ee1638ff8 0xfe0f87ff3e1cffce 0xefe0f87ff3e1cffc

def z255 : W := mkw 0x0930880039910000 0x0093088003991000 0x6ff3f8003ff3000b 0xf6ff3f8003ff3000

def z256 : W := mkw 0x0970024029a04408 0x00970024029a0440 0xfff006403fe0c60d 0xffff006403fe0c60

def z257 : W := mkw 0x2b708f683bb1ff1f 0x42b708f683bb1ff1 0xfff007f83ff3ff3d 0xffff007f83ff3ff3

def z258 : W := mkw 0x8fee676380664468 0x88fee67638066446 0xdfcc4647c1ffc7ff 0x7dfcc4647c1ffc7f

def z259 : W := mkw 0x0010981871111214 0x4001098187111121 0x2033f878f113063b 0xa2033f878f113063

def z260 : W := mkw 0xcffffffffddf1b15 0x4cffffffffddf1b1 0xffffffffffff3f3f 0xfffffffffffff3f3

def z261 : W := mkw 0x0000000000664468 0x8000000000066446 0x0000000001e30630 0x00000000001e3063

def z262 : W := mkw 0x0011109c61001b15 0x40011109c61001b1 0x303001fcf1003f3d 0xa303001fcf1003f3

def z263 : W := mkw 0x0084400000460000 0x0008440000046000 0x51cc4044c1ff073f 0x751cc4044c1ff073

def z264 : W := mkw 0x49b4680029c70000 0x049b4680029c7000 0x01f0780001e30001 0x101f0780001e3000

def z265 : W := mkw 0x9feff7f7d4180981 0x09feff7f7d418098 0x8fffffffc01c01c7 0xf8fffffffc01c01c

def z266 : W := mkw 0x864b17f7c0000000 0x0864b17f7c000000 0x8e0f87ffc0000006 0xe8e0f87ffc000000

def z267 : W := mkw 0x9fef77f7c200a981 0x09fef77f7c200a98 0x9fffffffc000f9c7 0xf9fffffffc000f9c

def z268 : W := mkw 0xaf7b37fe6ba0f60e 0x0af7b37fe6ba0f60 0xfff3bff83fe0fe0d 0xffff3bff83fe0fe0

def z269 : W := mkw 0x061b9d9e71111b15 0x4061b9d9e71111b1 0xbe3ffffff1133f3f 0xebe3ffffff1133f3

def z270 : W := mkw 0x00c4424180204468 0x800c442418020446 0x91cc4647c000c7f7 0x791cc4647c000c7f

def z271 : W := mkw 0x8fef67e780000000 0x08fef67e78000000 0x8fcf878700000006 0xf8fcf87870000000

def z272 : W := mkw 0x0010000821001204 0x0001000082100120 0x303041fcf1133f3f 0xa303041fcf1133f3

def z273 : W := mkw 0x8f6b37f640000000 0x08f6b37f64000000 0x8ff3bff800000005 0xf8ff3bff80000000

def z274 : W := mkw 0x0040024180204468 0x8004002418020446 0x800006030000c0c0 0x0800006030000c0c

def z275 : W := mkw 0x448ff894545f0911 0x4448ff894545f091 0x000ff804c01f0132 0x0000ff804c01f013

def z276 : W := mkw 0x00519addf1315f7d 0xc00519addf1315f7 0xb033fffff113ffff 0xab033fffff113fff

def z277 : W := mkw 0x0faf658600000000 0x00faf65860000000 0x8fffff8700000007 0xf8fffff870000000

def z278 : W := mkw 0x0010981871111b15 0x40010981871111b1 0x30307878f1133f39 0x030307878f1133f3

def z279 : W := mkw 0x16cfc7c7967eede9 0x816cfc7c7967eede 0xffcf87873efcf9ce 0xfffcf87873efcf9c

def z280 : W := mkw 0x00c5c2c590764d69 0x800c5c2c590764d6 0xf1cfc7c7f1ffffff 0xff1cfc7c7f1fffff

def z281 : W := mkw 0x4dbff8947ddf0000 0x04dbff8947ddf000 0x6ffff9fcffff000f 0xf6ffff9fcffff000

def z282 : W := mkw 0xcffffff7fd990000 0x0cffffff7fd99000 0xaffffffffe000007 0xfaffffffffe00000

def z283 : W := mkw 0x040a000000000000 0x0040a00000000000 0x0e0f800000000002 0xe0e0f80000000000

def z284 : W := mkw 0x00c4424180664468 0x800c442418066446 0x51c04040c1ffc7f9 0x151c04040c1ffc7f

def z285 : W := mkw 0x00c5dad5d0774d79 0xc00c5dad5d0774d7 0xd1cffe47c1ffc7ff 0x7d1cffe47c1ffc7f

def z286 : W := mkw 0x0000000000000000 0x0000000000000000 0x0033f80000000003 0xa0033f8000000000

def z287 : W := mkw 0x4d3aa8003d990000 0x04d3aa8003d99000 0x2e33b8003e000000 0x82e33b8003e00000

def z288 : W := mkw 0x00c4424180000000 0x000c442418000000 0x81cc4647c0000007 0x781cc4647c000000

def z289 : W := mkw 0x6bf46f682be7f60e 0x06bf46f682be7f60 0xfff07ff83fe3fe0d 0xffff07ff83fe3fe0

def z290 : W := mkw 0x201000082ba0f60e 0x0201000082ba0f60 0x703001f83fe0fe0d 0xa703001f83fe0fe0

def z291 : W := mkw 0x301080083fb8ff8f 0x0301080083fb8ff8 0x700000003ffcffc8 0x0700000003ffcffc

def z292 : W := mkw 0x00d44249a166566c 0x800d44249a166566 0xf1fc47fff1ffffff 0xff1fc47fff1fffff

def z293 : W := mkw 0x00c4424180664468 0x800c442418066446 0xd1cc0647c0ecc7f4 0x5d1cc0647c0ecc7f

def z294 : W := mkw 0x6ffe67682feef60e 0x06ffe67682feef60 0xfffc07f83fecfe0d 0xffffc07f83fecfe0

def z295 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0x8fffffffc1e30637 0xf8fffffffc1e3063

def z296 : W := mkw 0x0930000029800000 0x0093000002980000 0x2e3000003e000000 0x82e3000003e00000

def z297 : W := mkw 0x0001109440000000 0x0000110944000000 0x0033b9b800000000 0x80033b9b80000000

def z298 : W := mkw 0x9f2bb5b65618a981 0x09f2bb5b65618a98 0xfe3fbfbf3e1cf9ce 0xefe3fbfbf3e1cf9c

def z299 : W := mkw 0x568fed86165fa981 0x0568fed86165fa98 0xfe0fff873e1ff9ce 0xefe0fff873e1ff9c

def z300 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x7ffff844ffff073f 0xf7ffff844ffff073

def z301 : W := mkw 0x00d45a59e167567c 0xc00d45a59e167567 0xd1fc7e7fc1ffc7ff 0x7d1fc7e7fc1ffc7f

def z302 : W := mkw 0x168fc587965ea9e1 0x8168fc587965ea9e 0xfe0fc787fe1ff9fe 0xefe0fc787fe1ff9f

def z303 : W := mkw 0x501088003fdfa981 0x0501088003fdfa98 0x700000003ffff9c8 0x0700000003ffff9c

def z304 : W := mkw 0x3f3b85ae3f98bb87 0x03f3b85ae3f98bb8 0xfe3f87bf3e1cf9ce 0xefe3f87bf3e1cf9c

def z305 : W := mkw 0xcdbff897fddf0000 0x0cdbff897fddf000 0x6ffff807ffff000b 0xf6ffff807ffff000

def z306 : W := mkw 0x224007600220e40a 0x0224007600220e40 0x800006000000c000 0x0800006000000c00

def z307 : W := mkw 0x89e47271c0664468 0x889e47271c066446 0x01f07878c1e30631 0x101f07878c1e3063

def z308 : W := mkw 0x160b858614180981 0x0160b85861418098 0x8e0f8787001c01c6 0xe8e0f8787001c01c

def z309 : W := mkw 0x4dfeea41bddf0000 0x04dfeea41bddf000 0xeffffe47ffff000f 0xfeffffe47ffff000

def z310 : W := mkw 0xcdfefa71fddf0000 0x0cdfefa71fddf000 0x6ffff878ffff000b 0xf6ffff878ffff000

def z311 : W := mkw 0x448ee800145f0000 0x0448ee800145f000 0x41cff80001ff000b 0x741cff80001ff000

def z312 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8fcffe07c0000002 0x58fcffe07c000000

def z313 : W := mkw 0x5f3bad863f99a981 0x05f3bad863f99a98 0xfe3fbf873e1cf9ce 0xefe3fbf873e1cf9c

def z314 : W := mkw 0x2970026829a0560e 0x02970026829a0560 0x6ff000783fe00609 0xf6ff000783fe0060

def z315 : W := mkw 0x441a88003ddf0000 0x0441a88003ddf000 0x6e0f80003fff000a 0xe6e0f80003fff000

def z316 : W := mkw 0x0240076000000000 0x0024007600000000 0x800007f800000004 0x0800007f80000000

def z317 : W := mkw 0x160a05020608a080 0x0160a05020608a08 0xde0c06070e1cc1ce 0x6de0c06070e1cc1c

def z318 : W := mkw 0x4dbe68002dcf0000 0x04dbe68002dcf000 0x4ffc78000fef0001 0x54ffc78000fef000

def z319 : W := mkw 0x0dae600000000000 0x00dae60000000000 0x0fcc000000000000 0x50fcc00000000000

def z320 : W := mkw 0x0f6b07e600000000 0x00f6b07e60000000 0x8fff87ff00000007 0xf8fff87ff0000000

def z321 : W := mkw 0x020005000200a000 0x0020005000200a00 0xce0006000e00c000 0x4ce0006000e00c00

def z322 : W := mkw 0x06cf47c780000000 0x006cf47c78000000 0x8fcfc7c7c0000007 0xf8fcfc7c7c000000

def z323 : W := mkw 0x6dbee8083ffff60e 0x06dbee8083ffff60 0x7ffff8003ffffe0b 0xf7ffff8003ffffe0

def z324 : W := mkw 0x0000000000000000 0x0000000000000000 0x003001f800000005 0xa003001f80000000

def z325 : W := mkw 0x200000080220f60e 0x0200000080220f60 0x100000000000fe00 0x0100000000000fe0

def z326 : W := mkw 0x0010080021010000 0x0001008002101000 0x0030780001030001 0x0003078000103000

def z327 : W := mkw 0x161b858e3718bb85 0x0161b858e3718bb8 0xfe3f87ff3f1cffcf 0xefe3f87ff3f1cffc

def z328 : W := mkw 0x140b808614180981 0x0140b80861418098 0x0003800000000000 0x0000380000000000

def z329 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x3033b9fcf0003f34 0x83033b9fcf0003f3

def z330 : W := mkw 0x2f7a87683fb8f60e 0x02f7a87683fb8f60 0xffff87f83ffcfe0f 0xfffff87f83ffcfe0

def z331 : W := mkw 0x00c4424180664468 0x800c442418066446 0x11c04044c1f3073f 0x311c04044c1f3073

def z332 : W := mkw 0x824117f7c0000000 0x0824117f7c000000 0x8033ffffc0000007 0xa8033ffffc000000

def z333 : W := mkw 0x29f44269a9e6566e 0x829f44269a9e6566 0x01f04078c1e30631 0x101f04078c1e3063

def z334 : W := mkw 0x0001808410100901 0x0000180841010090 0x3003c1c4f1133f3f 0xa3003c1c4f1133f3

def z335 : W := mkw 0x2011989c7bb1ff1f 0x42011989c7bb1ff1 0x7033f9fcfff3ff3f 0xa7033f9fcfff3ff3

def z336 : W := mkw 0x140b989654190991 0x4140b98965419099 0x000ff807c01f01f2 0x0000ff807c01f01f

def z337 : W := mkw 0x4d3bb89c7d991b15 0x44d3bb89c7d991b1 0x3e33f9fcff133f3f 0xa3e33f9fcff133f3

def z338 : W := mkw 0x4d3aa8003ddf0000 0x04d3aa8003ddf000 0x6e33b8003fff0008 0x86e33b8003fff000

def z339 : W := mkw 0x448e6000044e0000 0x0448e6000044e000 0x000c0000000c0000 0x0000c0000000c000

def z340 : W := mkw 0x0930000829801204 0x0093000082980120 0x7ff001f83fe03e0d 0xf7ff001f83fe03e0

def z341 : W := mkw 0x09f44241a9e64468 0x809f44241a9e6446 0xfffc4647ffffc7ff 0xffffc4647ffffc7f

def z342 : W := mkw 0x4dee62418cee4468 0x84dee62418cee446 0xdfcc4647cfffc7ff 0x7dfcc4647cfffc7f

def z343 : W := mkw 0x0000000000000000 0x0000000000000000 0x41c0000001e00009 0x741c0000001e0000

def z344 : W := mkw 0xafff77ffe9a0560e 0x0afff77ffe9a0560 0x8fffffffc1e00607 0xf8fffffffc1e0060

def z345 : W := mkw 0x0b3005002b80a000 0x00b3005002b80a00 0xfff007803fe0f80d 0xffff007803fe0f80

def z346 : W := mkw 0x924117f7c200a981 0x0924117f7c200a98 0x900007ffc000f9c4 0x0900007ffc000f9c

def z347 : W := mkw 0x0011888c31111b15 0x40011888c31111b1 0x3003818431133f3e 0xa3003818431133f3

def z348 : W := mkw 0x29701a7869a1561e 0x429701a7869a1561 0x01f07878c1e30631 0x101f07878c1e3063

def z349 : W := mkw 0x0001909450100901 0x0000190945010090 0x3033f9fcf010390f 0xa3033f9fcf010390

def z350 : W := mkw 0x80011097c0000000 0x080011097c000000 0x00000007c0000000 0x000000007c000000

def z351 : W := mkw 0x0001109c40001b15 0x40001109c40001b1 0x1033f9fcc0003f37 0xa1033f9fcc0003f3

def z352 : W := mkw 0x49a4600008c60000 0x049a4600008c6000 0x01c0000000e00000 0x101c0000000e0000

def z353 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xbe3007f83e00fe04 0x8be3007f83e00fe0

def z354 : W := mkw 0x120105860200a981 0x0120105860200a98 0x900007870000f9c4 0x0900007870000f9c

def z355 : W := mkw 0x0000000000664468 0x8000000000066446 0xd00c060701ffc7fe 0x6d00c060701ffc7f

def z356 : W := mkw 0x8f6b37f7c0000000 0x08f6b37f7c000000 0x8e33bfffc0000004 0x88e33bfffc000000

def z357 : W := mkw 0x060b058600000000 0x0060b05860000000 0x0e03818000000000 0x80e0381800000000

def z358 : W := mkw 0x040b008600000000 0x0040b00860000000 0x000f800700000002 0x0000f80070000000

def z359 : W := mkw 0x041b989c75191b15 0x4041b989c75191b1 0x7e3ff9fcff1f3f3f 0xe7e3ff9fcff1f3f3

def z360 : W := mkw 0x160a85021618a080 0x0160a85021618a08 0xee0f86033e1cc0ca 0xeee0f86033e1cc0c

def z361 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x3033b9bc3010390e 0xa3033b9bc3010390

def z362 : W := mkw 0x0040024180000000 0x0004002418000000 0x80000647c0000004 0x080000647c000000

def z363 : W := mkw 0x868f7597c0000000 0x0868f7597c000000 0x8e0fff87c0000006 0xe8e0fff87c000000

def z364 : W := mkw 0x00d4ca49b1775f7d 0xc00d4ca49b1775f7 0xf1cc4647f1ffffff 0x7f1cc4647f1fffff

def z365 : W := mkw 0x8fee676380664468 0x88fee67638066446 0xcfcc060300ecc0c0 0x5cfcc060300ecc0c

def z366 : W := mkw 0x00c4424180664468 0x800c442418066446 0x41cc4040c1ff063b 0x741cc4040c1ff063

def z367 : W := mkw 0x49b4680029c70000 0x049b4680029c7000 0x41fc780001ff000b 0x741fc780001ff000

def z368 : W := mkw 0x0dee624180000000 0x00dee62418000000 0x8ffffe47c0000007 0xf8ffffe47c000000

def z369 : W := mkw 0x0084400180460060 0x8008440018046006 0xd00c4607c01fc1fe 0x6d00c4607c01fc1f

def z370 : W := mkw 0x0daf709440000000 0x00daf70944000000 0x0ffff9fcc0000007 0xf0ffff9fcc000000

def z371 : W := mkw 0x2b7117fc6ba0f60e 0x02b7117fc6ba0f60 0xfff3fffcffe0fe0f 0xffff3fffcffe0fe0

def z372 : W := mkw 0x14cfc2c7947e4de9 0x814cfc2c7947e4de 0xd1cfc647c1ffc7ff 0x7d1cfc647c1ffc7f

def z373 : W := mkw 0x041a880035190000 0x0041a88003519000 0x6e3ff8003f1f000b 0xe6e3ff8003f1f000

def z374 : W := mkw 0x040a800014180000 0x0040a80001418000 0xfe0f86073e1cc1ce 0xefe0f86073e1cc1c

def z375 : W := mkw 0x00d5daddf1111b15 0x400d5daddf1111b1 0xb1fffffff1133f3f 0xfb1fffffff1133f3

def z376 : W := mkw 0xbffff7ffffb8ff8f 0x0bffff7ffffb8ff8 0xfffffffffffcffcf 0xffffffffffffcffc

def z377 : W := mkw 0x361b858e3fb8ff8f 0x0361b858e3fb8ff8 0xfe0f87873ffcffce 0xefe0f87873ffcffc

def z378 : W := mkw 0x0040024000000000 0x0004002400000000 0x81c0064000000005 0x781c006400000000

def z379 : W := mkw 0xafff77ffeb80b206 0x0afff77ffeb80b20 0xaffffffffe003807 0xfaffffffffe00380

def z380 : W := mkw 0xcffffff7fdff4468 0x8cffffff7fdff446 0xffffffffffffc7ff 0xfffffffffffffc7f

def z381 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x30004044f1133f3f 0x230004044f1133f3

def z382 : W := mkw 0x00c4424180460060 0x800c442418046006 0x81cc4647c01f01f7 0x781cc4647c01f01f

def z383 : W := mkw 0x324107ee0220ff8f 0x0324107ee0220ff8 0x900007ff0000ffc4 0x0900007ff0000ffc

def z384 : W := mkw 0x4ffeef603ddf0000 0x04ffeef603ddf000 0xeffffff83fff000f 0xfeffffff83fff000

def z385 : W := mkw 0x201088083bb1ff1f 0x4201088083bb1ff1 0x700000003ff3ff38 0x0700000003ff3ff3

def z386 : W := mkw 0x161b8d863719a981 0x0161b8d863719a98 0xfe3fff873f1ff9cf 0xefe3fff873f1ff9c

def z387 : W := mkw 0x0084400180000000 0x0008440018000000 0x000c4007c0000002 0x0000c4007c000000

def z388 : W := mkw 0x6fbeed283fdfb206 0x06fbeed283fdfb20 0x6ffff9b83fff380b 0xf6ffff9b83fff380

def z389 : W := mkw 0x0b60076000204408 0x00b6007600020440 0xdff007f801e0c60d 0xfdff007f801e0c60

def z390 : W := mkw 0x020005000200a000 0x0020005000200a00 0x900007800000f804 0x0900007800000f80

def z391 : W := mkw 0xc9f47a71e9c70000 0x0c9f47a71e9c7000 0x01f07878c1e30001 0x101f07878c1e3000

def z392 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x6fffb8003eec0000 0xd6fffb8003eec000

def z393 : W := mkw 0x89e4626180000000 0x089e462618000000 0x01c0000000000000 0x101c000000000000

def z394 : W := mkw 0x0010000021000000 0x0001000002100000 0x2030000031000009 0xa203000003100000

def z395 : W := mkw 0x8feffff7d0110911 0x48feffff7d011091 0x8fffffffc0130137 0xf8fffffffc013013

def z396 : W := mkw 0x4dbee8083ddf1b15 0x44dbee8083ddf1b1 0x7ffff8003fff3f3b 0xf7ffff8003fff3f3

def z397 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x01fff80001ff0003 0x101fff80001ff000

def z398 : W := mkw 0x020185841210a901 0x0020185841210a90 0xfe0387843e10f90e 0xefe0387843e10f90

def z399 : W := mkw 0x824117f7c0204468 0x8824117f7c020446 0x900007ffc000c7f4 0x0900007ffc000c7f

def z400 : W := mkw 0x293000082ba0f60e 0x0293000082ba0f60 0x7ff000003fe0fe09 0xf7ff000003fe0fe0

def z401 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x0ff3f9f8c0000001 0x90ff3f9f8c000000

def z402 : W := mkw 0x148fc087945e09e1 0x8148fc087945e09e 0x000fc007c01f01f2 0x0000fc007c01f01f

def z403 : W := mkw 0x29f44269a9e6566e 0x829f44269a9e6566 0xd1fc467fc1ffc7ff 0x7d1fc467fc1ffc7f

def z404 : W := mkw 0x20d44249abe6f66e 0x820d44249abe6f66 0xf1cc4647ffffffff 0x7f1cc4647fffffff

def z405 : W := mkw 0x820115b640000000 0x0820115b64000000 0x000001b800000000 0x0000001b80000000

def z406 : W := mkw 0x2960026008a0440a 0x02960026008a0440 0x01c0000000e00000 0x101c0000000e0000

def z407 : W := mkw 0x2b70076829a0560e 0x02b70076829a0560 0x8ff007f801e00605 0xf8ff007f801e0060

def z408 : W := mkw 0xcffeef63bddf0000 0x0cffeef63bddf000 0xeffffe033fff000b 0xfeffffe033fff000

def z409 : W := mkw 0x0084400000460000 0x0008440000046000 0x41cc000000ec0000 0x541cc000000ec000

def z410 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0xf03ffffff11fffff 0xef03ffffff11ffff

def z411 : W := mkw 0x06cf47c780664468 0x806cf47c78066446 0xdfcfc7c7c1ffc7ff 0xfdfcfc7c7c1ffc7f

def z412 : W := mkw 0x0931989c79911b15 0x40931989c79911b1 0x7ff3f9fcfff33f3f 0xf7ff3f9fcfff33f3

def z413 : W := mkw 0x4d3bb89c7d991b15 0x44d3bb89c7d991b1 0x2e33b9b83e003800 0x82e33b9b83e00380

def z414 : W := mkw 0x4dbee8003dff4468 0x84dbee8003dff446 0x7ffff8003fffc7fb 0xf7ffff8003fffc7f

def z415 : W := mkw 0x8daf7097c0000000 0x08daf7097c000000 0x0ffff807c0000003 0xf0ffff807c000000

def z416 : W := mkw 0x0040024000204408 0x0004002400020440 0xd1c04644c1f3c73f 0x7d1c04644c1f3c73

def z417 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x300001fcf1133f3c 0x0300001fcf1133f3

def z418 : W := mkw 0x224007680220f60e 0x0224007680220f60 0xd1c007f801e0fe0d 0x7d1c007f801e0fe0

def z419 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x2033f9fcf0003807 0xa2033f9fcf000380

def z420 : W := mkw 0x0000000000000000 0x0000000000000000 0x00004004c0130132 0x000004004c013013

def z421 : W := mkw 0x160b8586167eede9 0x8160b8586167eede 0xfe0f87873ffffffe 0xefe0f87873ffffff

def z422 : W := mkw 0x0010181861011214 0x4001018186101121 0x303079f8f1033e3d 0xa303079f8f1033e3

def z423 : W := mkw 0x84cf72d7c0000000 0x084cf72d7c000000 0x81cffe47c0000007 0x781cffe47c000000

def z424 : W := mkw 0x4010080029c70000 0x04010080029c7000 0x0000000001e30000 0x00000000001e3000

def z425 : W := mkw 0x449ff89c755f1b15 0x4449ff89c755f1b1 0x303ff9fcf11f3f3f 0xa303ff9fcf11f3f3

def z426 : W := mkw 0x401088083ddf1b15 0x4401088083ddf1b1 0x700000003fff3f38 0x0700000003fff3f3

def z427 : W := mkw 0x160a85021618a981 0x0160a85021618a98 0xfe0c06033e1cf9c8 0x4fe0c06033e1cf9c

def z428 : W := mkw 0x948ff097d4180981 0x0948ff097d418098 0x000ff807c01c01c2 0x0000ff807c01c01c

def z429 : W := mkw 0x100080001618a981 0x0100080001618a98 0x200000003e003800 0x0200000003e00380

def z430 : W := mkw 0x4dee62418cee4468 0x84dee62418cee446 0xcfcc06030eecc0c0 0x5cfcc06030eecc0c

def z431 : W := mkw 0x8240076380000000 0x0824007638000000 0x8000060300000000 0x0800006030000000

def z432 : W := mkw 0x4dbff8947ddf0911 0x44dbff8947ddf091 0x6ffff804ffff013b 0xf6ffff804ffff013

def z433 : W := mkw 0x49b5f89c79d71b15 0x449b5f89c79d71b1 0x31f3f9fcf1f33f3f 0xb31f3f9fcf1f33f3

def z434 : W := mkw 0x004112ddc0205f7d 0xc004112ddc0205f7 0x900007ffc000fff4 0x0900007ffc000fff

def z435 : W := mkw 0x164b87c79638ede9 0x8164b87c79638ede 0xfe0f87c7fe1cfffe 0xefe0f87c7fe1cfff

def z436 : W := mkw 0x2b3005282b80b206 0x02b3005282b80b20 0xfe3007b83e00f80c 0xefe3007b83e00f80

def z437 : W := mkw 0x220005280200b206 0x0220005280200b20 0x000001b800003800 0x0000001b80000380

def z438 : W := mkw 0x0001109c40001b15 0x40001109c40001b1 0x100041fcc1133f3f 0x2100041fcc1133f3

def z439 : W := mkw 0x12119d9e7311bb95 0x412119d9e7311bb9 0xb033fffff113ffff 0xab033fffff113fff

def z440 : W := mkw 0x4d3aa8003d990000 0x04d3aa8003d99000 0x2e33f8003f13000b 0xa2e33f8003f13000

def z441 : W := mkw 0x848e600380000000 0x0848e60038000000 0x000c000300000000 0x0000c00030000000

def z442 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8fcc07ffc0000004 0x58fcc07ffc000000

def z443 : W := mkw 0x1001008600000981 0x0100100860000098 0x00000007000001c0 0x000000007000001c

def z444 : W := mkw 0x0b70076029800000 0x00b7007602980000 0xeff007f83fe0000d 0xfeff007f83fe0000

def z445 : W := mkw 0x161b8d8e3719bb95 0x4161b8d8e3719bb9 0xfe0f87873f1ffffe 0xefe0f87873f1ffff

def z446 : W := mkw 0x00c4424180664468 0x800c442418066446 0xc1cc4647c0ecc0c7 0x7c1cc4647c0ecc0c

def z447 : W := mkw 0x024007400220e408 0x0024007400220e40 0xffc007c03fe0fe0d 0xfffc007c03fe0fe0

def z448 : W := mkw 0x120105860200a981 0x0120105860200a98 0xd00c0787001cf9ce 0x6d00c0787001cf9c

def z449 : W := mkw 0x040a800014180000 0x0040a80001418000 0x000f8000001c0002 0x0000f8000001c000

def z450 : W := mkw 0x0084400000460000 0x0008440000046000 0xd1cc460701ffc1cf 0x7d1cc460701ffc1c

def z451 : W := mkw 0x161b9d9e7719bb95 0x4161b9d9e7719bb9 0xfe3fbfbf3e1cf9ce 0xefe3fbfbf3e1cf9c

def z452 : W := mkw 0x0001808410100901 0x0000180841010090 0x0003800400100102 0x0000380040010010

def z453 : W := mkw 0x3f6b87e61eb8ed8b 0x03f6b87e61eb8ed8 0xffcf87873efcf9ce 0xfffcf87873efcf9c

def z454 : W := mkw 0x160b05860608a080 0x0160b05860608a08 0xce0f87870e0cc0c6 0xece0f87870e0cc0c

def z455 : W := mkw 0x448ee801945f0060 0x8448ee801945f006 0x000ff807c01f01f2 0x0000ff807c01f01f

def z456 : W := mkw 0x0be4476180664468 0x80be447618066446 0xdffc47ffc1ffc7ff 0xfdffc47ffc1ffc7f

def z457 : W := mkw 0x0dee624180664468 0x80dee62418066446 0xdffffe47c1ffc7ff 0xfdffffe47c1ffc7f

def z458 : W := mkw 0x00c4424180664468 0x800c442418066446 0x01c0000000e00000 0x101c0000000e0000

def z459 : W := mkw 0x0b70076821001204 0x00b7007682100120 0xbff007f831003e0d 0xfbff007f831003e0

def z460 : W := mkw 0x80847011c0000000 0x080847011c000000 0x00007800c0000000 0x000007800c000000

def z461 : W := mkw 0x89f5fafdf1111b15 0x489f5fafdf1111b1 0x31f3f9fcf1133f3f 0xb31f3f9fcf1133f3

def z462 : W := mkw 0x060a050200000000 0x0060a05020000000 0x8e0c060300000000 0x48e0c06030000000

def z463 : W := mkw 0x2bf447682be6f60e 0x02bf447682be6f60 0xfffc47f83ffffe0f 0xffffc47f83ffffe0

def z464 : W := mkw 0x49f46a41a9e74468 0x849f46a41a9e7446 0xd1fc7e47c1ffc7ff 0x7d1fc7e47c1ffc7f

def z465 : W := mkw 0x2b2005200a80a002 0x02b2005200a80a00 0x0e0000000e000000 0x00e0000000e00000

def z466 : W := mkw 0x4fbeed003fdfa000 0x04fbeed003fdfa00 0xffffff803ffff80f 0xfffffff803ffff80

def z467 : W := mkw 0x49b4680029c70000 0x049b4680029c7000 0x6ff078003fe30009 0xf6ff078003fe3000

def z468 : W := mkw 0x5fbeed023fdfa080 0x05fbeed023fdfa08 0xeffffe033fffc0cb 0xfeffffe033fffc0c

def z469 : W := mkw 0x10c4c241967eede9 0x810c4c241967eede 0xf1cc4647ffffffff 0x7f1cc4647fffffff

def z470 : W := mkw 0x8fee676380000000 0x08fee67638000000 0x8fcc4647c0000007 0x78fcc4647c000000

def z471 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0xfffffe073fffc1cf 0xffffffe073fffc1c

def z472 : W := mkw 0x69f46a6829e7560e 0x069f46a6829e7560 0x01f0787801e30601 0x101f0787801e3060

def z473 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00c0603000cc0c0 0x4c00c0603000cc0c

def z474 : W := mkw 0x020005000200a000 0x0020005000200a00 0x2e0001803e003800 0x82e0001803e00380

def z475 : W := mkw 0x8fef77f7c0460000 0x08fef77f7c046000 0xcfffffffc1ff000f 0xfcfffffffc1ff000

def z476 : W := mkw 0x140a80001618a981 0x0140a80001618a98 0x7e0f80003e1cf9ca 0xe7e0f80003e1cf9c

def z477 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xfe0fc7c7ff1fffff 0xefe0fc7c7ff1ffff

def z478 : W := mkw 0xaffffffffbb1ff1f 0x4affffffffbb1ff1 0xfffffffffff3ff3f 0xffffffffffff3ff3

def z479 : W := mkw 0x3fffc7efbffeffef 0x83fffc7efbffeffe 0xffffc7ffffffffff 0xfffffc7fffffffff

def z480 : W := mkw 0x00c4424180000000 0x000c442418000000 0x01c04040c0000001 0x101c04040c000000

def z481 : W := mkw 0x5f3bad863f99a981 0x05f3bad863f99a98 0x2e33b9803e003800 0x82e33b9803e00380

def z482 : W := mkw 0x164b87c61638ed89 0x0164b87c61638ed8 0xffcf87c73ffcffcf 0xfffcf87c73ffcffc

def z483 : W := mkw 0x8feff7f7d4180000 0x08feff7f7d418000 0xeffffffffe1c000f 0xfeffffffffe1c000

def z484 : W := mkw 0x4dfeea403dff4408 0x04dfeea403dff440 0xfffffe403fffc60f 0xffffffe403fffc60

def z485 : W := mkw 0x0000000000460000 0x0000000000046000 0x4000000001ff0008 0x04000000001ff000

def z486 : W := mkw 0x8fef77f7c200a000 0x08fef77f7c200a00 0xfffffffffe00f80f 0xffffffffffe00f80

def z487 : W := mkw 0x1f3b85863f98a981 0x01f3b85863f98a98 0xffff87873ffcf9cf 0xfffff87873ffcf9c

def z488 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0x0e33f9fcc0000007 0xa0e33f9fcc000000

def z489 : W := mkw 0x401088003dff4468 0x8401088003dff446 0x700000003fffc7f8 0x0700000003fffc7f

def z490 : W := mkw 0xcfff7ff7e9c70000 0x0cfff7ff7e9c7000 0x8fffffffc1e30007 0xf8fffffffc1e3000

def z491 : W := mkw 0x6fee67600eeee40a 0x06fee67600eeee40 0xcfcc06000eecc000 0x5cfcc06000eecc00

def z492 : W := mkw 0x060b858614180000 0x0060b85861418000 0xee0f87873e1c000e 0xeee0f87873e1c000

def z493 : W := mkw 0x0001989c50111b15 0x40001989c50111b1 0x1003f9fcc0133f36 0x01003f9fcc0133f3

def z494 : W := mkw 0x848f7097c0460060 0x8848f7097c046006 0x000ff807c01f01f2 0x0000ff807c01f01f

def z495 : W := mkw 0x0011808c31101b05 0x00011808c31101b0 0x303381fc31103f0f 0xa303381fc31103f0

def z496 : W := mkw 0x8be577f7c0000000 0x08be577f7c000000 0x81f07fffc0000005 0x181f07fffc000000

def z497 : W := mkw 0x00c552ddc0665f7d 0xc00c552ddc0665f7 0xd1cc47ffc1ffffff 0x7d1cc47ffc1fffff

def z498 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x2ff3f8003fe30001 0x92ff3f8003fe3000

def z499 : W := mkw 0x4dfffaddfdff5f7d 0xc4dfffaddfdff5f7 0xffffffffffffffff 0xffffffffffffffff

def z500 : W := mkw 0x0000000000000000 0x0000000000000000 0x300001803000380c 0xa300001803000380

def z501 : W := mkw 0x0084400180460060 0x8008440018046006 0x100c4047c11f07ff 0x2100c4047c11f07f

def z502 : W := mkw 0x160b05860200a981 0x0160b05860200a98 0x9e0f87870000f9c6 0xe9e0f87870000f9c

def z503 : W := mkw 0x82519ffff1111b15 0x482519ffff1111b1 0xb033fffff1133f3f 0xab033fffff1133f3

def z504 : W := mkw 0x160a05020608a080 0x0160a05020608a08 0xfe0c07833e0cf8cc 0xefe0c07833e0cf8c

def z505 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfffc07ff3ffcffcf 0xffffc07ff3ffcffc

def z506 : W := mkw 0x0000000000000000 0x0000000000000000 0x800c060700000006 0x6800c06070000000

def z507 : W := mkw 0x224007698220f66e 0x8224007698220f66 0x900007ffc000fff4 0x0900007ffc000fff

def z508 : W := mkw 0x1011989c7719bb95 0x41011989c7719bb9 0x7033f9fcff1fffff 0xa7033f9fcff1ffff

def z509 : W := mkw 0x00c4424180204408 0x000c442418020440 0xd1cc4647c1e0c60f 0x7d1cc4647c1e0c60

def z510 : W := mkw 0x8fef77f7c0204468 0x88fef77f7c020446 0x9fffffffc000c7f7 0xf9fffffffc000c7f

def z511 : W := mkw 0xdffffff7ffdfa981 0x0dffffff7ffdfa98 0xfffffffffffff9cf 0xffffffffffffff9c

def z512 : W := mkw 0x2be447618ae6e46a 0x82be447618ae6e46 0xdfcc4647cfffc7ff 0x7dfcc4647cfffc7f

def z513 : W := mkw 0x0040024000204408 0x0004002400020440 0x900006400000c604 0x0900006400000c60

def z514 : W := mkw 0x849ff89ff1111b15 0x4849ff89ff1111b1 0x303ff9fff1133f3f 0xa303ff9fff1133f3

def z515 : W := mkw 0x8fff77ffe1001204 0x08fff77ffe100120 0xbffffffff1003e0f 0xfbffffffff1003e0

def z516 : W := mkw 0x161b9d9e7719bb95 0x4161b9d9e7719bb9 0x3e33f9fcff133f3f 0xa3e33f9fcff133f3

def z517 : W := mkw 0x168fc586165ea981 0x0168fc586165ea98 0xffcfc7873ffff9cf 0xfffcfc7873ffff9c

def z518 : W := mkw 0x02c447418266e468 0x802c447418266e46 0xffcc47c7ffffffff 0xfffcc47c7fffffff

def z519 : W := mkw 0x120185861210a981 0x0120185861210a98 0xb00387873010f9ce 0xab00387873010f9c

def z520 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x2033f9bcf0133932 0x82033f9bcf013393

def z521 : W := mkw 0x89e47271c0664468 0x889e47271c066446 0xd1fc7e7fc1ffc7ff 0x7d1fc7e7fc1ffc7f

def z522 : W := mkw 0x00c4424180664468 0x800c442418066446 0x900c4647c01fc7f6 0x0900c4647c01fc7f

def z523 : W := mkw 0x4dae60000cce0000 0x04dae60000cce000 0x4fcc40000fff000b 0x74fcc40000fff000

def z524 : W := mkw 0x0000000000000000 0x0000000000000000 0x900006070000c1c4 0x0900006070000c1c

def z525 : W := mkw 0x10008000167eede9 0x810008000167eede 0x700000003ffffff8 0x0700000003ffffff

def z526 : W := mkw 0x09a4600000000000 0x009a460000000000 0x01f0780000000001 0x101f078000000000

def z527 : W := mkw 0x16ce4743866ee4e8 0x816ce4743866ee4e 0xdfcc4647cfffc7ff 0x7dfcc4647cfffc7f

def z528 : W := mkw 0x8dee7271c0000000 0x08dee7271c000000 0x0ffff878c0000003 0xf0ffff878c000000

def z529 : W := mkw 0x4dbee8083ddf1204 0x04dbee8083ddf120 0x7ffff9f83fff3e0f 0xf7ffff9f83fff3e0

def z530 : W := mkw 0x440aa80014190000 0x0440aa8001419000 0x0003b80000000000 0x00003b8000000000

def z531 : W := mkw 0x201000082b80b206 0x0201000082b80b20 0x200000003e003800 0x0200000003e00380

def z532 : W := mkw 0x0040024180204468 0x8004002418020446 0xd00c0647c01cc7fe 0x6d00c0647c01cc7f

def z533 : W := mkw 0x0000000000000000 0x0000000000000000 0x100000400100060d 0x2100000400100060

def z534 : W := mkw 0x0000000000664468 0x8000000000066446 0x4000000000ecc0c0 0x04000000000ecc0c

def z535 : W := mkw 0x449ee800355f0000 0x0449ee800355f000 0x203ff800311f000b 0xa203ff800311f000

def z536 : W := mkw 0x0000000000204408 0x0000000000020440 0x5000000001e0c608 0x05000000001e0c60

def z537 : W := mkw 0x2010000829a0560e 0x02010000829a0560 0x0000000001e00600 0x00000000001e0060

def z538 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8fffbfbb00000000 0xd8fffbfbb0000000

def z539 : W := mkw 0x040a000004080000 0x0040a00000408000 0x4e0c00000e0c0000 0x44e0c00000e0c000

def z540 : W := mkw 0x00c4424180664468 0x800c442418066446 0xc1cc460301ffc0cb 0x7c1cc460301ffc0c

def z541 : W := mkw 0x16cfc7c79618a981 0x016cfc7c79618a98 0xffcfc7c7fe1cf9cf 0xfffcfc7c7fe1cf9c

def z542 : W := mkw 0x00d45a59e167567c 0xc00d45a59e167567 0x01f07878c1e30631 0x101f07878c1e3063

def z543 : W := mkw 0x060b858610100901 0x0060b85861010090 0xbe0f87873010390e 0xebe0f87873010390

def z544 : W := mkw 0x140b80861618a981 0x0140b80861618a98 0x700f80073e1cf9ca 0x0700f80073e1cf9c

def z545 : W := mkw 0x49b4e80039d70000 0x049b4e80039d7000 0x21f3f80031f3000b 0xb21f3f80031f3000

def z546 : W := mkw 0x0000101040000000 0x0000010104000000 0x00307878c0000001 0x000307878c000000

def z547 : W := mkw 0x1000800014180981 0x0100080001418098 0x00000000001c01c0 0x000000000001c01c

def z548 : W := mkw 0x4daee8001cdf0000 0x04daee8001cdf000 0x4fcff8000eff0002 0x54fcff8000eff000

def z549 : W := mkw 0x29719afc79b15f1f 0x429719afc79b15f1 0x31f3f9fcf1f33f3f 0xb31f3f9fcf1f33f3

def z550 : W := mkw 0x5dbee8003fdfa981 0x05dbee8003fdfa98 0x7ffff8003ffff9cb 0xf7ffff8003ffff9c

def z551 : W := mkw 0x89f47a79e1011214 0x489f47a79e101121 0x01f07878c1030631 0x101f07878c103063

def z552 : W := mkw 0x0010181861011214 0x4001018186101121 0x0030383800000000 0x0003038380000000

def z553 : W := mkw 0x2b7007602ba0e40a 0x02b7007602ba0e40 0xeff006003fe0c009 0xfeff006003fe0c00

def z554 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x0033f87cc1130733 0x00033f87cc113073

def z555 : W := mkw 0x160a05020608a080 0x0160a05020608a08 0x0e0000000e000000 0x00e0000000e00000

def z556 : W := mkw 0x0040024000204408 0x0004002400020440 0xc1c0060000e0c000 0x5c1c0060000e0c00

def z557 : W := mkw 0x3f7b87ee3fb8ff8f 0x03f7b87ee3fb8ff8 0xfff387f83fe0fe0d 0xffff387f83fe0fe0

def z558 : W := mkw 0x0960026000000000 0x0096002600000000 0x01f0007800000001 0x101f000780000000

def z559 : W := mkw 0x80401271c0000000 0x080401271c000000 0x00000078c0000000 0x000000078c000000

def z560 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0x7e0381803e1cf9c8 0x87e0381803e1cf9c

def z561 : W := mkw 0x448ee800145f0000 0x0448ee800145f000 0x6e0ff8003e1f000a 0xe6e0ff8003e1f000

def z562 : W := mkw 0xabf47779eba0f60e 0x0abf47779eba0f60 0xfff07ff8ffe0fe0d 0xffff07ff8ffe0fe0

def z563 : W := mkw 0x0000181040010010 0x4000018104001001 0x00007800c0030030 0x000007800c003003

def z564 : W := mkw 0x6ffffffc7fffff1f 0x46ffffffc7fffff1 0xfffffffcffffff3f 0xffffffffcffffff3

def z565 : W := mkw 0x9fee67638608a080 0x09fee67638608a08 0xcfcc06030e0cc0c0 0x5cfcc06030e0cc0c

def z566 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x3003f804f1133f3a 0x03003f804f1133f3

def z567 : W := mkw 0x0084400000000000 0x0008440000000000 0x01cc400000000003 0x701cc40000000000

def z568 : W := mkw 0x161b9d9e7719bb95 0x4161b9d9e7719bb9 0x2e33b9b83e003800 0x82e33b9b83e00380

def z569 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c0007001c01c2 0x0000c0007001c01c

def z570 : W := mkw 0x8f2a252200000000 0x08f2a25220000000 0x0e00000000000000 0x00e0000000000000

def z571 : W := mkw 0x225007682ba0f60e 0x0225007682ba0f60 0xf00007f83fe0fe0c 0x0f00007f83fe0fe0

def z572 : W := mkw 0x0201058600000000 0x0020105860000000 0x8000078700000004 0x0800007870000000

def z573 : W := mkw 0x0d3a80003d980000 0x00d3a80003d98000 0x6fff80003ffc000b 0xf6fff80003ffc000

def z574 : W := mkw 0x82c557f7c0664468 0x882c557f7c066446 0xd1cc47ffc1ffc7ff 0x7d1cc47ffc1ffc7f

def z575 : W := mkw 0x00d4ca41b1774468 0x800d4ca41b177446 0xf1fffe47f1ffc7ff 0xff1fffe47f1ffc7f

def z576 : W := mkw 0x0095d89c71571b15 0x40095d89c71571b1 0x71fff9fcf1ff3f3f 0xf71fff9fcf1ff3f3

def z577 : W := mkw 0x00c4424180664468 0x800c442418066446 0x91c04647c1e3c7f5 0x191c04647c1e3c7f

def z578 : W := mkw 0x0920000008800000 0x0092000000880000 0x4fc000000ee00000 0x54fc000000ee0000

def z579 : W := mkw 0x2be447618ae6e46a 0x82be447618ae6e46 0xcfcc06030eecc0c0 0x5cfcc06030eecc0c

def z580 : W := mkw 0x0040024180204468 0x8004002418020446 0xd1c00647c1e0c7fd 0x7d1c00647c1e0c7f

def z581 : W := mkw 0x0000000000000000 0x0000000000000000 0xd00c4647c11fc7ff 0x6d00c4647c11fc7f

def z582 : W := mkw 0x0001008400000000 0x0000100840000000 0x0003818400000006 0xa000381840000000

def z583 : W := mkw 0x0000000180000060 0x8000000018000006 0x00000007c00001f0 0x000000007c00001f

def z584 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0x6e0f81803e1c380a 0xe6e0f81803e1c380

def z585 : W := mkw 0x3f3b85ae3f98bb87 0x03f3b85ae3f98bb8 0x2e3381b83e003800 0x82e3381b83e00380

def z586 : W := mkw 0x1fafe5861618a981 0x01fafe5861618a98 0xffffff873e1cf9cf 0xfffffff873e1cf9c

def z587 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xce0f86070e1cc1c2 0x4ce0f86070e1cc1c

def z588 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xffc006003fe0fe08 0x5ffc006003fe0fe0

def z589 : W := mkw 0x0000000000000000 0x0000000000000000 0x6e0000003e000008 0xe6e0000003e00000

def z590 : W := mkw 0x00c4424180460000 0x000c442418046000 0xc1cc4647c1ff000f 0x7c1cc4647c1ff000

def z591 : W := mkw 0x1201159e4200bb95 0x41201159e4200bb9 0x900007ffc000fff4 0x0900007ffc000fff

def z592 : W := mkw 0x040b808414180901 0x0040b80841418090 0x7e0f81843e1c390e 0xe7e0f81843e1c390

def z593 : W := mkw 0x00d5daddf1775f7d 0xc00d5daddf1775f7 0x31f3f9fcf1f33f3f 0xb31f3f9fcf1f33f3

def z594 : W := mkw 0x0010880031110000 0x0001088003111000 0x2033b80030000000 0x82033b8003000000

def z595 : W := mkw 0x00c4424180000000 0x000c442418000000 0x91cc4647c113073f 0x791cc4647c113073

def z596 : W := mkw 0x0084400180460060 0x8008440018046006 0x00004000c0030030 0x000004000c003003

def z597 : W := mkw 0x224007680220f60e 0x0224007680220f60 0xfe0007f83e00fe0c 0xefe0007f83e00fe0

def z598 : W := mkw 0x6b708f683ffff60e 0x06b708f683ffff60 0xfff007f83ffffe0d 0xffff007f83ffffe0

def z599 : W := mkw 0x0040024000204408 0x0004002400020440 0xd1cc064701fcc7cf 0x7d1cc064701fcc7c

def z600 : W := mkw 0x9f2bb5b65618a981 0x09f2bb5b65618a98 0x2e33b9b83e003800 0x82e33b9b83e00380

def z601 : W := mkw 0x2b6007600aa0e40a 0x02b6007600aa0e40 0xdfc006400fe0c60d 0x7dfc006400fe0c60

def z602 : W := mkw 0x00c4424180664468 0x800c442418066446 0xc1cc4643c1efc6f1 0x5c1cc4643c1efc6f

def z603 : W := mkw 0x22519ffc7331ff1f 0x422519ffc7331ff1 0xb033fffcf113ff3f 0xab033fffcf113ff3

def z604 : W := mkw 0x120005020200a080 0x0120005020200a08 0x800006030000c0c0 0x0800006030000c0c

def z605 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0x3e0381843e10390e 0xa3e0381843e10390

def z606 : W := mkw 0x5fafe5861edea981 0x05fafe5861edea98 0xffcf87873efcf9ce 0xfffcf87873efcf9c

def z607 : W := mkw 0x0b719ffc71111b15 0x40b719ffc71111b1 0xbff3fffcf1133f3f 0xfbff3fffcf1133f3

def z608 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xcff006780fe0c601 0x5cff006780fe0c60

def z609 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x3033b9f831003e0d 0xa3033b9f831003e0

def z610 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000000001130738 0x0100000000113073

def z611 : W := mkw 0x0000000000460060 0x8000000000046006 0x00000000001f01f0 0x000000000001f01f

def z612 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x2e3ff8003e1f0002 0x82e3ff8003e1f000

def z613 : W := mkw 0x0084400000460000 0x0008440000046000 0x000c4000001f0002 0x0000c4000001f000

def z614 : W := mkw 0x021005082300b204 0x0021005082300b20 0xfe3007f83f00fe0d 0xefe3007f83f00fe0

def z615 : W := mkw 0x0010880831111204 0x0001088083111120 0x3033f9f831133e0f 0xa3033f9f831133e0

def z616 : W := mkw 0x0040024180204468 0x8004002418020446 0x90004647c113c7ff 0x290004647c113c7f

def z617 : W := mkw 0x4d3aa8003d990000 0x04d3aa8003d99000 0x6e3fb8003e1c000a 0xe6e3fb8003e1c000

def z618 : W := mkw 0x5fffefc7bfffede9 0x85fffefc7bfffede 0xffffffc7ffffffff 0xfffffffc7fffffff

def z619 : W := mkw 0x8faf75b640000000 0x08faf75b64000000 0x0ffff9b800000003 0xf0ffff9b80000000

def z620 : W := mkw 0x548fe886145f0981 0x0548fe886145f098 0x000ff807001f01c2 0x0000ff807001f01c

def z621 : W := mkw 0x400000000cce0000 0x0400000000cce000 0x400000000eec0000 0x0400000000eec000

def z622 : W := mkw 0x141b989e75191b95 0x4141b989e75191b9 0x303ff9fff11f3fff 0xa303ff9fff11f3ff

def z623 : W := mkw 0x00c4424180664468 0x800c442418066446 0x81cc4647c1e30637 0x781cc4647c1e3063

def z624 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xfe0387803e00f80c 0xefe0387803e00f80

def z625 : W := mkw 0x0040024180664468 0x8004002418066446 0xd0000647c1ffc7fc 0x0d0000647c1ffc7f

def z626 : W := mkw 0x100080001618a981 0x0100080001618a98 0xf00c06073e1cf9ce 0x6f00c06073e1cf9c

def z627 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0x900f8787001cf9c6 0x0900f8787001cf9c

def z628 : W := mkw 0x4084680000470000 0x0408468000047000 0x0000780000030000 0x0000078000003000

def z629 : W := mkw 0x8fee676380000000 0x08fee67638000000 0x8ffffe0300000003 0xf8ffffe030000000

def z630 : W := mkw 0x2bf5dffdfbf7ff7f 0xc2bf5dffdfbf7ff7 0xffffffffffffffff 0xffffffffffffffff

def z631 : W := mkw 0x0000000000204468 0x8000000000020446 0x100000000000c7f0 0x0100000000000c7f

def z632 : W := mkw 0xcfee67638cce0000 0x0cfee67638cce000 0xcfcc06030eec0000 0x5cfcc06030eec000

def z633 : W := mkw 0x2970026829a0560e 0x02970026829a0560 0x31f001f831e03e0d 0xb31f001f831e03e0

def z634 : W := mkw 0x200000000aa0e40a 0x0200000000aa0e40 0x400000000ee0c000 0x0400000000ee0c00

def z635 : W := mkw 0x4dfeea41bdff4468 0x84dfeea41bdff446 0x6ffff840ffff063b 0xf6ffff840ffff063

def z636 : W := mkw 0x0010000821001204 0x0001000082100120 0x0030007801000601 0x0003000780100060

def z637 : W := mkw 0x0011189c61011214 0x40011189c6101121 0x0033f9fcc1030637 0xa0033f9fcc103063

def z638 : W := mkw 0x6f3aad283f99b206 0x06f3aad283f99b20 0x2e33b9b83e003800 0x82e33b9b83e00380

def z639 : W := mkw 0x120105860200a981 0x0120105860200a98 0x0000018000003800 0x0000001800000380

def z640 : W := mkw 0x060b05860200a000 0x0060b05860200a00 0xfe0f87873e00f80e 0xefe0f87873e00f80

def z641 : W := mkw 0x0200050000000000 0x0020005000000000 0x8e00078000000004 0xe8e0007800000000

def z642 : W := mkw 0x100000000608a080 0x0100000000608a08 0x400000000e0cc0c0 0x0400000000e0cc0c

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0x00004040c1030631 0x000004040c103063

def z644 : W := mkw 0x0000880010110911 0x4000088001011091 0x0000000000130130 0x0000000000013013

def z645 : W := mkw 0x4dbe680029c70000 0x04dbe680029c7000 0x0ffff80001e30003 0xf0ffff80001e3000

def z646 : W := mkw 0x4daee800145f0000 0x04daee800145f000 0x0ffff800001f0003 0xf0ffff800001f000

def z647 : W := mkw 0x4dbff89c7ddf1b15 0x44dbff89c7ddf1b1 0x6ffff9b83fff380b 0xf6ffff9b83fff380

def z648 : W := mkw 0x0084400000460000 0x0008440000046000 0x01c0400001e30001 0x101c0400001e3000

def z649 : W := mkw 0x840b309640000000 0x0840b30964000000 0x0003b80000000000 0x00003b8000000000

def z650 : W := mkw 0x2b701f786ba1f61e 0x42b701f786ba1f61 0xfff07ff8ffe3fe3d 0xffff07ff8ffe3fe3

def z651 : W := mkw 0x0000000000000000 0x0000000000000000 0x400c0000001c000a 0x6400c0000001c000

def z652 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x3033f80031133f3b 0xa3033f80031133f3

def z653 : W := mkw 0x0010880031110000 0x0001088003111000 0x2000000031130008 0x0200000003113000

def z654 : W := mkw 0x848ff897d0110911 0x4848ff897d011091 0x000ff807c0130132 0x0000ff807c013013

def z655 : W := mkw 0x0010080821011214 0x4001008082101121 0x0000000001030630 0x0000000000103063

def z656 : W := mkw 0x8b6117f7c0000000 0x08b6117f7c000000 0x8ff007ffc0000005 0xf8ff007ffc000000

def z657 : W := mkw 0x5fae65020ecea080 0x05fae65020ecea08 0xcfcc06030eecc0c0 0x5cfcc06030eecc0c

def z658 : W := mkw 0x0084400180460060 0x8008440018046006 0x41cc4007c1ff01fb 0x741cc4007c1ff01f

def z659 : W := mkw 0x493088003ddf0000 0x0493088003ddf000 0x6ff000003fff0009 0xf6ff000003fff000

def z660 : W := mkw 0x89e47271c0000000 0x089e47271c000000 0x81fc7e7fc0000007 0x781fc7e7fc000000

def z661 : W := mkw 0x048e600000000000 0x0048e60000000000 0x000ff80000000002 0x0000ff8000000000

def z662 : W := mkw 0x00519adc71315f1d 0x400519adc71315f1 0xf1f3fffcf1f3ff3f 0xff1f3fffcf1f3ff3

def z663 : W := mkw 0x86cf77f7c0000000 0x086cf77f7c000000 0x800fffffc0000006 0x0800fffffc000000

def z664 : W := mkw 0x0000000000000000 0x0000000000000000 0x000040000113000b 0x2000040000113000

def z665 : W := mkw 0x12c547c78266ede9 0x812c547c78266ede 0xd1cc47c7c1ffffff 0x7d1cc47c7c1fffff

def z666 : W := mkw 0x0001909c50101b15 0x40001909c50101b1 0x300381fcf0103f3e 0xa300381fcf0103f3

def z667 : W := mkw 0x40d4ca41bdff4468 0x840d4ca41bdff446 0xf1cc4647ffffc7ff 0x7f1cc4647ffffc7f

def z668 : W := mkw 0x2bf44769abe6f66e 0x82bf44769abe6f66 0xfffc07fb3fecfecd 0xffffc07fb3fecfec

def z669 : W := mkw 0x00c4424180664468 0x800c442418066446 0xc1cc4607c0ffc1f2 0x5c1cc4607c0ffc1f

def z670 : W := mkw 0x0010880031110000 0x0001088003111000 0x3033f844f113073f 0xa3033f844f113073

def z671 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x3033b9b831133f38 0x83033b9b831133f3

def z672 : W := mkw 0x297002682ba0f60e 0x0297002682ba0f60 0x71f000783fe0fe09 0x171f000783fe0fe0

def z673 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x303001f831133f3d 0xa303001f831133f3

def z674 : W := mkw 0x160b959e5618bb95 0x4160b959e5618bb9 0xfe0f87fffe1cfffe 0xefe0f87fffe1cfff

def z675 : W := mkw 0x2930002829801206 0x0293000282980120 0x0030003800000000 0x0003000380000000

def z676 : W := mkw 0x0085d895d0570971 0xc0085d895d057097 0x000ff807c01f01f2 0x0000ff807c01f01f

def z677 : W := mkw 0x6ffeef603fffe40a 0x06ffeef603fffe40 0xeffffe003fffc00b 0xfeffffe003fffc00

def z678 : W := mkw 0x048ec000145e0000 0x0048ec000145e000 0x6fcfc0003fff000b 0xf6fcfc0003fff000

def z679 : W := mkw 0x00c4424180664468 0x800c442418066446 0xd1c04640c1e3c63d 0x7d1c04640c1e3c63

def z680 : W := mkw 0x100000000200a981 0x0100000000200a98 0x100000000000f9c0 0x0100000000000f9c

def z681 : W := mkw 0x2ffe67682ba0f60e 0x02ffe67682ba0f60 0xfffffff83fe0fe0f 0xffffffff83fe0fe0

def z682 : W := mkw 0x4011989c7ddf1b15 0x44011989c7ddf1b1 0x7033f9fcffff3f3f 0xa7033f9fcffff3f3

def z683 : W := mkw 0x824117ffc0001b15 0x4824117ffc0001b1 0x900007ffc0003f34 0x0900007ffc0003f3

def z684 : W := mkw 0x968ff597d618a981 0x0968ff597d618a98 0xfe0fff87fe1cf9ce 0xefe0fff87fe1cf9c

def z685 : W := mkw 0x00c4424180000000 0x000c442418000000 0x81cc060300000000 0x581cc06030000000

def z686 : W := mkw 0x0000000000000000 0x0000000000000000 0x100000040010010e 0x2100000040010010

def z687 : W := mkw 0x160b05860608a981 0x0160b05860608a98 0xde0c07870e0cf9c4 0x4de0c07870e0cf9c

def z688 : W := mkw 0x49b4781869c71214 0x449b4781869c7121 0x01f07878c1e30631 0x101f07878c1e3063

def z689 : W := mkw 0xcfeffff7d45f0000 0x0cfeffff7d45f000 0x8fffffffc01f0007 0xf8fffffffc01f000

def z690 : W := mkw 0x140b808614180981 0x0140b80861418098 0xd00f8607001cc1ce 0x6d00f8607001cc1c

def z691 : W := mkw 0x16ce4743866ee4e8 0x816ce4743866ee4e 0xcfcc06030eecc0c0 0x5cfcc06030eecc0c

def z692 : W := mkw 0x4930280029810000 0x0493028002981000 0x0030380000000000 0x0003038000000000

def z693 : W := mkw 0x0920000000000000 0x0092000000000000 0x0ff0000000000001 0xf0ff000000000000

def z694 : W := mkw 0x225007682320f60e 0x0225007682320f60 0xb03007f83100fe0d 0xab03007f83100fe0

def z695 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0x2e0f81873e1c39c2 0x82e0f81873e1c39c

def z696 : W := mkw 0x2b7007682be6f66e 0x82b7007682be6f66 0xfff007f83ffffffd 0xffff007f83ffffff

def z697 : W := mkw 0x8ffffff7f1110000 0x08ffffff7f111000 0xaffffffff113000f 0xfaffffffff113000

def z698 : W := mkw 0x0000800014180000 0x0000080001418000 0x600000003e1c0008 0x0600000003e1c000

def z699 : W := mkw 0x00c4424000664408 0x000c442400066440 0xd1cc464001ffc60f 0x7d1cc464001ffc60

def z700 : W := mkw 0x22c447698266f66e 0x822c447698266f66 0xd1cc47ffc1ffffff 0x7d1cc47ffc1fffff

def z701 : W := mkw 0xcf3bbdb67d990000 0x0cf3bbdb67d99000 0x2e33b9b83e000000 0x82e33b9b83e00000

def z702 : W := mkw 0x00c4424180664468 0x800c442418066446 0xd1cc064301ecc6cd 0x7d1cc064301ecc6c

def z703 : W := mkw 0x100180841618a981 0x0100180841618a98 0x700381843e1cf9ce 0xa700381843e1cf9c

def z704 : W := mkw 0x120185861618a981 0x0120185861618a98 0xf00007873e1cf9cc 0x0f00007873e1cf9c

def z705 : W := mkw 0x0001989450110911 0x4000198945011091 0x0003b80000000000 0x00003b8000000000

def z706 : W := mkw 0x124107c78220ede9 0x8124107c78220ede 0x900007c7c000fff4 0x0900007c7c000fff

def z707 : W := mkw 0x0dbe600029c60000 0x00dbe600029c6000 0x6ffff8003fff000b 0xf6ffff8003fff000

def z708 : W := mkw 0x0011989c75191b15 0x40011989c75191b1 0x7033f9fcff1f3f3f 0xa7033f9fcff1f3f3

def z709 : W := mkw 0x4dbee8083ddf1204 0x04dbee8083ddf120 0x6ffff9b83fff380b 0xf6ffff9b83fff380

def z710 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x6ff3f8003fff0009 0x96ff3f8003fff000

def z711 : W := mkw 0x160a05020608a080 0x0160a05020608a08 0xee0c07833e0cf8c0 0xcee0c07833e0cf8c

def z712 : W := mkw 0x4dbee8083ddf1b15 0x44dbee8083ddf1b1 0x7ffff9f83fff3f3f 0xf7ffff9f83fff3f3

def z713 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xfe3fff873e1cf9cf 0xefe3fff873e1cf9c

def z714 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xfe0fc7c7fe1cf9cf 0xefe0fc7c7fe1cf9c

def z715 : W := mkw 0x0000000000000000 0x0000000000000000 0x0033f9f800000007 0xa0033f9f80000000

def z716 : W := mkw 0x8ffeef6bb1111b15 0x48ffeef6bb1111b1 0xbfcc060331133f38 0x5bfcc060331133f3

def z717 : W := mkw 0x8fef77f7c0460060 0x88fef77f7c046006 0xdfffffffc01fc1ff 0xfdfffffffc01fc1f

def z718 : W := mkw 0x4010880839d71b15 0x44010880839d71b1 0x3000000031f33f38 0x03000000031f33f3

def z719 : W := mkw 0x2b619ff45ab1ed1b 0x42b619ff45ab1ed1 0xcfc3fe04cef3c132 0x5cfc3fe04cef3c13

def z720 : W := mkw 0x9fef77f7c266ede9 0x89fef77f7c266ede 0xdfffffffc1ffffff 0xfdfffffffc1fffff

def z721 : W := mkw 0x2b700769aba0f66e 0x82b700769aba0f66 0xfff007fb3fe0fecd 0xffff007fb3fe0fec

def z722 : W := mkw 0x0010880831775f7d 0xc0010880831775f7 0x3000000031f33f38 0x03000000031f33f3

def z723 : W := mkw 0x0b3005082b80b204 0x00b3005082b80b20 0xfff007f83fe0fe0d 0xffff007f83fe0fe0

def z724 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0xcfffffffc0ffc1f7 0xfcfffffffc0ffc1f

def z725 : W := mkw 0x601088083fb9f60e 0x0601088083fb9f60 0x700000003fe0fe08 0x0700000003fe0fe0

def z726 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x7ffff8403fff060f 0xf7ffff8403fff060

def z727 : W := mkw 0x8def72f7c0000000 0x08def72f7c000000 0x01fff9ffc0000007 0xb01fff9ffc000000

def z728 : W := mkw 0xcfef77f7cc880000 0x0cfef77f7cc88000 0x8fffffffce000007 0xf8fffffffce00000

def z729 : W := mkw 0x8fef77f7c0204468 0x88fef77f7c020446 0x9fffffffc113c7ff 0xf9fffffffc113c7f

def z730 : W := mkw 0x160a85021618a981 0x0160a85021618a98 0xfe0c07833e1cf9cc 0xefe0c07833e1cf9c

def z731 : W := mkw 0x9fef77f7c200a981 0x09fef77f7c200a98 0xdfffffffc01cf9cf 0xfdfffffffc01cf9c

def z732 : W := mkw 0x89e572f5c0000000 0x089e572f5c000000 0x01f3f87cc0000003 0x101f3f87cc000000

def z733 : W := mkw 0x4daf709c4cce1b15 0x44daf709c4cce1b1 0x5fcc01fcceec3f34 0x55fcc01fcceec3f3

def z734 : W := mkw 0x0001109440000000 0x0000110944000000 0xd03fffffc01cc1cf 0xed03fffffc01cc1c

def z735 : W := mkw 0x89e47271c0000000 0x089e47271c000000 0x01f3f878c0000003 0xb01f3f878c000000

def z736 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x2000000031033e30 0x02000000031033e3

def z737 : W := mkw 0x004112d440000000 0x0004112d44000000 0x81f3fffcc0000007 0xf81f3fffcc000000

def z738 : W := mkw 0x2b7007682ba0f66e 0x82b7007682ba0f66 0xfff007f83fe0fffd 0xffff007f83fe0fff

def z739 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xfe0f87c73f1cffcf 0xefe0f87c73f1cffc

def z740 : W := mkw 0x4dae60000cce0000 0x04dae60000cce000 0x4ffff8000fff000b 0xf4ffff8000fff000

def z741 : W := mkw 0x161a1d1a6709b294 0x4161a1d1a6709b29 0xce3c7e7bcf0fc6f1 0x4ce3c7e7bcf0fc6f

def z742 : W := mkw 0x4dbee8083ddf1204 0x04dbee8083ddf120 0x6ffff8783fff060b 0xf6ffff8783fff060

def z743 : W := mkw 0x004112d5c0000000 0x0004112d5c000000 0x8033ffffc0000007 0xa8033ffffc000000

def z744 : W := mkw 0xcfef77f7c8c60000 0x0cfef77f7c8c6000 0x8fffffffc0e00007 0xf8fffffffc0e0000

def z745 : W := mkw 0x8f2b35b640664468 0x88f2b35b64066446 0x5e33b9b801ffc7f8 0x85e33b9b801ffc7f

def z746 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x3000018031133f3c 0xa3000018031133f3

def z747 : W := mkw 0x448ee800145f0000 0x0448ee800145f000 0x6fcff8003fff000b 0xf6fcff8003fff000

def z748 : W := mkw 0x66ceef68167ff60e 0x066ceef68167ff60 0x900ffff8001ffe06 0x0900ffff8001ffe0

def z749 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x6ffff8073fff01cb 0xf6ffff8073fff01c

def z750 : W := mkw 0x00d5daddf1775f7d 0xc00d5daddf1775f7 0xe1ffbfbb30ecf8c0 0xde1ffbfbb30ecf8c

def z751 : W := mkw 0x0fee676000664408 0x00fee67600066440 0xdffffff801ffc60f 0xfdffffff801ffc60

def z752 : W := mkw 0x4d3aa8003d990000 0x04d3aa8003d99000 0x6fffb8003ffc000b 0xf6fffb8003ffc000

def z753 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0xcfffffffc01c000f 0xfcfffffffc01c000

def z754 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfff007f83ee0fe04 0xdfff007f83ee0fe0

def z755 : W := mkw 0x8faf75b7c0000000 0x08faf75b7c000000 0x0e3ff9ffc0000007 0xa0e3ff9ffc000000

def z756 : W := mkw 0x8fef77f7c8800000 0x08fef77f7c880000 0xcfffffffcee00007 0xfcfffffffcee0000

def z757 : W := mkw 0x00508a4831315f1d 0x400508a4831315f1 0xf1c0064031f3ff3d 0x7f1c0064031f3ff3

def z758 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x2000000030133930 0x0200000003013393

def z759 : W := mkw 0x4dbee801bddf0060 0x84dbee801bddf006 0x6ffff800ffff003b 0xf6ffff800ffff003

def z760 : W := mkw 0x2b3005282ba0f60e 0x02b3005282ba0f60 0x7ff001b83fe0fe09 0xf7ff001b83fe0fe0

def z761 : W := mkw 0xd48ff897d45f0981 0x0d48ff897d45f098 0x000ff807c01f01c2 0x0000ff807c01f01c

def z762 : W := mkw 0x00c552d5c0664468 0x800c552d5c066446 0x01f3f9fcc1e30637 0xb01f3f9fcc1e3063

def z763 : W := mkw 0x060b159640000000 0x0060b15964000000 0x0e33f9fcc0000007 0xa0e33f9fcc000000

def z764 : W := mkw 0x4dbee8083ddf1b15 0x44dbee8083ddf1b1 0x7ffff844ffff3f3f 0xf7ffff844ffff3f3

def z765 : W := mkw 0x0201159640000000 0x0020115964000000 0x8033ffffc0000007 0xa8033ffffc000000

def z766 : W := mkw 0x1011989e71111b95 0x41011989e71111b9 0x3033f9fff1133fff 0xa3033f9fff1133ff

def z767 : W := mkw 0x0dae600000000000 0x00dae60000000000 0x0ffff9f800000007 0xf0ffff9f80000000

def z768 : W := mkw 0x0b70076829801204 0x00b7007682980120 0xfff007f83fe03e0d 0xffff007f83fe03e0

def z769 : W := mkw 0xafef77f7c8a0440a 0x0afef77f7c8a0440 0x8fffffffc0e00007 0xf8fffffffc0e0000

def z770 : W := mkw 0x120085001618a981 0x0120085001618a98 0xfe0c07873e1cf9ce 0xefe0c07873e1cf9c

def z771 : W := mkw 0x2b700769aba0f66e 0x82b700769aba0f66 0xfffc07fffffcffff 0xffffc07fffffcfff

def z772 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfff047fcffe0fe0f 0xffff047fcffe0fe0

def z773 : W := mkw 0x0daee000145e0000 0x00daee000145e000 0x6ffff8003fff000b 0xf6ffff8003fff000

def z774 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x6ffff8003eec0003 0xf6ffff8003eec000

def z775 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0xb03ffffff1133f3f 0xeb03ffffff1133f3

def z776 : W := mkw 0x101088083719bb95 0x4101088083719bb9 0x700000003e1cf9c8 0x0700000003e1cf9c

def z777 : W := mkw 0xc48ff897d45f0911 0x4c48ff897d45f091 0x000ff807c01f0132 0x0000ff807c01f013

def z778 : W := mkw 0x8f6b37f640000000 0x08f6b37f64000000 0x8e33bff800000004 0x88e33bff80000000

def z779 : W := mkw 0x160b05860608a981 0x0160b05860608a98 0xfe0c07873e0cf9cc 0xefe0c07873e0cf9c

def z780 : W := mkw 0x0001109440000000 0x0000110944000000 0x803fffffc0000007 0xe803fffffc000000

def z781 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x2ffff8003fe30003 0xf2ffff8003fe3000

def z782 : W := mkw 0x8fef77f7c0664408 0x08fef77f7c066440 0xdfffffffc1ffc60f 0xfdfffffffc1ffc60

def z783 : W := mkw 0x160a85021618a080 0x0160a85021618a08 0xfe0f87833e1cf8ce 0xefe0f87833e1cf8c

def z784 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0x0e33b9fcc0000004 0x80e33b9fcc000000

def z785 : W := mkw 0x4dbee8083ddf1b15 0x44dbee8083ddf1b1 0x6ffff8003fff380b 0xf6ffff8003fff380

def z786 : W := mkw 0x8faf75b7c0000000 0x08faf75b7c000000 0x8e3fffbfc0000006 0xe8e3fffbfc000000

def z787 : W := mkw 0x9fef77f7c608a080 0x09fef77f7c608a08 0xfffffffffe0cf8cf 0xffffffffffe0cf8c

def z788 : W := mkw 0x4d3aa8003d990000 0x04d3aa8003d99000 0x6ff3b8003ee00000 0xd6ff3b8003ee0000

def z789 : W := mkw 0x2b3005282b80b206 0x02b3005282b80b20 0xfff007b83fe0f80d 0xffff007b83fe0f80

def z790 : W := mkw 0x8faf75b7c0460060 0x88faf75b7c046006 0x0e3ff9bfc01f01f2 0x80e3ff9bfc01f01f

def z791 : W := mkw 0x120105860200a981 0x0120105860200a98 0xfe0c07873e1cf9ce 0xefe0c07873e1cf9c

def z792 : W := mkw 0x89e572f5c0664468 0x889e572f5c066446 0x11f3f9fcc1f3073f 0xb11f3f9fcc1f3073

def z793 : W := mkw 0x2b700769aba0f66e 0x82b700769aba0f66 0xfff047fffff3ffff 0xffff047fffff3fff

def z794 : W := mkw 0x0010880831111204 0x0001088083111120 0x3033f9fcf1133f3f 0xa3033f9fcf1133f3

def z795 : W := mkw 0x4011989c7d991b15 0x44011989c7d991b1 0x3033f9fcff133f3f 0xa3033f9fcff133f3

def z796 : W := mkw 0x160b95965618a981 0x0160b95965618a98 0xfe0fff87fe1cf9ce 0xefe0fff87fe1cf9c

def z797 : W := mkw 0x00d4ca49b1775f7d 0xc00d4ca49b1775f7 0xf1cc060331fffff8 0x5f1cc060331fffff

def z798 : W := mkw 0x160b95965618a981 0x0160b95965618a98 0xfe0f87fffe1cf9ce 0xefe0f87fffe1cf9c

def z799 : W := mkw 0x5dbee8003ddf0981 0x05dbee8003ddf098 0x6ffff8003fff01cb 0xf6ffff8003fff01c

def z800 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfffc47ffffffffff 0xffffc47fffffffff

def z801 : W := mkw 0x848f7097c0460060 0x8848f7097c046006 0x103ff9ffc11f07ff 0xa103ff9ffc11f07f

def z802 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0xdfffffffc1ecc6cf 0xfdfffffffc1ecc6c

def z803 : W := mkw 0x0001909450100901 0x0000190945010090 0x3033f9fcf1133f3f 0xa3033f9fcf1133f3

def z804 : W := mkw 0x4dae60000cce0000 0x04dae60000cce000 0x4fffb8000eec0000 0xd4fffb8000eec000

def z805 : W := mkw 0x0001109440000000 0x0000110944000000 0x3033f9fcf000380f 0xa3033f9fcf000380

def z806 : W := mkw 0x601088083fdfb206 0x0601088083fdfb20 0x600000003fff3808 0x0600000003fff380

def z807 : W := mkw 0x160b95965618a991 0x4160b95965618a99 0xfe0f8787fe1cf9fe 0xefe0f8787fe1cf9f

def z808 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xee0f87833e1cf8ca 0xeee0f87833e1cf8c

def z809 : W := mkw 0x20508a483bb1ff1f 0x420508a483bb1ff1 0xf1c04644fff3ff3f 0x7f1c04644fff3ff3

def z810 : W := mkw 0x4dbe68002dcf0000 0x04dbe68002dcf000 0x4ffff8000fef0003 0xf4ffff8000fef000

def z811 : W := mkw 0x9fee6763866ee4e8 0x89fee6763866ee4e 0xcfcc06030eecc0c0 0x5cfcc06030eecc0c

def z812 : W := mkw 0x99e4f271d618a981 0x099e4f271d618a98 0x71f07878fe1cf9c9 0x171f07878fe1cf9c

def z813 : W := mkw 0x0010880839911b15 0x40010880839911b1 0x700000003ff33f38 0x0700000003ff33f3

def z814 : W := mkw 0x84cf72d7c0000000 0x084cf72d7c000000 0x81ffffffc0000007 0xf81ffffffc000000

def z815 : W := mkw 0xc2519ff7fddf0000 0x0c2519ff7fddf000 0xe00007ffffff000c 0x0e00007ffffff000

def z816 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x1033f9fcc1133f37 0x01033f9fcc1133f3

def z817 : W := mkw 0x0011189c61011b15 0x40011189c61011b1 0x1033f9fcc1033f37 0xa1033f9fcc1033f3

def z818 : W := mkw 0x9fef77f7c608a080 0x09fef77f7c608a08 0x8fffffffce000007 0xf8fffffffce00000

def z819 : W := mkw 0x89e572f5c0664468 0x889e572f5c066446 0xd1ffffffc1ffc7ff 0xfd1ffffffc1ffc7f

def z820 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8ff3ffffc0000005 0x98ff3ffffc000000

def z821 : W := mkw 0x82c557f7c0664468 0x882c557f7c066446 0xd1ffffffc1ffc7ff 0xfd1ffffffc1ffc7f

def z822 : W := mkw 0x6ffeef683ffff60e 0x06ffeef683ffff60 0xffcc06003ffffe08 0x5ffcc06003ffffe0

def z823 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x6ffff9f83fff000f 0xf6ffff9f83fff000

def z824 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x30000044f1133f3c 0x030000044f1133f3

def z825 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xfe0f86073e1cf9ca 0x4fe0f86073e1cf9c

def z826 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x7ffff8043fff010f 0xf7ffff8043fff010

def z827 : W := mkw 0x2b708f683bb1ff1f 0x42b708f683bb1ff1 0xffc006003ff3ff38 0x5ffc006003ff3ff3

def z828 : W := mkw 0x0d2b309440000000 0x00d2b30944000000 0x0e33b9b800000000 0x80e33b9b80000000

def z829 : W := mkw 0x820115b640000000 0x0820115b64000000 0x0033b9b800000000 0x80033b9b80000000

def z830 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0xeffffe073fff000f 0xfeffffe073fff000

def z831 : W := mkw 0x161a8d0a3719bb95 0x4161a8d0a3719bb9 0xfe0c06033f1ffff8 0x4fe0c06033f1ffff

def z832 : W := mkw 0x16cfc7c7967eede9 0x816cfc7c7967eede 0x2fc3c1c0ffe33e31 0x92fc3c1c0ffe33e3

def z833 : W := mkw 0x9f2b35b64200a981 0x09f2b35b64200a98 0x0e33b9b800003800 0x80e33b9b80000380

def z834 : W := mkw 0x948ff097d45e09e1 0x8948ff097d45e09e 0x000ff807c01f01f2 0x0000ff807c01f01f

def z835 : W := mkw 0x2bb44529abc6b266 0x82bb44529abc6b26 0x2e3c41bffe1f39f2 0x82e3c41bffe1f39f

def z836 : W := mkw 0x160b95965618a981 0x0160b95965618a98 0xfe3fbfbf3e1cf9ce 0xefe3fbfbf3e1cf9c

def z837 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0x0e33b9f800000005 0xa0e33b9f80000000

def z838 : W := mkw 0x8fee676380000000 0x08fee67638000000 0x8ffffffb00000007 0xf8ffffffb0000000

def z839 : W := mkw 0x201088083bf7ff7f 0xc201088083bf7ff7 0x700000003ffffff8 0x0700000003ffffff

def z840 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x0ffff9f8c0000003 0xf0ffff9f8c000000

def z841 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0xdfffffffc0ecc7f7 0xfdfffffffc0ecc7f

def z842 : W := mkw 0x0fee676180664468 0x80fee67618066446 0xdfffffffc1ffc7ff 0xfdfffffffc1ffc7f

def z843 : W := mkw 0x10d4ca49b77ffffd 0xc10d4ca49b77ffff 0xf1cc4647ffffffff 0x7f1cc4647fffffff

def z844 : W := mkw 0x4daee8001cdf0000 0x04daee8001cdf000 0x6fcff8003eff000a 0xf6fcff8003eff000

def z845 : W := mkw 0x5bb56d862bc7a981 0x05bb56d862bc7a98 0x91f07f8701e3f9c5 0x191f07f8701e3f9c

def z846 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x2ff3b8003ee00000 0x92ff3b8003ee0000

def z847 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0xcfffffffc1ff063f 0xfcfffffffc1ff063

def z848 : W := mkw 0x548ff896545f0991 0x4548ff896545f099 0x000ff807c01f01f2 0x0000ff807c01f01f

def z849 : W := mkw 0x224117fc4220f60e 0x0224117fc4220f60 0x900007fcc000fe04 0x0900007fcc000fe0

def z850 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x3000000030003f30 0x03000000030003f3

def z851 : W := mkw 0x0b2115b440000000 0x00b2115b44000000 0x0e33f9fcc0000007 0xa0e33f9fcc000000

def z852 : W := mkw 0x4d7aaa41bdb94468 0x84d7aaa41bdb9446 0xbe33be47fe00c7f4 0x8be33be47fe00c7f

def z853 : W := mkw 0x8f6b37f7c0000000 0x08f6b37f7c000000 0x8e33ffffc0000007 0xa8e33ffffc000000

def z854 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0x0e33b9bc00000006 0xa0e33b9bc0000000

def z855 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0xdfffffffc0fcc1cf 0xfdfffffffc0fcc1c

def z856 : W := mkw 0x8fef77f7c0204408 0x08fef77f7c020440 0xdfffffffc1f3c73f 0xfdfffffffc1f3c73

def z857 : W := mkw 0xb24117ffc220ff8f 0x0b24117ffc220ff8 0x900007ffc000ffc4 0x0900007ffc000ffc

def z858 : W := mkw 0x8faf75b640460000 0x08faf75b64046000 0x4ffff9b801ff000b 0xf4ffff9b801ff000

def z859 : W := mkw 0x8faf75b7c0000000 0x08faf75b7c000000 0x0e33f9b8c0000000 0x80e33f9b8c000000

def z860 : W := mkw 0x0f6a276000000000 0x00f6a27600000000 0x8ff3bff800000005 0xf8ff3bff80000000

def z861 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0x0ff3f9f8c1e30631 0x90ff3f9f8c1e3063

def z862 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xfe0f87c7fe1cfffe 0xefe0f87c7fe1cfff

def z863 : W := mkw 0x2b700f682ba1f61e 0x42b700f682ba1f61 0xfff007f83fe3fe3d 0xffff007f83fe3fe3

def z864 : W := mkw 0x8fef77f7c200a000 0x08fef77f7c200a00 0xaffffffffe003807 0xfaffffffffe00380

def z865 : W := mkw 0x401088083ddf1204 0x0401088083ddf120 0x700000003fff3e08 0x0700000003fff3e0

def z866 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0x8e33bfb800000004 0xe8e33bfb80000000

def z867 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x6ff3f8003fe30009 0xf6ff3f8003fe3000

def z868 : W := mkw 0x020005000200a000 0x0020005000200a00 0xfe0c07833e0cf8cc 0xefe0c07833e0cf8c

def z869 : W := mkw 0xa24117ffc220ff1f 0x4a24117ffc220ff1 0x900007ffc000ff34 0x0900007ffc000ff3

def z870 : W := mkw 0x8fef77f7c0460000 0x08fef77f7c046000 0xdfffffffc1ffc1cf 0xfdfffffffc1ffc1c

def z871 : W := mkw 0x0001109440000000 0x0000110944000000 0x0033b9bc00000006 0xa0033b9bc0000000

def z872 : W := mkw 0x0001109c40001b15 0x40001109c40001b1 0x1033f9fcc1133f3f 0xa1033f9fcc1133f3

def z873 : W := mkw 0x4dbee8083ddf1214 0x44dbee8083ddf121 0x6ffff8003fff063b 0xf6ffff8003fff063

def z874 : W := mkw 0x160b95965618a981 0x0160b95965618a98 0xfe3fffffff1fffff 0xefe3fffffff1ffff

def z875 : W := mkw 0x0001109440000000 0x0000110944000000 0x0033f9f8c0000001 0x80033f9f8c000000

def z876 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x3000000031003e08 0x03000000031003e0

def z877 : W := mkw 0x2b6007680aa0f60e 0x02b6007680aa0f60 0xffc007f83ee0fe0c 0xfffc007f83ee0fe0

def z878 : W := mkw 0x80011097c0000000 0x080011097c000000 0x0033f9ffc0000007 0xa0033f9ffc000000

def z879 : W := mkw 0x8def72f7c0000000 0x08def72f7c000000 0x81fffe7fc0000007 0x781fffe7fc000000

def z880 : W := mkw 0x0010880831111204 0x0001088083111120 0x3000000031133e08 0x03000000031133e0

def z881 : W := mkw 0x160a85021618a981 0x0160a85021618a98 0xfe0c06073e1cf9ce 0x6fe0c06073e1cf9c

def z882 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0x8e3fffffc0000007 0xe8e3fffffc000000

def z883 : W := mkw 0xcfef77f7ccee4468 0x8cfef77f7ccee446 0xdfffffffcfffc7ff 0xfdfffffffcfffc7f

def z884 : W := mkw 0x0001989c50111b15 0x40001989c50111b1 0x1033f9fcc0133f37 0xa1033f9fcc0133f3

def z885 : W := mkw 0x0faf759640000000 0x00faf75964000000 0x8fffffffc0000007 0xf8fffffffc000000

def z886 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x3000000030103908 0x0300000003010390

def z887 : W := mkw 0x960b95b65618a981 0x0960b95b65618a98 0xfe0f87bf3e1cf9ce 0xefe0f87bf3e1cf9c

def z888 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfff007b83ee0f80c 0xffff007b83ee0f80

def z889 : W := mkw 0x49b4e80039d70000 0x049b4e80039d7000 0x6ff3f8003ff3000b 0xf6ff3f8003ff3000

def z890 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfff007b83fe0fe08 0xdfff007b83fe0fe0

def z891 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x7ffff8003fff073b 0xf7ffff8003fff073

def z892 : W := mkw 0x224117fdc220ff7f 0xc224117fdc220ff7 0x900007ffc000fff4 0x0900007ffc000fff

def z893 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xbff007f83fe0fe05 0x9bff007f83fe0fe0

def z894 : W := mkw 0x00c552d5c0000000 0x000c552d5c000000 0x01f3f9fcc0000007 0xb01f3f9fcc000000

def z895 : W := mkw 0x049ec800355f0000 0x0049ec800355f000 0x6ffff8003fff000b 0xf6ffff8003fff000

def z896 : W := mkw 0x8fef77f7c0204408 0x08fef77f7c020440 0x9fffffffc000c607 0xf9fffffffc000c60

def z897 : W := mkw 0x8b6117f7c0000000 0x08b6117f7c000000 0x8ff3ffffc0000007 0xf8ff3ffffc000000

def z898 : W := mkw 0x864b17f7c0000000 0x0864b17f7c000000 0x8e3fffffc0000007 0xe8e3fffffc000000

def z899 : W := mkw 0x160b8d861619a991 0x4160b8d861619a99 0xfe0f87873e1ff9fe 0xefe0f87873e1ff9f

def z900 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8fffbfffc0000004 0xd8fffbfffc000000

def z901 : W := mkw 0x8fef77f7c200a000 0x08fef77f7c200a00 0xcfffffffce00c007 0xfcfffffffce00c00

def z902 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x3033f9fcf0133f36 0x83033f9fcf0133f3

def z903 : W := mkw 0xafef77f7cae6e46a 0x8afef77f7cae6e46 0xdfffffffcfffc7ff 0xfdfffffffcfffc7f

def z904 : W := mkw 0x8fef77f7c0204468 0x88fef77f7c020446 0x8fffffffc000c0c7 0xf8fffffffc000c0c

def z905 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x6fffb8003fff0008 0xd6fffb8003fff000

def z906 : W := mkw 0x4dbee801bddf0000 0x04dbee801bddf000 0x6ffff807ffff000b 0xf6ffff807ffff000

def z907 : W := mkw 0x8dee7271c0000000 0x08dee7271c000000 0x01fff878c0000003 0x101fff878c000000

def z908 : W := mkw 0x160b9d965619a991 0x4160b9d965619a99 0xfe0fbf873e1cf9ce 0xefe0fbf873e1cf9c

def z909 : W := mkw 0x8fef77f7c0460060 0x88fef77f7c046006 0x9fffffffc11f07ff 0xf9fffffffc11f07f

def z910 : W := mkw 0x8f6b37f7c0000000 0x08f6b37f7c000000 0x0e33b9f8c0000000 0x80e33b9f8c000000

def z911 : W := mkw 0x401088083dff5f7d 0xc401088083dff5f7 0x700000003ffffff8 0x0700000003ffffff

def z912 : W := mkw 0x324117fe4220ff9f 0x4324117fe4220ff9 0x900007ffc000fff4 0x0900007ffc000fff

def z913 : W := mkw 0xafef77f7c220e40a 0x0afef77f7c220e40 0x8fffffffc000c007 0xf8fffffffc000c00

def z914 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0x7ff001f83fe0fe09 0x97ff001f83fe0fe0

def z915 : W := mkw 0x60d4ca49bffff66e 0x860d4ca49bffff66 0xf1cc4647ffffffff 0x7f1cc4647fffffff

def z916 : W := mkw 0x892130b440000000 0x0892130b44000000 0x0033b9b800000000 0x80033b9b80000000

def z917 : W := mkw 0x0001109440000000 0x0000110944000000 0x0033b9f800000005 0xa0033b9f80000000

def z918 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x6ffff844ffff000f 0xf6ffff844ffff000

def z919 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0x8fffffffc1ff07f7 0xf8fffffffc1ff07f

def z920 : W := mkw 0x0084400000460000 0x0008440000046000 0xd1cc4647c1ffc7ff 0x7d1cc4647c1ffc7f

def z921 : W := mkw 0x0001109440000000 0x0000110944000000 0x0033f9bcc0000002 0x80033f9bcc000000

def z922 : W := mkw 0x960bb5965618a981 0x0960bb5965618a98 0xfe0fbf873e1cf9ce 0xefe0fbf873e1cf9c

def z923 : W := mkw 0x868f7597c0000000 0x0868f7597c000000 0x8e3fffffc0000007 0xe8e3fffffc000000

def z924 : W := mkw 0x0010880831571b75 0xc0010880831571b7 0x30000000311f3ff8 0x030000000311f3ff

def z925 : W := mkw 0x060b159640000000 0x0060b15964000000 0x8e3fbfbf00000006 0xe8e3fbfbf0000000

def z926 : W := mkw 0x601088083f99b206 0x0601088083f99b20 0x200000003e003800 0x0200000003e00380

def z927 : W := mkw 0xa49f709feba0f60e 0x0a49f709feba0f60 0x700ff807ffe0fe0a 0x0700ff807ffe0fe0

def z928 : W := mkw 0x448ff895d45f0971 0xc448ff895d45f097 0x000ff807c01f01f2 0x0000ff807c01f01f

def z929 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x6fcff8003fff000a 0x56fcff8003fff000

def z930 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8fffffffc01c01c7 0xf8fffffffc01c01c

def z931 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0xfffffe47ffffc7ff 0xffffffe47ffffc7f

def z932 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x2033f9f8f1133e3b 0xa2033f9f8f1133e3

def z933 : W := mkw 0x8fef77f7c0460060 0x88fef77f7c046006 0xcfffffffc1ff01ff 0xfcfffffffc1ff01f

def z934 : W := mkw 0x101088083719bb95 0x4101088083719bb9 0x200000003e003800 0x0200000003e00380

def z935 : W := mkw 0x4dbee801bddf0060 0x84dbee801bddf006 0x6ffff8033fff00cb 0xf6ffff8033fff00c

def z936 : W := mkw 0x8f6b37f7c0000000 0x08f6b37f7c000000 0x8e3fbfffc0000006 0xe8e3fbfffc000000

def z937 : W := mkw 0x924117f7c220ede9 0x8924117f7c220ede 0x900007ffc000fff4 0x0900007ffc000fff

def z938 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x6ffff8003eff0002 0xd6ffff8003eff000

def z939 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xee0f87873e1cf9c2 0xcee0f87873e1cf9c

def z940 : W := mkw 0x160b9d965619a991 0x4160b9d965619a99 0xfe3ffffffe1ff9ff 0xefe3ffffffe1ff9f

def z941 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x71f3f9fcf1f33f3f 0xf71f3f9fcf1f33f3

def z942 : W := mkw 0x4dbee8003ddf0911 0x44dbee8003ddf091 0x6ffff8003fff013b 0xf6ffff8003fff013

def z943 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x7e33f9fcff133f3f 0xe7e33f9fcff133f3

def z944 : W := mkw 0x4dbee8083ddf1204 0x04dbee8083ddf120 0x7ffff8003fff3e0b 0xf7ffff8003fff3e0

def z945 : W := mkw 0x9fef77f7c220ede9 0x89fef77f7c220ede 0x9fffffffc000fff7 0xf9fffffffc000fff

def z946 : W := mkw 0x8f2b35b64200a000 0x08f2b35b64200a00 0xfe33bfb83e00f80c 0xefe33bfb83e00f80

def z947 : W := mkw 0x2b700f682ba1f60e 0x02b700f682ba1f60 0xfff07ff83fe3fe0d 0xffff07ff83fe3fe0

def z948 : W := mkw 0x8def72f7c0000000 0x08def72f7c000000 0x01f3f878c0000001 0x101f3f878c000000

def z949 : W := mkw 0x22508f683331f60e 0x022508f683331f60 0xb033fff83113fe0f 0xab033fff83113fe0

def z950 : W := mkw 0x9fef77f7c0000981 0x09fef77f7c000098 0x8fffffffc00001c7 0xf8fffffffc00001c

def z951 : W := mkw 0x40108808355f1b15 0x440108808355f1b1 0x30000000311f3f38 0x030000000311f3f3

def z952 : W := mkw 0xafef77f7caa0e40a 0x0afef77f7caa0e40 0xfffffffffee0f80f 0xffffffffffee0f80

def z953 : W := mkw 0x4daee0001cde0000 0x04daee0001cde000 0x6ffff8003efc000b 0xf6ffff8003efc000

def z954 : W := mkw 0x101088083719bb95 0x4101088083719bb9 0xf00c4647ff1fffff 0x6f00c4647ff1ffff

def z955 : W := mkw 0x0921109440000000 0x0092110944000000 0x0ff3f9fcc0000007 0xf0ff3f9fcc000000

def z956 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0xbffffffff000380f 0xfbffffffff000380

def z957 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0x0e33f9f8c0000001 0x80e33f9f8c000000

def z958 : W := mkw 0x0010981871111214 0x4001098187111121 0x3033f9f8f1133e3f 0xa3033f9f8f1133e3

def z959 : W := mkw 0x8fef77f7c0204468 0x88fef77f7c020446 0xdfffffffc1e0c7ff 0xfdfffffffc1e0c7f

def z960 : W := mkw 0x160a05020608a080 0x0160a05020608a08 0xfe0c07873e1cf9ce 0xefe0c07873e1cf9c

def z961 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8fffbffb00000005 0xf8fffbffb0000000

def z962 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfff007f83ff3ff3d 0xffff007f83ff3ff3

def z963 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0x3ff001f83fe03e0d 0xb3ff001f83fe03e0

def z964 : W := mkw 0x0dae701040000000 0x00dae70104000000 0x0ffff878c0000003 0xf0ffff878c000000

def z965 : W := mkw 0x00855095c0460060 0x800855095c046006 0x003ff9ffc01f01f7 0xa003ff9ffc01f01f

def z966 : W := mkw 0x8fef77f7c0460000 0x08fef77f7c046000 0x8fffffffc01f0007 0xf8fffffffc01f000

def z967 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0xcfffbfbb00ecc0c0 0xdcfffbfbb00ecc0c

def z968 : W := mkw 0x8fef77f7c0000911 0x48fef77f7c000091 0x8fffffffc0000137 0xf8fffffffc000013

def z969 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x3033f9f8f1133f39 0x83033f9f8f1133f3

def z970 : W := mkw 0x8fef77f7c0204468 0x88fef77f7c020446 0x8fffffffc0000637 0xf8fffffffc000063

def z971 : W := mkw 0x20d4ca49bbf7ff7f 0xc20d4ca49bbf7ff7 0xf1cc4647ffffffff 0x7f1cc4647fffffff

def z972 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0x0e33f9bcc0000002 0x80e33f9bcc000000

def z973 : W := mkw 0x293000082ba0f60e 0x0293000082ba0f60 0x7ff001f83fe0fe0d 0xf7ff001f83fe0fe0

def z974 : W := mkw 0x2970026829a0560e 0x02970026829a0560 0x7ff001f83fe03e0d 0xf7ff001f83fe03e0

def z975 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfff3fff83fe0fe0f 0xffff3fff83fe0fe0

def z976 : W := mkw 0x2010880839b15f1f 0x42010880839b15f1 0x3000000031f33f38 0x03000000031f33f3

def z977 : W := mkw 0x701088083fffff8f 0x0701088083fffff8 0x700000003fffffc8 0x0700000003fffffc

def z978 : W := mkw 0x8faf75b640000000 0x08faf75b64000000 0x0e3ff9b800000002 0x80e3ff9b80000000

def z979 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xeff007f83fe0fe01 0xdeff007f83fe0fe0

def z980 : W := mkw 0x201088083bb1f60e 0x0201088083bb1f60 0x700000003ff3fe08 0x0700000003ff3fe0

def z981 : W := mkw 0x00c4424180664468 0x800c442418066446 0xffcc4647ffffc7ff 0xfffcc4647ffffc7f

def z982 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfffc07ff3fe0fe0f 0xffffc07ff3fe0fe0

def z983 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8fffffffc1030637 0xf8fffffffc103063

def z984 : W := mkw 0x49f47a59e9e7567c 0xc49f47a59e9e7567 0x01f07878c1e30631 0x101f07878c1e3063

def z985 : W := mkw 0x0930880039910000 0x0093088003991000 0x6ff3b8003fe00009 0xf6ff3b8003fe0000

def z986 : W := mkw 0x020185841210a901 0x0020185841210a90 0xfe0f87873e1cf9ce 0xefe0f87873e1cf9c

def z987 : W := mkw 0x601088083fffff1f 0x4601088083fffff1 0x700000003fffff38 0x0700000003fffff3

def z988 : W := mkw 0x0040024000204408 0x0004002400020440 0xd1cc4647c1ffc7ff 0x7d1cc4647c1ffc7f

def z989 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x2033f9fcf1033e37 0xa2033f9fcf1033e3

def z990 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8fffffffc113000f 0xf8fffffffc113000

def z991 : W := mkw 0xcf2b35b64c880000 0x0cf2b35b64c88000 0x0e33b9b80e000000 0x80e33b9b80e00000

def z992 : W := mkw 0x4dbee8003ddf0901 0x04dbee8003ddf090 0x7ffff8003fff390b 0xf7ffff8003fff390

def z993 : W := mkw 0x601088083dff560e 0x0601088083dff560 0x600000003fff0608 0x0600000003fff060

def z994 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0xdfffffffc1e3c63f 0xfdfffffffc1e3c63

def z995 : W := mkw 0x2b3005282b80b206 0x02b3005282b80b20 0x6ff001b83ee03800 0xd6ff001b83ee0380

def z996 : W := mkw 0x06cf57d7c0664468 0x806cf57d7c066446 0xdfffffffc1ffc7ff 0xfdfffffffc1ffc7f

def z997 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xee0f87873e0cf8c6 0xeee0f87873e0cf8c

def z998 : W := mkw 0x0b6117f440000000 0x00b6117f44000000 0x8ff3bff800000005 0xf8ff3bff80000000

def z999 : W := mkw 0x00c4424180664468 0x800c442418066446 0xd1cc4607c1ffc7fa 0x5d1cc4607c1ffc7f

def z1000 : W := mkw 0x560bad861619a981 0x0560bad861619a98 0xfe0fbf873e1cf9ce 0xefe0fbf873e1cf9c

def z1001 : W := mkw 0x040b808414180901 0x0040b80841418090 0xfe0f87873e1cf9ce 0xefe0f87873e1cf9c

def z1002 : W := mkw 0xaf2b35b64a80a002 0x0af2b35b64a80a00 0x0e33b9b80e000000 0x80e33b9b80e00000

def z1003 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0xdfffffffc000c00f 0xfdfffffffc000c00

def z1004 : W := mkw 0x8fef77f7c266e468 0x88fef77f7c266e46 0xffffffffffffffff 0xffffffffffffffff

def z1005 : W := mkw 0x00508a49b1315f7d 0xc00508a49b1315f7 0xb0000647f113fffc 0x0b0000647f113fff

def z1006 : W := mkw 0x5f3bbd9e7f99bb95 0x45f3bbd9e7f99bb9 0x2e33b9b83e003800 0x82e33b9b83e00380

def z1007 : W := mkw 0x6fee67600eeee40a 0x06fee67600eeee40 0xcffffff80eecc007 0xfcffffff80eecc00

def z1008 : W := mkw 0x0010880831571b15 0x40010880831571b1 0x7000000031ff3f38 0x07000000031ff3f3

def z1009 : W := mkw 0x201088083bb1ff1f 0x4201088083bb1ff1 0x700000003fe0fe08 0x0700000003fe0fe0

def z1010 : W := mkw 0x8fef77f7c0204408 0x08fef77f7c020440 0xcfffffffc0e0c007 0xfcfffffffc0e0c00

def z1011 : W := mkw 0x4daee8001cdf0000 0x04daee8001cdf000 0x4fcfb8000eec0000 0x54fcfb8000eec000

def z1012 : W := mkw 0x00c552d5c0664468 0x800c552d5c066446 0xc1ffffffc0ecc0c7 0xfc1ffffffc0ecc0c

def z1013 : W := mkw 0x8fef77f7c0460000 0x08fef77f7c046000 0xdfffffffc1ff073f 0xfdfffffffc1ff073

def z1014 : W := mkw 0x8fef77f7c200a000 0x08fef77f7c200a00 0xfffffffffe1cf9cf 0xffffffffffe1cf9c

def z1015 : W := mkw 0x0011189c61011214 0x40011189c6101121 0x3033f9fcf1033e3f 0xa3033f9fcf1033e3

def z1016 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xfe0f87873f1ffffe 0xefe0f87873f1ffff

def z1017 : W := mkw 0x8faf75b640000000 0x08faf75b64000000 0x8fffffbf00000007 0xf8fffffbf0000000

def z1018 : W := mkw 0x0dbee0003d980000 0x00dbee0003d98000 0x6ffff8003ffc000b 0xf6ffff8003ffc000

def z1019 : W := mkw 0x0f2a252000000000 0x00f2a25200000000 0x0e33b9b800000000 0x80e33b9b80000000

def z1020 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x6fffb8003efc000a 0xf6fffb8003efc000

def z1021 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x3033f9fcf1033f35 0x83033f9fcf1033f3

def z1022 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xaff007f83fe03e05 0xfaff007f83fe03e0

def z1023 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0x0e33f9b800000003 0xa0e33f9b80000000

def z1024 : W := mkw 0x0def72d5c0000000 0x00def72d5c000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1025 : W := mkw 0x0094c80831571b15 0x40094c80831571b1 0x71cc400031ff3f3b 0x771cc400031ff3f3

def z1026 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8fffffffc0130137 0xf8fffffffc013013

def z1027 : W := mkw 0x9fef77f7c200a080 0x09fef77f7c200a08 0x8fffffffc000c0c7 0xf8fffffffc000c0c

def z1028 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x0ff3b9b800000000 0x90ff3b9b80000000

def z1029 : W := mkw 0x2b6117f44aa0e40a 0x02b6117f44aa0e40 0xcff3fffccee0c007 0xfcff3fffccee0c00

def z1030 : W := mkw 0xa24117f7c220e40a 0x0a24117f7c220e40 0x800007ffc000c004 0x0800007ffc000c00

def z1031 : W := mkw 0xa24117ffc220f66e 0x8a24117ffc220f66 0x900007ffc000fff4 0x0900007ffc000fff

def z1032 : W := mkw 0x9fef77f7c200a981 0x09fef77f7c200a98 0xfffffffffe00f9cf 0xffffffffffe00f9c

def z1033 : W := mkw 0x020115944200a000 0x0020115944200a00 0xfe33fffcfe00f80f 0xefe33fffcfe00f80

def z1034 : W := mkw 0xa9f47279e9e6566e 0x8a9f47279e9e6566 0x01f07878c1e30631 0x101f07878c1e3063

def z1035 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xfe3f87ff3e1cf9cf 0xefe3f87ff3e1cf9c

def z1036 : W := mkw 0x160b05860608a080 0x0160b05860608a08 0xfe0f87873e0cf8ce 0xefe0f87873e0cf8c

def z1037 : W := mkw 0x0011989c79911b15 0x40011989c79911b1 0x7033f9fcfff33f3f 0xa7033f9fcfff33f3

def z1038 : W := mkw 0x84cf72d7c0664468 0x884cf72d7c066446 0xd1ffffffc1ffc7ff 0xfd1ffffffc1ffc7f

def z1039 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x6ffff8003fef0001 0xd6ffff8003fef000

def z1040 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x7033f9fcf11fffff 0xa7033f9fcf11ffff

def z1041 : W := mkw 0x8f6b37f7c0000000 0x08f6b37f7c000000 0x8ff3bfffc0000005 0xf8ff3bfffc000000

def z1042 : W := mkw 0x9fef77f7c66ee4e8 0x89fef77f7c66ee4e 0xdfffffffcfffc7ff 0xfdfffffffcfffc7f

def z1043 : W := mkw 0x840b309640000000 0x0840b30964000000 0x0033b9b800000000 0x80033b9b80000000

def z1044 : W := mkw 0xcfef77f7ccee4468 0x8cfef77f7ccee446 0xcfffffffceecc0c7 0xfcfffffffceecc0c

def z1045 : W := mkw 0x00d4ca49b1111b15 0x400d4ca49b1111b1 0xb1cc4647f1133f3f 0x7b1cc4647f1133f3

def z1046 : W := mkw 0x001088083311bb15 0x4001088083311bb1 0x700000003f13ff38 0x0700000003f13ff3

def z1047 : W := mkw 0x0fef67e600000000 0x00fef67e60000000 0x8fffffff00000007 0xf8fffffff0000000

def z1048 : W := mkw 0x160a85021618a981 0x0160a85021618a98 0xfe0f86033e1cf9ca 0xefe0f86033e1cf9c

def z1049 : W := mkw 0x9fef77f7c608a080 0x09fef77f7c608a08 0xdfffffffce1cc1cf 0xfdfffffffce1cc1c

def z1050 : W := mkw 0x00c4424180664468 0x800c442418066446 0x91cc4647c1ffc7f7 0x191cc4647c1ffc7f

def z1051 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8fffbfbf00000006 0xf8fffbfbf0000000

def z1052 : W := mkw 0x5dbee8023ddf0080 0x05dbee8023ddf008 0x6ffff8033fff00cb 0xf6ffff8033fff00c

def z1053 : W := mkw 0x8dee7271c0000000 0x08dee7271c000000 0x8ffffe7fc0000007 0xf8ffffe7fc000000

def z1054 : W := mkw 0x4dbee8003d990000 0x04dbee8003d99000 0x6ffff8003fe0000b 0xf6ffff8003fe0000

def z1055 : W := mkw 0x4dbee8083ddf1204 0x04dbee8083ddf120 0x7ffff9fcffff3f3f 0xf7ffff9fcffff3f3

def z1056 : W := mkw 0x0001109440000000 0x0000110944000000 0x0033f9fcc1030637 0xa0033f9fcc103063

def z1057 : W := mkw 0x8dee7271c0664468 0x88dee7271c066446 0x4ffff878c1ff063b 0xf4ffff878c1ff063

def z1058 : W := mkw 0x0d3a200029800000 0x00d3a20002980000 0x6ff3b8003fe00009 0xf6ff3b8003fe0000

def z1059 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0x9fffffffc1e3c7f7 0xf9fffffffc1e3c7f

def z1060 : W := mkw 0x848f7097c0000000 0x0848f7097c000000 0x003ff9bfc0000002 0x8003ff9bfc000000

def z1061 : W := mkw 0xafef77f7cae6e46a 0x8afef77f7cae6e46 0xcfffffffceecc0c7 0xfcfffffffceecc0c

def z1062 : W := mkw 0x3b70076a2ba0f68e 0x03b70076a2ba0f68 0xfff007fb3fe0fecd 0xffff007fb3fe0fec

def z1063 : W := mkw 0x9f2b35b64200a981 0x09f2b35b64200a98 0x9e33bfbf0000f9c4 0x89e33bfbf0000f9c

def z1064 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xffc007f83fe0fe0c 0x5ffc007f83fe0fe0

def z1065 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x0ffff9ffc0000003 0x90ffff9ffc000000

def z1066 : W := mkw 0x8fef77f7c0460060 0x88fef77f7c046006 0x8fffffffc00c00c7 0xf8fffffffc00c00c

def z1067 : W := mkw 0x0930000829801204 0x0093000082980120 0x6ff001b83fe03809 0xf6ff001b83fe0380

def z1068 : W := mkw 0x148fd897d45f09f1 0xc148fd897d45f09f 0x000ff807c01f01f2 0x0000ff807c01f01f

def z1069 : W := mkw 0x0001109440000911 0x4000110944000091 0x0033f9fcc0000137 0xa0033f9fcc000013

def z1070 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x9fffffffc000c1c7 0xf9fffffffc000c1c

def z1071 : W := mkw 0x8f6b37f640000000 0x08f6b37f64000000 0x8fffbfff00000007 0xf8fffbfff0000000

def z1072 : W := mkw 0x0b6007600220e408 0x00b6007600220e40 0xfff007f83fe0fe0d 0xffff007f83fe0fe0

def z1073 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8ffffffbc0000001 0xd8ffffffbc000000

def z1074 : W := mkw 0x0be557f5c0664468 0x80be557f5c066446 0xdfffffffc1ffc7ff 0xfdfffffffc1ffc7f

def z1075 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x3000000431133f3e 0x23000000431133f3

def z1076 : W := mkw 0x8faf75b640000000 0x08faf75b64000000 0x0ff3f9b800000001 0x90ff3f9b80000000

def z1077 : W := mkw 0x004112d5c0204468 0x8004112d5c020446 0x9033ffffc000c7f7 0xa9033ffffc000c7f

def z1078 : W := mkw 0x2b6007600aa0e40a 0x02b6007600aa0e40 0xfff007f83ee0f80d 0xffff007f83ee0f80

def z1079 : W := mkw 0x0010880835191b15 0x40010880835191b1 0x700000003f1f3f38 0x0700000003f1f3f3

def z1080 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0x8e33bfbf00000004 0x88e33bfbf0000000

def z1081 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8fffffbfc0000002 0xd8fffffbfc000000

def z1082 : W := mkw 0x1011989c75191b95 0x41011989c75191b9 0x3033f9fcf11f3fff 0xa3033f9fcf11f3ff

def z1083 : W := mkw 0x401088083d991b15 0x4401088083d991b1 0x300000003f133f38 0x0300000003f133f3

def z1084 : W := mkw 0x024117f440000000 0x0024117f44000000 0x8033fffcc0000007 0xa8033fffcc000000

def z1085 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x30004040f1133f39 0x030004040f1133f3

def z1086 : W := mkw 0x4d3aa8003d990000 0x04d3aa8003d99000 0x6ff3f8003ff3000b 0xf6ff3f8003ff3000

def z1087 : W := mkw 0xab70076baba0f60e 0x0ab70076baba0f60 0xfff007fb3fe0fe0d 0xffff007fb3fe0fe0

def z1088 : W := mkw 0x824117f7c0204468 0x8824117f7c020446 0x9033ffffc113c7ff 0xa9033ffffc113c7f

def z1089 : W := mkw 0x69f46a69a9e7566e 0x869f46a69a9e7566 0x01f07878c1e30631 0x101f07878c1e3063

def z1090 : W := mkw 0x4daee8001cdf0000 0x04daee8001cdf000 0x4ffff8000eff0003 0xf4ffff8000eff000

def z1091 : W := mkw 0x4daf70944cce0000 0x04daf70944cce000 0x4ffff9fcceec0007 0xf4ffff9fcceec000

def z1092 : W := mkw 0x0daf709440000000 0x00daf70944000000 0x0ffff9b800000003 0xf0ffff9b80000000

def z1093 : W := mkw 0x00855095c0000000 0x000855095c000000 0x003ff9ffc0000007 0xa003ff9ffc000000

def z1094 : W := mkw 0x160a85021618a981 0x0160a85021618a98 0xee0c06033e0cf8c0 0x4ee0c06033e0cf8c

def z1095 : W := mkw 0x8f2b35b64200a000 0x08f2b35b64200a00 0x2e33b9b83e003800 0x82e33b9b83e00380

def z1096 : W := mkw 0x0dbee80039910000 0x00dbee8003991000 0x6ffff8003ff3000b 0xf6ffff8003ff3000

def z1097 : W := mkw 0xa24117fe4220f60e 0x0a24117fe4220f60 0x900007f80000fe04 0x0900007f80000fe0

def z1098 : W := mkw 0x40d4ca49bdff5f7d 0xc40d4ca49bdff5f7 0xf1cc4647ffffffff 0x7f1cc4647fffffff

def z1099 : W := mkw 0x501088083fdfbb95 0x4501088083fdfbb9 0x700000003ffffff8 0x0700000003ffffff

def z1100 : W := mkw 0x060b159640000000 0x0060b15964000000 0xde3fffffc11fc7ff 0xede3fffffc11fc7f

def z1101 : W := mkw 0x0d2b309440000000 0x00d2b30944000000 0x0e33f9fcc0000007 0xa0e33f9fcc000000

def z1102 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0x0e3fb9b800000002 0xe0e3fb9b80000000

def z1103 : W := mkw 0x0001109440000000 0x0000110944000000 0x0033f9fcc113000f 0xa0033f9fcc113000

def z1104 : W := mkw 0x224007680220f60e 0x0224007680220f60 0xffc007f83fe0fe0d 0xfffc007f83fe0fe0

def z1105 : W := mkw 0x0970024829a0560c 0x00970024829a0560 0xfff007f83fe0fe0d 0xffff007f83fe0fe0

def z1106 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x703ff9fcf11f3f3f 0xe703ff9fcf11f3f3

def z1107 : W := mkw 0x201088083b91bb17 0x4201088083b91bb1 0x200000003e003800 0x0200000003e00380

def z1108 : W := mkw 0x4dbee8083ddf1b15 0x44dbee8083ddf1b1 0x7fcc00003fff3f38 0x57fcc00003fff3f3

def z1109 : W := mkw 0x8def72f7c0664468 0x88def72f7c066446 0xd1fffe7fc1ffc7ff 0x7d1fffe7fc1ffc7f

def z1110 : W := mkw 0x02108d083311bb15 0x402108d083311bb1 0xfe0007803f13ff3c 0xefe0007803f13ff3

def z1111 : W := mkw 0x140a80001618a981 0x0140a80001618a98 0xfe0f86073e1cf9ce 0xefe0f86073e1cf9c

def z1112 : W := mkw 0x0fee676180000000 0x00fee67618000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1113 : W := mkw 0x8d2b30b640000000 0x08d2b30b64000000 0x0033b83800000000 0x00033b8380000000

def z1114 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0x6ff001f83fe03e09 0xf6ff001f83fe03e0

def z1115 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x3000004031133f3d 0x23000004031133f3

def z1116 : W := mkw 0x8dee7271c0000000 0x08dee7271c000000 0x0ff3f878c0000001 0x90ff3f878c000000

def z1117 : W := mkw 0x86cf77f7c0000000 0x086cf77f7c000000 0x803fffffc0000007 0xa803fffffc000000

def z1118 : W := mkw 0x8daf7097c0000000 0x08daf7097c000000 0x0ffff9ffc0000007 0xf0ffff9ffc000000

def z1119 : W := mkw 0x2b3005282b80b206 0x02b3005282b80b20 0x2ff001b83fe03801 0x92ff001b83fe0380

def z1120 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfff007fc3ff0ff0f 0xffff007fc3ff0ff0

def z1121 : W := mkw 0x0001109440000000 0x0000110944000000 0x0033f9b800000003 0xa0033f9b80000000

def z1122 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x30004004f1133f3a 0x030004004f1133f3

def z1123 : W := mkw 0x0010880831315f7d 0xc0010880831315f7 0x300000003113fff8 0x0300000003113fff

def z1124 : W := mkw 0x8fef77f7c0000060 0x88fef77f7c000006 0x8fffffffc00001f7 0xf8fffffffc00001f

def z1125 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xfe0f87833e1cf9c8 0xcfe0f87833e1cf9c

def z1126 : W := mkw 0x0f6b17f640000000 0x00f6b17f64000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1127 : W := mkw 0x12118d8e3311bb95 0x412118d8e3311bb9 0xb00007873113fffc 0x0b00007873113fff

def z1128 : W := mkw 0x8daf70b7c0000000 0x08daf70b7c000000 0x003ff83fc0000002 0x0003ff83fc000000

def z1129 : W := mkw 0x8f6b37f640000000 0x08f6b37f64000000 0x0ff3b9f800000001 0x90ff3b9f80000000

def z1130 : W := mkw 0x9fef77f7c608a981 0x09fef77f7c608a98 0xdfffffffce0cf9c7 0xfdfffffffce0cf9c

def z1131 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8fffffbb00000003 0xf8fffffbb0000000

def z1132 : W := mkw 0x301088083fb9ff9f 0x4301088083fb9ff9 0x700000003ffffff8 0x0700000003ffffff

def z1133 : W := mkw 0x0b60076000000000 0x00b6007600000000 0x8ff3fff800000007 0xf8ff3fff80000000

def z1134 : W := mkw 0x892130b440000000 0x0892130b44000000 0x0033f9fcc0000007 0xa0033f9fcc000000

def z1135 : W := mkw 0x9f2b35b64608a080 0x09f2b35b64608a08 0x0e33b9b80e000000 0x80e33b9b80e00000

def z1136 : W := mkw 0xcdbee803bddf0000 0x0cdbee803bddf000 0x6ffff8033fff000b 0xf6ffff8033fff000

def z1137 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0xeffffffffe00000f 0xfeffffffffe00000

def z1138 : W := mkw 0xefef77f7ceeee40a 0x0efef77f7ceeee40 0xcfffffffceecc007 0xfcfffffffceecc00

def z1139 : W := mkw 0x8faf75b7c0000000 0x08faf75b7c000000 0x0ffff9bfc0000003 0xf0ffff9bfc000000

def z1140 : W := mkw 0x2b7007682b80b206 0x02b7007682b80b20 0xeff007f83fe0380d 0xfeff007f83fe0380

def z1141 : W := mkw 0x820115b640000000 0x0820115b64000000 0x0033f9fcc0000007 0xa0033f9fcc000000

def z1142 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x2ff3f8003ff3000b 0xb2ff3f8003ff3000

def z1143 : W := mkw 0xcfef77f7c44e0000 0x0cfef77f7c44e000 0x8fffffffc00c0007 0xf8fffffffc00c000

def z1144 : W := mkw 0x3d7b82ee3db85f8f 0x03d7b82ee3db85f8 0x01ff807f01fc07c3 0x101ff807f01fc07c

def z1145 : W := mkw 0x0b7007602b80a000 0x00b7007602b80a00 0xfff007f83fe0f80d 0xffff007f83fe0f80

def z1146 : W := mkw 0x060a85001618a000 0x0060a85001618a00 0xfe0f87873e1cf9ce 0xefe0f87873e1cf9c

def z1147 : W := mkw 0x120115964200a981 0x0120115964200a98 0x9033ffffc000f9c7 0xa9033ffffc000f9c

def z1148 : W := mkw 0xaf6b37f64aa0e40a 0x0af6b37f64aa0e40 0xcff3bfb80ee0c000 0xdcff3bfb80ee0c00

def z1149 : W := mkw 0x601088083ffff66e 0x8601088083ffff66 0x700000003ffffff8 0x0700000003ffffff

def z1150 : W := mkw 0x0011109c61001204 0x00011109c6100120 0x3033f9fcf1133f3f 0xa3033f9fcf1133f3

def z1151 : W := mkw 0x804112f5c0000000 0x0804112f5c000000 0x0033f9fcc0000007 0xa0033f9fcc000000

def z1152 : W := mkw 0x8f6b37f640000000 0x08f6b37f64000000 0x8ff3bfb800000000 0xd8ff3bfb80000000

def z1153 : W := mkw 0x8fef77f7c4080000 0x08fef77f7c408000 0xcfffffffce0c0007 0xfcfffffffce0c000

def z1154 : W := mkw 0x0931109c69801b15 0x40931109c69801b1 0x7ff001fcffe03f3d 0xf7ff001fcffe03f3

def z1155 : W := mkw 0x060b05860200a000 0x0060b05860200a00 0xfe0f87873e1cf9ce 0xefe0f87873e1cf9c

def z1156 : W := mkw 0x8faf75b640000000 0x08faf75b64000000 0x0fffb9b800000000 0xd0fffb9b80000000

def z1157 : W := mkw 0x0001109440000000 0x0000110944000000 0x0033f9fcc0130137 0xa0033f9fcc013013

def z1158 : W := mkw 0x60d4ca483ffff60e 0x060d4ca483ffff60 0xf1cc46403ffffe0f 0x7f1cc46403ffffe0

def z1159 : W := mkw 0x8fef77f7c0460000 0x08fef77f7c046000 0xcfffffffc0ec0007 0xfcfffffffc0ec000

def z1160 : W := mkw 0xafef77f7caa0e40a 0x0afef77f7caa0e40 0xdfffffffcfe0c60f 0xfdfffffffcfe0c60

def z1161 : W := mkw 0x060b159640000000 0x0060b15964000000 0x0e33b9b800000000 0x80e33b9b80000000

def z1162 : W := mkw 0x9f2b35b64608a080 0x09f2b35b64608a08 0xce3fbfbb0e0cc0c0 0xcce3fbfbb0e0cc0c

def z1163 : W := mkw 0x8fef77f7c0460060 0x88fef77f7c046006 0x8fffffffc0030037 0xf8fffffffc003003

def z1164 : W := mkw 0x80857095c0000000 0x080857095c000000 0x0033f9fcc0000007 0xa0033f9fcc000000

def z1165 : W := mkw 0x4dae60000cce0000 0x04dae60000cce000 0x4fcff8000eec0002 0x54fcff8000eec000

def z1166 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x9fffffffc100060f 0xf9fffffffc100060

def z1167 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfffc07f83ffcfe0f 0xffffc07f83ffcfe0

def z1168 : W := mkw 0x8fee7773c0000000 0x08fee7773c000000 0x8ffffe7bc0000003 0xf8ffffe7bc000000

def z1169 : W := mkw 0x160b15964608a080 0x0160b15964608a08 0xce3fffffce0cc0c7 0xece3fffffce0cc0c

def z1170 : W := mkw 0x8def72f7c0664468 0x88def72f7c066446 0x01fff87fc1ff07f3 0x101fff87fc1ff07f

def z1171 : W := mkw 0x8fef77f7c0204408 0x08fef77f7c020440 0x8fffffffc1e00607 0xf8fffffffc1e0060

def z1172 : W := mkw 0x848f7097c0000000 0x0848f7097c000000 0x003ff87fc0000003 0x0003ff87fc000000

def z1173 : W := mkw 0x1010880835191b95 0x41010880835191b9 0x30000000311f3ff8 0x030000000311f3ff

def z1174 : W := mkw 0x0085509440000000 0x0008550944000000 0x01fff9fcc0000007 0xf01fff9fcc000000

def z1175 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x6ffff840ffff063b 0xf6ffff840ffff063

def z1176 : W := mkw 0x4dbee801bddf0060 0x84dbee801bddf006 0xfffffe07ffffc1ff 0xffffffe07ffffc1f

def z1177 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xeff007b83fe0f809 0xfeff007b83fe0f80

def z1178 : W := mkw 0x09a5709440000000 0x009a570944000000 0x01f3f9fcc0000007 0xb01f3f9fcc000000

def z1179 : W := mkw 0x4094c8083ddf1b15 0x44094c8083ddf1b1 0x71cc4044ffff3f3f 0x771cc4044ffff3f3

def z1180 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0xcfffffffc1e0000f 0xfcfffffffc1e0000

def z1181 : W := mkw 0xafee67638ae6e46a 0x8afee67638ae6e46 0xcfcc06030eecc0c0 0x5cfcc06030eecc0c

def z1182 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xfe0f87833e0cf8cc 0xefe0f87833e0cf8c

def z1183 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0x1e33f9fcc113073f 0xa1e33f9fcc113073

def z1184 : W := mkw 0x6fee67618eeee46a 0x86fee67618eeee46 0xcfcc06030eecc0c0 0x5cfcc06030eecc0c

def z1185 : W := mkw 0x493088003ddf0000 0x0493088003ddf000 0x6ff3f8003fff000b 0xf6ff3f8003fff000

def z1186 : W := mkw 0x0001109440000000 0x0000110944000000 0x0033f87cc0000003 0x00033f87cc000000

def z1187 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xbe0f87873e1cf9c6 0x8be0f87873e1cf9c

def z1188 : W := mkw 0x0d3a88003d990000 0x00d3a88003d99000 0x6ffff8003fff000b 0xf6ffff8003fff000

def z1189 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0xf033fffcf113ff3f 0xef033fffcf113ff3

def z1190 : W := mkw 0x9fef77f7c66ee4e8 0x89fef77f7c66ee4e 0xcfffffffceecc0c7 0xfcfffffffceecc0c

def z1191 : W := mkw 0x8fef77f7c0204468 0x88fef77f7c020446 0xdfffffffc01cc7ff 0xfdfffffffc01cc7f

def z1192 : W := mkw 0x101088083311bb95 0x4101088083311bb9 0x300000003113fff8 0x0300000003113fff

def z1193 : W := mkw 0x0dee626000000000 0x00dee62600000000 0x0ffff87800000003 0xf0ffff8780000000

def z1194 : W := mkw 0x0fef77f440000000 0x00fef77f44000000 0x8ffffffcc0000007 0xf8ffffffcc000000

def z1195 : W := mkw 0x8f6b37f7c0000000 0x08f6b37f7c000000 0x8e33bfbb00000000 0x88e33bfbb0000000

def z1196 : W := mkw 0x0930000029800000 0x0093000002980000 0x6ff3f8003fe0000b 0xf6ff3f8003fe0000

def z1197 : W := mkw 0x2b700769aba0f60e 0x02b700769aba0f60 0xfff007ffffe0fe0d 0xffff007ffffe0fe0

def z1198 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x6fffb8003fec0009 0xf6fffb8003fec000

def z1199 : W := mkw 0x8be577f7c0000000 0x08be577f7c000000 0x81f3ffffc0000007 0xb81f3ffffc000000

def z1200 : W := mkw 0x0010880831111b15 0x40010880831111b1 0xf00c0607311ffffe 0x6f00c0607311ffff

def z1201 : W := mkw 0x6dbee8283ddf1206 0x06dbee8283ddf120 0x6ffff8383fff000b 0xf6ffff8383fff000

def z1202 : W := mkw 0x8f2b35b7c0000000 0x08f2b35b7c000000 0x0e33b9bfc0000000 0x80e33b9bfc000000

def z1203 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0x9fffffffc1f3073f 0xf9fffffffc1f3073

def z1204 : W := mkw 0xcfef77f7ccce0000 0x0cfef77f7ccce000 0xcfffffffcfff000f 0xfcfffffffcfff000

def z1205 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x9fffffffc0000737 0xf9fffffffc000073

def z1206 : W := mkw 0x8faf75b7c0000000 0x08faf75b7c000000 0x0e3fb9bb00000000 0x80e3fb9bb0000000

def z1207 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xfe0c07873e1cf9cc 0x4fe0c07873e1cf9c

def z1208 : W := mkw 0x0010880831315f1d 0x40010880831315f1 0x7000000031f3ff38 0x07000000031f3ff3

def z1209 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0x0ff3b9b800000001 0xf0ff3b9b80000000

def z1210 : W := mkw 0x8fef77f7c0000901 0x08fef77f7c000090 0x9fffffffc0003907 0xf9fffffffc000390

def z1211 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0xdfffffffc11fc7ff 0xfdfffffffc11fc7f

def z1212 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x9fffffffc010010f 0xf9fffffffc010010

def z1213 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfff007fcffe0ff3d 0xffff007fcffe0ff3

def z1214 : W := mkw 0x00c4424180664468 0x800c442418066446 0xd1fc47ffc1ffc7ff 0xfd1fc47ffc1ffc7f

def z1215 : W := mkw 0x0000101040000000 0x0000010104000000 0x0033f878c0000003 0xa0033f878c000000

def z1216 : W := mkw 0x401088083ddf1b15 0x4401088083ddf1b1 0x600000003fff3808 0x0600000003fff380

def z1217 : W := mkw 0x00c4424180664468 0x800c442418066446 0xd1fffe47c1ffc7ff 0xfd1fffe47c1ffc7f

def z1218 : W := mkw 0x8dae703040000000 0x08dae70304000000 0x0ffff83800000003 0xf0ffff8380000000

def z1219 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0x2ff001b83ee03800 0x92ff001b83ee0380

def z1220 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xffcf87873ffcf9cf 0xfffcf87873ffcf9c

def z1221 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x0000000001130730 0x0000000000113073

def z1222 : W := mkw 0x0085509440460000 0x0008550944046000 0x41fff9fcc1ff000f 0xf41fff9fcc1ff000

def z1223 : W := mkw 0x160b9d965619a991 0x4160b9d965619a99 0xfe0fffc7ff1fffff 0xefe0fffc7ff1ffff

def z1224 : W := mkw 0x4d3aa8003ddf0000 0x04d3aa8003ddf000 0x6ff3b8003fff0009 0xf6ff3b8003fff000

def z1225 : W := mkw 0x0001109440000000 0x0000110944000000 0x1033f9fcc0000737 0xa1033f9fcc000073

def z1226 : W := mkw 0x040b109440000000 0x0040b10944000000 0x0e3ff9fcc0000007 0xe0e3ff9fcc000000

def z1227 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xfe0fc7873f1ff9cf 0xefe0fc7873f1ff9c

def z1228 : W := mkw 0x0b2115b440000000 0x00b2115b44000000 0x0e33b9b800000000 0x80e33b9b80000000

def z1229 : W := mkw 0x0dae600008800000 0x00dae60000880000 0x4ffff8000ee00003 0xf4ffff8000ee0000

def z1230 : W := mkw 0x29f45a79e9e7567e 0xc29f45a79e9e7567 0x01f07878c1e30631 0x101f07878c1e3063

def z1231 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xeff007f83ee0f805 0xfeff007f83ee0f80

def z1232 : W := mkw 0x8def72f7c0000000 0x08def72f7c000000 0x0ffff87fc0000003 0xf0ffff87fc000000

def z1233 : W := mkw 0x025007482320f60c 0x0025007482320f60 0xfff007f83fe0fe0d 0xffff007f83fe0fe0

def z1234 : W := mkw 0x00c4424180664468 0x800c442418066446 0xd1cc0647c1ffc7fc 0x5d1cc0647c1ffc7f

def z1235 : W := mkw 0x0094c809b1571b75 0xc0094c809b1571b7 0x300c4007f11f3ffa 0x0300c4007f11f3ff

def z1236 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xfe0fc787fe1ff9fe 0xefe0fc787fe1ff9f

def z1237 : W := mkw 0xdfef77f7cecea080 0x0dfef77f7cecea08 0xcfffffffceecc0c7 0xfcfffffffceecc0c

def z1238 : W := mkw 0x82c557f7c0000000 0x082c557f7c000000 0x81ffffffc0000007 0xf81ffffffc000000

def z1239 : W := mkw 0x8fef77f7c220e408 0x08fef77f7c220e40 0xffffffffffe0fe0f 0xfffffffffffe0fe0

def z1240 : W := mkw 0x4d3aa8003d990000 0x04d3aa8003d99000 0x2ff3b8003fe00001 0x92ff3b8003fe0000

def z1241 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x6ffff804ffff013b 0xf6ffff804ffff013

def z1242 : W := mkw 0x9fef77f7c200a981 0x09fef77f7c200a98 0x8fffffffc0003807 0xf8fffffffc000380

def z1243 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8ff3fff8c0000005 0xf8ff3fff8c000000

def z1244 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0xeffffe033fffc0cb 0xfeffffe033fffc0c

def z1245 : W := mkw 0x06cf57d7c0000000 0x006cf57d7c000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1246 : W := mkw 0x0001109440000000 0x0000110944000000 0x1033f9fcc100060f 0xa1033f9fcc100060

def z1247 : W := mkw 0x0001109440000901 0x0000110944000090 0x1033f9fcc0003907 0xa1033f9fcc000390

def z1248 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfff047f83ff3fe0f 0xffff047f83ff3fe0

def z1249 : W := mkw 0x8f6b37f640204408 0x08f6b37f64020440 0xdff3bff801e0c60d 0xfdff3bff801e0c60

def z1250 : W := mkw 0x8be577f5c0000000 0x08be577f5c000000 0x8ff3fffcc0000007 0xf8ff3fffcc000000

def z1251 : W := mkw 0x0fae652000000000 0x00fae65200000000 0x0ffff9b800000003 0xf0ffff9b80000000

def z1252 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfff007ff3fe0ffcd 0xffff007ff3fe0ffc

def z1253 : W := mkw 0x6b702f682ba1f60e 0x06b702f682ba1f60 0xfff03ff83fe0fe0d 0xffff03ff83fe0fe0

def z1254 : W := mkw 0x9fef77f7c4080080 0x09fef77f7c408008 0x8fffffffc00c00c7 0xf8fffffffc00c00c

def z1255 : W := mkw 0x0001109440000000 0x0000110944000000 0x1033f9fcc010010f 0xa1033f9fcc010010

def z1256 : W := mkw 0x8dee7271c0664468 0x88dee7271c066446 0xdffffe7fc1ffc7ff 0xfdffffe7fc1ffc7f

def z1257 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8ffffe7fc0000003 0x58ffffe7fc000000

def z1258 : W := mkw 0x0001109440664468 0x8000110944066446 0x5033f9fcc1ffc7ff 0xa5033f9fcc1ffc7f

def z1259 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x303ff9fff11f3fff 0xa303ff9fff11f3ff

def z1260 : W := mkw 0x0001109440000000 0x0000110944000000 0x0033b9fcc0000004 0x80033b9fcc000000

def z1261 : W := mkw 0x8d2a303040000000 0x08d2a30304000000 0x0e33b83800000000 0x80e33b8380000000

def z1262 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0xde3fbfbf001cc1ce 0xede3fbfbf001cc1c

def z1263 : W := mkw 0x101088083719bb95 0x4101088083719bb9 0x300000003f133f38 0x0300000003f133f3

def z1264 : W := mkw 0xcfaf75b64cce0000 0x0cfaf75b64cce000 0x4fffb9b80eec0000 0xd4fffb9b80eec000

def z1265 : W := mkw 0x8f6b37f7c0204468 0x88f6b37f7c020446 0x9e33bfffc000c7f4 0x89e33bfffc000c7f

def z1266 : W := mkw 0x0b6117f440204408 0x00b6117f44020440 0xdff3fffcc1f3c73f 0xfdff3fffcc1f3c73

def z1267 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x30000004f1133f38 0x030000004f1133f3

def z1268 : W := mkw 0x4daee8001cdf0000 0x04daee8001cdf000 0x4fcff8000fff000b 0x74fcff8000fff000

def z1269 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x4ffff8000fff0003 0x54ffff8000fff000

def z1270 : W := mkw 0x401088083ddf1214 0x4401088083ddf121 0x600000003fff0638 0x0600000003fff063

def z1271 : W := mkw 0x4dbe680029c70000 0x04dbe680029c7000 0x6ffff8003fe3000b 0xf6ffff8003fe3000

def z1272 : W := mkw 0x448ff894545f0911 0x4448ff894545f091 0x000ff800001f0002 0x0000ff800001f000

def z1273 : W := mkw 0x09b4c80039d70000 0x009b4c80039d7000 0x6ffff8003fff000b 0xf6ffff8003fff000

def z1274 : W := mkw 0x8fee7771c0000000 0x08fee7771c000000 0x8ffffff8c0000007 0xf8ffffff8c000000

def z1275 : W := mkw 0x040b109640000000 0x0040b10964000000 0x003ff9ffc0000007 0xa003ff9ffc000000

def z1276 : W := mkw 0x201088083331ff1f 0x4201088083331ff1 0x300000003113ff38 0x0300000003113ff3

def z1277 : W := mkw 0x160b85861618a981 0x0160b85861618a98 0xfe0f87873e0cf9c4 0xcfe0f87873e0cf9c

def z1278 : W := mkw 0x10108808377ffffd 0xc10108808377ffff 0x700000003ffffff8 0x0700000003ffffff

def z1279 : W := mkw 0x89e572f5c0000000 0x089e572f5c000000 0x01f3f9f8c0000001 0x901f3f9f8c000000

def z1280 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x2ffff8003fff0003 0x92ffff8003fff000

def z1281 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0x0e3fb9bf00000002 0x80e3fb9bf0000000

def z1282 : W := mkw 0x124117dfc220fffd 0xc124117dfc220fff 0x900007ffc000fff4 0x0900007ffc000fff

def z1283 : W := mkw 0x0def72d5c0664468 0x80def72d5c066446 0xdfffffffc1ffc7ff 0xfdfffffffc1ffc7f

def z1284 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfffc07fb3fecfecd 0xffffc07fb3fecfec

def z1285 : W := mkw 0x824117f7c0000000 0x0824117f7c000000 0x8033bfffc0000004 0x88033bfffc000000

def z1286 : W := mkw 0x4dbe60002dce0000 0x04dbe60002dce000 0x6ffff8003fec000b 0xf6ffff8003fec000

def z1287 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x70000000311ffff8 0x070000000311ffff

def z1288 : W := mkw 0x8fef77f7c0204408 0x08fef77f7c020440 0xdfffffffc1fcc7cf 0xfdfffffffc1fcc7c

def z1289 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x3000400031133f3b 0x23000400031133f3

def z1290 : W := mkw 0x8f2b35b640000000 0x08f2b35b64000000 0x8e3fbfbb00000000 0xc8e3fbfbb0000000

def z1291 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0xfffffe003fffc00f 0xffffffe003fffc00

def z1292 : W := mkw 0x0daf709440460000 0x00daf70944046000 0x5ffff9fcc1ff073f 0xf5ffff9fcc1ff073

def z1293 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x2033f9fcf1133f33 0x82033f9fcf1133f3

def z1294 : W := mkw 0x00c4424180664468 0x800c442418066446 0xf1cc47c7f1ffffff 0xff1cc47c7f1fffff

def z1295 : W := mkw 0xafef77f7ca80a002 0x0afef77f7ca80a00 0x8fffffffce000007 0xf8fffffffce00000

def z1296 : W := mkw 0x096112f440000000 0x0096112f44000000 0x01f3f9fcc0000007 0xb01f3f9fcc000000

def z1297 : W := mkw 0x89e572f5c0000000 0x089e572f5c000000 0x81ffffffc0000007 0xf81ffffffc000000

def z1298 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x0ff3f9fcc0000007 0xb0ff3f9fcc000000

def z1299 : W := mkw 0x4dbee801bddf0060 0x84dbee801bddf006 0x7ffff847ffff07ff 0xf7ffff847ffff07f

def z1300 : W := mkw 0x29f44269a9e6566e 0x829f44269a9e6566 0x01f0007801e00601 0x101f0007801e0060

def z1301 : W := mkw 0x0be557f5c0000000 0x00be557f5c000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1302 : W := mkw 0x401088083d991b15 0x4401088083d991b1 0x200000003e003800 0x0200000003e00380

def z1303 : W := mkw 0x2b700769aba0f66e 0x82b700769aba0f66 0xfff007f8ffe0fe3d 0xffff007f8ffe0fe3

def z1304 : W := mkw 0x0010880831111214 0x4001088083111121 0x2000000031130638 0x0200000003113063

def z1305 : W := mkw 0x00d4ca49b1775f7d 0xc00d4ca49b1775f7 0x31c04040f1f33f39 0x131c04040f1f33f3

def z1306 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x7ffff8003fffc1cb 0xf7ffff8003fffc1c

def z1307 : W := mkw 0x004112d440204408 0x0004112d44020440 0xd1f3fffcc1e0c60f 0xfd1f3fffcc1e0c60

def z1308 : W := mkw 0x840b309640000000 0x0840b30964000000 0x0033f9fcc0000007 0xa0033f9fcc000000

def z1309 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0x3033f9f8f1033e3d 0xa3033f9f8f1033e3

def z1310 : W := mkw 0x160b8d861619a981 0x0160b8d861619a98 0xfe0fff873e1ff9ce 0xefe0fff873e1ff9c

def z1311 : W := mkw 0x0201159440000000 0x0020115944000000 0x8e33fffcc0000007 0xe8e33fffcc000000

def z1312 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x81ffffffc0000007 0x181ffffffc000000

def z1313 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0xcfffffffc1efc6f7 0xfcfffffffc1efc6f

def z1314 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0x8fffffffc0e00007 0xf8fffffffc0e0000

def z1315 : W := mkw 0xbfef77f7cea8e48a 0x0bfef77f7cea8e48 0xcfffffffceecc0c7 0xfcfffffffceecc0c

def z1316 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfff047f8ffe3fe3d 0xffff047f8ffe3fe3

def z1317 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0xcfffffffc1ffc0cf 0xfcfffffffc1ffc0c

def z1318 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0xcfffffffc00cc0c7 0xfcfffffffc00cc0c

def z1319 : W := mkw 0x3f3b9dbe7f99bb97 0x43f3b9dbe7f99bb9 0x2e33b9b83e003800 0x82e33b9b83e00380

def z1320 : W := mkw 0x201088083b91bb17 0x4201088083b91bb1 0x300000003f133f38 0x0300000003f133f3

def z1321 : W := mkw 0x224117fc4220ff1f 0x4224117fc4220ff1 0x900007f80000fe04 0x0900007f80000fe0

def z1322 : W := mkw 0x8f6b37f640000000 0x08f6b37f64000000 0x8ff3fffcc0000007 0xf8ff3fffcc000000

def z1323 : W := mkw 0x0010880831111b15 0x40010880831111b1 0x2000000031133808 0x0200000003113380

def z1324 : W := mkw 0x8fef77f7c0000000 0x08fef77f7c000000 0x8e3fffffc0000006 0x88e3fffffc000000

def z1325 : W := mkw 0x0011989c71111b15 0x40011989c71111b1 0xb033fffff113ffff 0xab033fffff113fff

def z1326 : W := mkw 0x4dbee8003ddf0060 0x84dbee8003ddf006 0x6ffff8003fff01fb 0xf6ffff8003fff01f

def z1327 : W := mkw 0x160a05020608a080 0x0160a05020608a08 0xfe0c06033e0cf8c8 0x4fe0c06033e0cf8c

def z1328 : W := mkw 0x8fef77f7c0460000 0x08fef77f7c046000 0x8fffffffc1e30007 0xf8fffffffc1e3000

def z1329 : W := mkw 0x8fef77f640000000 0x08fef77f64000000 0x8ffffff800000007 0xf8ffffff80000000

def z1330 : W := mkw 0x8faf75b640000000 0x08faf75b64000000 0x0ffff9fcc0000007 0xf0ffff9fcc000000

def z1331 : W := mkw 0x8fef77f7c200a000 0x08fef77f7c200a00 0x9fffffffc000f807 0xf9fffffffc000f80

def z1332 : W := mkw 0x4dbee8003ddf0000 0x04dbee8003ddf000 0x7ffff9803fff380f 0xf7ffff9803fff380

def z1333 : W := mkw 0x048f709440000000 0x0048f70944000000 0x003ff9fcc0000007 0xa003ff9fcc000000

def z1334 : W := mkw 0x00c4424180664468 0x800c442418066446 0xc1cc4647c1ffc7f3 0x5c1cc4647c1ffc7f

def z1335 : W := mkw 0x2b7007682ba0f60e 0x02b7007682ba0f60 0xfff007f83ffcffcd 0xffff007f83ffcffc

def z1336 : W := mkw 0x8fef77f7c0664468 0x88fef77f7c066446 0x9fffffffc01fc7f7 0xf9fffffffc01fc7f

def z1337 : W := mkw 0x2b3005282b80b206 0x02b3005282b80b20 0x7ff001f83fe03e0d 0xf7ff001f83fe03e0

def z1338 : W := mkw 0x8def72f5c0000000 0x08def72f5c000000 0x0ffff9fcc0000007 0xf0ffff9fcc000000

def z1339 : W := mkw 0x0011888c31111b15 0x40011888c31111b1 0x3000018431133f3c 0x03000018431133f3

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z7,z8,z4,z5])],[(0,[z6,z1,z2,z7,z4,z5,z9]),(0,[z10,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z11,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z12,z5]),(0,[z0,z6,z1,z2,z7,z4,z5]),(1,[z6,z1,z2,z7,z4,z13]),(0,[z6,z1,z14,z2,z7,z4,z13])],[(0,[z15,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z16]),(0,[z17,z6,z1,z18,z2,z7,z4]),(1,[z19,z6,z20,z7,z4,z5])],[(0,[z6,z1,z21,z2,z22,z7,z4]),(0,[z17,z23,z6,z1,z2,z7,z4]),(0,[z24,z6,z1,z2,z7,z4,z5]),(0,[z6,z25,z1,z2,z7,z4,z5]),(0,[z6,z1,z26,z2,z7,z4,z5]),(0,[z6,z1,z27,z2,z7,z4,z5])],[(0,[z6,z1,z2,z28,z7,z4,z5]),(0,[z29,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z30,z4,z5]),(0,[z6,z1,z2,z7,z4,z31,z32]),(0,[z33,z34,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z35,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z36,z13])],[(0,[z6,z1,z2,z7,z4,z37,z5]),(0,[z17,z6,z1,z2,z38,z7,z4]),(0,[z6,z39,z1,z2,z7,z4,z40]),(0,[z41,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z42,z7,z4,z5])],[(0,[z6,z1,z2,z7,z4,z43,z5]),(0,[z6,z1,z44,z2,z7,z4,z5]),(1,[z6,z1,z2,z7,z5,z45])],[(0,[z6,z1,z2,z3,z7,z4,z31]),(1,[z6,z1,z2,z7,z4,z31])]],
   [[(0,[z6,z1,z46,z2,z7,z4,z5]),(0,[z6,z1,z47,z48,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z5,z49]),(0,[z19,z6,z1,z2,z7,z4,z31]),(0,[z6,z50,z1,z2,z7,z4,z5]),(0,[z6,z1,z51,z52,z2,z7,z4])],[(0,[z23,z6,z1,z2,z7,z4,z13]),(0,[z53,z6,z1,z2,z7,z4,z5]),(0,[z54,z6,z1,z2,z7,z4,z5]),(0,[z6,z55,z1,z20,z7,z4,z5]),(0,[z6,z56,z1,z2,z57,z4,z5]),(0,[z6,z1,z2,z7,z4,z58,z59]),(1,[z6,z1,z60,z2,z7,z4])],[(0,[z6,z1,z2,z7,z4,z5,z61]),(0,[z23,z1,z18,z2,z7,z4,z5]),(0,[z6,z1,z2,z62,z7,z4,z5]),(0,[z17,z6,z1,z2,z63,z7,z4]),(0,[z6,z1,z2,z7,z4,z64,z13]),(0,[z65,z6,z1,z2,z7,z4,z5])],[(0,[z6,z66,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z67]),(0,[z68,z6,z1,z2,z7,z4,z13]),(0,[z69,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z3,z7,z4,z70]),(0,[z6,z1,z2,z7,z71,z4,z5]),(0,[z34,z6,z1,z72,z2,z7,z4]),(0,[z6,z1,z73,z2,z7,z4,z5]),(0,[z6,z1,z74,z2,z7,z4,z5])],[(1,[z75,z1,z22,z7,z4,z5]),(0,[z23,z6,z1,z18,z7,z4,z5]),(1,[z6,z1,z2,z76,z7,z5]),(0,[z6,z1,z2,z7,z77,z4,z5]),(0,[z6,z1,z2,z7,z78,z4,z5]),(0,[z6,z1,z79,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z80,z4,z5]),(0,[z34,z6,z1,z2,z7,z4,z81]),(1,[z6,z1,z82,z2,z7,z4]),(0,[z17,z6,z1,z83,z2,z7,z4]),(0,[z6,z1,z2,z7,z84,z4,z13]),(0,[z6,z56,z1,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z31,z85])],[(0,[z86,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z87,z5]),(0,[z0,z34,z6,z1,z2,z7,z4]),(0,[z6,z1,z88,z2,z7,z4,z5]),(0,[z19,z6,z1,z2,z89,z4,z5]),(0,[z6,z90,z1,z2,z63,z4,z5]),(0,[z6,z1,z2,z91,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z92,z13]),(0,[z6,z1,z83,z2,z7,z36,z5])],[(0,[z23,z6,z1,z2,z7,z4,z31]),(0,[z6,z1,z2,z7,z4,z5,z93]),(0,[z34,z6,z1,z2,z7,z4,z36]),(0,[z6,z1,z2,z7,z4,z5,z94])]],
   [[(0,[z95,z6,z1,z2,z7,z4,z5]),(0,[z6,z96,z1,z2,z7,z4,z5]),(1,[z6,z1,z2,z7,z4,z12]),(0,[z6,z1,z2,z7,z97,z98,z5]),(1,[z17,z6,z1,z2,z7,z4]),(0,[z6,z99,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z100,z4,z13]),(0,[z6,z1,z101,z2,z7,z4,z59])],[(0,[z19,z17,z6,z1,z2,z7,z4]),(0,[z6,z1,z102,z2,z7,z4,z5]),(1,[z6,z1,z103,z7,z4,z5]),(0,[z6,z56,z1,z2,z7,z104,z5]),(0,[z6,z1,z105,z2,z7,z4,z31])],[(0,[z106,z6,z1,z2,z107,z4,z5]),(0,[z6,z1,z2,z7,z4,z108,z5]),(0,[z109,z17,z6,z1,z2,z7,z4]),(0,[z110,z17,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z111,z4,z5]),(0,[z6,z1,z2,z91,z7,z104,z5])],[(1,[z6,z1,z2,z7,z4,z112]),(0,[z6,z1,z2,z7,z84,z4,z31]),(0,[z6,z1,z113,z2,z7,z4,z5]),(0,[z6,z56,z1,z2,z7,z4,z31]),(0,[z6,z1,z114,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z4,z5,z115]),(0,[z6,z1,z2,z7,z98,z104,z5]),(0,[z6,z1,z2,z7,z98,z92,z5]),(0,[z6,z1,z2,z7,z4,z104,z31]),(0,[z6,z1,z2,z91,z7,z4,z31]),(0,[z6,z1,z2,z7,z4,z92,z31]),(0,[z6,z1,z2,z116,z7,z4,z5])],[(0,[z6,z1,z2,z7,z117,z4,z13]),(0,[z0,z6,z1,z83,z2,z4,z5]),(0,[z34,z6,z1,z2,z7,z84,z4]),(0,[z118,z6,z1,z2,z7,z4,z5]),(0,[z119,z6,z1,z2,z7,z4,z5]),(0,[z6,z55,z1,z2,z7,z4,z31]),(0,[z6,z1,z2,z7,z4,z120,z31]),(0,[z6,z1,z2,z7,z4,z121,z5]),(0,[z6,z1,z2,z7,z122,z4,z5]),(0,[z6,z1,z52,z2,z7,z4,z59])],[(1,[z86,z1,z2,z117,z4,z5]),(0,[z6,z1,z2,z7,z4,z123,z5]),(0,[z6,z1,z2,z7,z124,z4,z5]),(0,[z53,z34,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z98,z4,z31]),(0,[z17,z34,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z125]),(0,[z126,z6,z1,z2,z7,z4,z5])],[(0,[z127,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z128,z2,z22,z7,z4])]],
   [[(0,[z6,z129,z1,z2,z7,z4,z130]),(0,[z17,z6,z6,z1,z2,z7,z4]),(1,[z54,z1,z2,z7,z4,z5]),(1,[z6,z1,z2,z7,z4,z131]),(0,[z6,z1,z132,z2,z7,z4,z13]),(0,[z6,z1,z105,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z133,z5])],[(0,[z6,z1,z2,z7,z4,z134,z5]),(0,[z6,z1,z2,z135,z7,z4,z5]),(0,[z19,z54,z1,z2,z7,z4,z5])],[(0,[z6,z1,z136,z2,z7,z4,z5]),(0,[z17,z6,z1,z2,z137,z7,z4]),(1,[z6,z90,z2,z84,z4,z5]),(0,[z6,z1,z2,z7,z4,z13,z138]),(0,[z6,z1,z60,z2,z7,z4,z36])],[(0,[z17,z6,z1,z2,z7,z117,z4]),(0,[z139,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z104,z5]),(0,[z6,z1,z2,z7,z4,z140,z5]),(0,[z6,z1,z2,z7,z4,z5,z141])],[(0,[z142,z68,z6,z1,z2,z7,z4]),(0,[z143,z6,z1,z2,z7,z4,z5]),(0,[z17,z6,z1,z52,z2,z7,z4]),(0,[z144,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z31,z138]),(0,[z6,z1,z145,z7,z146,z4,z5]),(0,[z6,z1,z2,z7,z147,z4,z5]),(0,[z6,z1,z148,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z149]),(0,[z6,z1,z2,z7,z4,z5,z45])],[(0,[z6,z1,z2,z7,z98,z4,z5]),(0,[z139,z17,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z150,z5]),(1,[z6,z1,z2,z7,z151,z5]),(0,[z6,z2,z7,z4,z31,z5,z13]),(0,[z6,z1,z152,z2,z7,z4,z5]),(0,[z153,z6,z1,z2,z7,z4,z5]),(0,[z6,z154,z1,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z155,z4,z5]),(0,[z6,z1,z2,z7,z156,z4,z5]),(0,[z157,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z38,z4,z58,z5])],[(0,[z34,z6,z1,z48,z2,z7,z4]),(0,[z6,z1,z2,z158,z7,z4,z5]),(0,[z17,z6,z1,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z5,z159])]],
   [[(0,[z23,z1,z48,z2,z7,z4,z5]),(0,[z6,z1,z160,z22,z7,z4,z5]),(0,[z6,z1,z101,z22,z7,z4,z5]),(0,[z1,z2,z3,z7,z117,z4,z5]),(0,[z6,z1,z2,z7,z4,z161,z5]),(0,[z6,z1,z162,z2,z7,z4,z5]),(0,[z6,z1,z2,z163,z7,z4,z5]),(0,[z6,z1,z164,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z4,z165,z5]),(0,[z6,z1,z22,z7,z4,z5,z166]),(0,[z6,z1,z2,z7,z167,z4,z5]),(0,[z6,z1,z168,z2,z7,z4,z5]),(0,[z34,z6,z1,z2,z169,z7,z4]),(0,[z6,z1,z52,z2,z7,z170,z5]),(0,[z171,z6,z1,z2,z7,z4,z5])],[(0,[z172,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z173,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z174,z5]),(0,[z175,z6,z1,z2,z7,z4,z5]),(0,[z6,z176,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z177,z7,z4,z5])],[(0,[z178,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z179,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z180,z5])],[(0,[z6,z1,z22,z20,z7,z4,z5]),(1,[z6,z1,z2,z7,z181,z5]),(1,[z6,z1,z2,z182,z4,z5])],[(0,[z17,z6,z1,z2,z7,z4,z183]),(0,[z34,z6,z1,z2,z7,z170,z4]),(0,[z6,z184,z1,z2,z7,z4,z5]),(1,[z33,z6,z2,z7,z4,z31]),(0,[z33,z6,z2,z7,z4,z31,z5])],[(0,[z17,z6,z1,z2,z7,z30,z4]),(0,[z6,z1,z185,z2,z7,z4,z31]),(1,[z6,z1,z2,z7,z170,z92])],[(0,[z186,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z187]),(0,[z6,z1,z2,z7,z4,z188,z5]),(0,[z6,z189,z1,z2,z7,z4,z5]),(0,[z190,z6,z1,z2,z7,z4,z5]),(0,[z6,z191,z1,z2,z7,z4,z5])]],
   [[(0,[z192,z6,z1,z2,z7,z4,z5]),(0,[z34,z6,z1,z2,z7,z193,z5]),(0,[z34,z6,z1,z2,z38,z7,z4]),(0,[z194,z6,z1,z2,z7,z4,z5])],[(0,[z6,z195,z1,z2,z7,z4,z5]),(0,[z17,z6,z1,z2,z7,z4,z64]),(1,[z6,z1,z137,z7,z4,z5]),(1,[z6,z196,z2,z7,z104,z5]),(0,[z6,z1,z2,z7,z4,z5,z13]),(0,[z6,z1,z197,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z4,z13,z198]),(1,[z6,z1,z105,z145,z4,z5]),(0,[z6,z1,z2,z97,z4,z36,z5])],[(0,[z199,z6,z1,z83,z2,z7,z5]),(0,[z6,z1,z2,z7,z81,z36,z5]),(0,[z17,z6,z1,z82,z2,z7,z4]),(0,[z6,z196,z1,z2,z7,z4,z5]),(0,[z6,z1,z83,z2,z91,z4,z5])],[(0,[z6,z1,z2,z7,z97,z81,z5]),(0,[z200,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z201]),(0,[z6,z1,z2,z7,z4,z5,z202]),(0,[z6,z1,z2,z7,z4,z5,z203]),(0,[z6,z1,z52,z2,z7,z4,z92])],[(0,[z6,z1,z18,z2,z7,z4,z13]),(0,[z204,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z205,z2,z7,z4,z31]),(0,[z6,z1,z206,z2,z7,z4,z31]),(0,[z6,z1,z2,z7,z4,z5,z207]),(0,[z6,z1,z185,z2,z7,z4,z5]),(0,[z6,z1,z208,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z209,z5])],[(0,[z210,z6,z1,z2,z7,z4,z5]),(0,[z106,z6,z1,z2,z7,z4,z9]),(0,[z17,z17,z6,z1,z2,z7,z4]),(0,[z211,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z212,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z13,z213]),(0,[z214,z6,z1,z2,z7,z4,z31]),(0,[z6,z1,z2,z215,z7,z4,z5])],[(0,[z86,z6,z1,z2,z117,z4,z5]),(0,[z172,z34,z6,z1,z2,z7,z4]),(0,[z34,z6,z55,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z216,z5])]],
   [[(0,[z106,z6,z1,z2,z28,z4,z5]),(0,[z6,z1,z2,z217,z7,z4,z5]),(0,[z178,z34,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z5,z218]),(0,[z6,z56,z1,z2,z182,z4,z5]),(0,[z6,z219,z1,z2,z7,z4,z5])],[(0,[z6,z1,z2,z63,z7,z4,z13])],[(0,[z6,z1,z2,z22,z7,z4,z13]),(0,[z53,z6,z1,z2,z91,z7,z5]),(0,[z6,z1,z83,z2,z63,z4,z5]),(0,[z6,z1,z2,z220,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z221])],[(0,[z6,z129,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z222,z4,z5]),(0,[z223,z6,z1,z2,z7,z4,z5]),(0,[z6,z90,z1,z2,z7,z4,z224]),(0,[z6,z1,z2,z7,z4,z151,z5]),(0,[z6,z1,z2,z7,z225,z4,z5]),(0,[z6,z1,z2,z7,z226,z4,z5])],[(0,[z6,z1,z2,z7,z4,z227,z5]),(0,[z186,z34,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z5,z228])],[(0,[z214,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z229,z4,z5]),(0,[z6,z1,z2,z7,z81,z92,z5]),(0,[z6,z1,z2,z7,z4,z13,z166]),(0,[z6,z1,z2,z7,z4,z230,z5]),(0,[z6,z1,z2,z231,z7,z4,z5])],[(0,[z6,z1,z232,z2,z7,z4,z5]),(0,[z17,z1,z2,z7,z4,z5,z32]),(0,[z6,z1,z2,z7,z4,z5,z233])],[(0,[z214,z17,z6,z1,z2,z7,z4]),(0,[z6,z1,z160,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z131,z5]),(0,[z6,z1,z2,z63,z7,z4,z31]),(0,[z6,z1,z185,z2,z7,z4,z234]),(0,[z6,z1,z2,z7,z4,z235,z5]),(0,[z6,z1,z2,z7,z236,z4,z5])]],
   [[(0,[z6,z1,z2,z7,z237,z4,z5]),(0,[z6,z1,z2,z84,z146,z4,z5]),(0,[z6,z1,z2,z84,z97,z4,z5]),(0,[z6,z1,z2,z238,z7,z4,z5]),(0,[z6,z1,z2,z7,z239,z4,z5]),(0,[z6,z1,z2,z7,z5,z45,z85])],[(0,[z6,z1,z2,z240,z7,z4,z5]),(0,[z241,z6,z1,z2,z7,z4,z5])],[(0,[z242,z6,z1,z2,z7,z4,z5]),(0,[z17,z6,z56,z1,z2,z7,z4])],[(0,[z6,z1,z2,z7,z243,z4,z5]),(0,[z199,z6,z1,z2,z7,z4,z5]),(0,[z34,z6,z6,z1,z2,z7,z4]),(0,[z6,z1,z244,z2,z7,z4,z5]),(0,[z6,z39,z1,z2,z7,z4,z13]),(0,[z6,z1,z14,z7,z4,z5,z166]),(0,[z6,z1,z245,z2,z7,z4,z5])],[(0,[z6,z246,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z247,z4,z5]),(0,[z0,z6,z1,z2,z97,z4,z5]),(0,[z6,z1,z2,z20,z7,z4,z31]),(1,[z6,z1,z2,z91,z97,z5]),(1,[z6,z1,z51,z2,z4,z85]),(0,[z6,z1,z52,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z4,z5,z248]),(0,[z6,z1,z2,z7,z4,z249,z5]),(0,[z6,z1,z2,z7,z250,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z251])],[(0,[z17,z6,z252,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z253,z4,z5]),(0,[z6,z1,z2,z7,z254,z4,z5])],[(0,[z142,z6,z1,z2,z7,z4,z5]),(1,[z6,z1,z255,z2,z7,z5]),(0,[z34,z6,z1,z52,z2,z7,z4]),(0,[z6,z1,z2,z145,z63,z4,z5]),(0,[z6,z1,z256,z2,z7,z4,z5]),(0,[z6,z1,z72,z2,z7,z4,z31]),(0,[z6,z1,z101,z7,z4,z59,z5]),(1,[z6,z1,z52,z2,z7,z138])]],
   [[(0,[z1,z18,z2,z22,z7,z4,z5]),(0,[z6,z1,z2,z7,z257,z4,z5]),(0,[z6,z1,z2,z7,z4,z258,z5]),(0,[z259,z6,z1,z2,z7,z4,z5])],[(0,[z6,z1,z18,z2,z7,z4,z248]),(0,[z6,z1,z2,z7,z4,z5,z260]),(0,[z261,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z101,z2,z7,z4,z166]),(0,[z262,z6,z1,z2,z7,z4,z5])],[(0,[z23,z6,z1,z22,z7,z4,z5]),(0,[z6,z263,z1,z2,z7,z4,z5]),(0,[z34,z6,z1,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z264,z4,z13]),(0,[z6,z1,z2,z7,z4,z5,z265]),(0,[z6,z1,z2,z7,z4,z266,z5])],[(0,[z6,z1,z48,z2,z7,z4,z13]),(0,[z86,z6,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z3,z7,z4,z5]),(0,[z6,z1,z2,z20,z7,z4,z5]),(1,[z6,z1,z2,z7,z4,z267])],[(0,[z6,z1,z2,z7,z4,z31,z268]),(0,[z6,z1,z269,z2,z7,z4,z5]),(0,[z6,z270,z1,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z4,z271,z5]),(0,[z6,z1,z2,z7,z4,z13,z32]),(0,[z272,z6,z1,z2,z7,z4,z5]),(1,[z6,z1,z2,z7,z4,z273])],[(0,[z6,z274,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z275,z4,z5]),(0,[z17,z6,z1,z2,z91,z7,z4]),(0,[z6,z1,z2,z7,z264,z104,z5]),(0,[z6,z276,z1,z2,z7,z4,z5]),(0,[z6,z1,z277,z2,z7,z4,z5]),(0,[z278,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z52,z2,z7,z4,z166])],[(0,[z6,z1,z2,z279,z7,z4,z5]),(0,[z6,z1,z280,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z281,z5]),(0,[z6,z1,z2,z7,z4,z5,z282]),(0,[z6,z1,z283,z2,z7,z4,z5]),(0,[z6,z284,z1,z2,z7,z4,z5])]],
   [[(0,[z6,z1,z285,z2,z7,z4,z5]),(0,[z199,z34,z6,z1,z2,z7,z4]),(0,[z286,z17,z6,z1,z2,z7,z4]),(0,[z34,z6,z1,z2,z7,z4,z183]),(0,[z6,z1,z2,z7,z264,z287,z5]),(0,[z6,z288,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z234,z5]),(0,[z6,z1,z2,z7,z4,z289,z5])],[(0,[z6,z1,z2,z290,z7,z4,z5]),(0,[z6,z1,z2,z7,z291,z4,z5])],[(0,[z6,z1,z292,z2,z7,z4,z5]),(0,[z6,z293,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z294,z5]),(0,[z17,z6,z288,z1,z2,z7,z4]),(1,[z6,z1,z2,z7,z4,z295]),(0,[z6,z1,z296,z2,z7,z4,z5]),(0,[z297,z6,z1,z2,z7,z4,z31]),(0,[z6,z1,z2,z7,z4,z5,z298]),(0,[z6,z1,z14,z2,z7,z4,z31]),(0,[z6,z1,z72,z7,z4,z64,z5]),(0,[z6,z1,z2,z7,z4,z299,z5])],[(1,[z6,z1,z2,z7,z300,z5]),(0,[z6,z1,z301,z2,z7,z4,z5]),(0,[z6,z1,z2,z302,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z303,z5]),(0,[z6,z1,z2,z91,z7,z36,z5])],[(0,[z17,z68,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z63,z3,z4,z5]),(1,[z199,z1,z2,z7,z81,z5]),(0,[z142,z34,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z304,z4,z5]),(0,[z6,z1,z2,z7,z182,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z305])],[(0,[z6,z1,z2,z306,z7,z4,z5]),(0,[z6,z1,z2,z7,z98,z36,z5]),(0,[z6,z55,z1,z185,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z307,z13]),(0,[z6,z1,z2,z7,z4,z36,z31]),(0,[z6,z1,z308,z2,z7,z4,z5])],[(1,[z6,z1,z2,z7,z4,z70]),(0,[z199,z1,z2,z7,z4,z81,z5]),(0,[z6,z1,z2,z7,z4,z309,z5]),(0,[z6,z1,z51,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z13,z85]),(0,[z6,z1,z2,z7,z4,z5,z310])],[(0,[z34,z6,z1,z2,z22,z7,z4]),(0,[z17,z6,z196,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z311,z4,z5])]],
   [[(0,[z6,z1,z2,z7,z4,z312,z5]),(0,[z86,z34,z6,z1,z2,z7,z4]),(1,[z6,z1,z2,z89,z4,z5]),(0,[z6,z39,z2,z63,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z313,z5]),(0,[z6,z1,z2,z314,z7,z4,z5]),(0,[z6,z1,z2,z7,z315,z4,z5]),(0,[z6,z1,z316,z2,z7,z4,z5])],[(1,[z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z317,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z318,z4,z5]),(0,[z6,z1,z319,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z59,z13]),(0,[z6,z1,z320,z2,z7,z4,z5]),(0,[z6,z1,z14,z2,z7,z4,z5])],[(0,[z6,z1,z321,z2,z7,z4,z5]),(0,[z17,z53,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z183,z13]),(0,[z19,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z322,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z323,z5])],[(0,[z109,z6,z1,z2,z7,z4,z5]),(0,[z110,z6,z1,z2,z7,z4,z5]),(0,[z297,z17,z6,z1,z2,z7,z4]),(0,[z324,z17,z6,z1,z2,z7,z4]),(0,[z17,z6,z90,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z64,z31]),(0,[z6,z1,z2,z325,z7,z4,z5])],[(0,[z68,z1,z2,z22,z7,z4,z5]),(0,[z68,z6,z1,z2,z7,z4,z31]),(0,[z326,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z327,z7,z4,z5]),(0,[z17,z6,z1,z2,z7,z4,z281]),(0,[z6,z1,z328,z2,z7,z4,z5]),(0,[z329,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z51,z2,z7,z4,z31]),(0,[z6,z1,z2,z7,z330,z4,z5]),(0,[z6,z1,z2,z7,z4,z36,z5])],[(0,[z6,z331,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z332,z5]),(1,[z6,z1,z333,z7,z4,z5]),(0,[z6,z1,z2,z91,z7,z92,z5])],[(0,[z106,z6,z1,z2,z7,z4,z13]),(0,[z334,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z181,z4,z5])],[(0,[z86,z6,z1,z83,z2,z4,z5]),(0,[z6,z39,z1,z2,z7,z151,z5]),(0,[z6,z1,z2,z335,z7,z4,z5])]],
   [[(0,[z75,z6,z1,z2,z7,z4,z13]),(0,[z6,z55,z1,z2,z7,z4,z295]),(0,[z6,z1,z2,z7,z4,z166,z85]),(1,[z6,z1,z101,z7,z4,z59])],[(0,[z23,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z185,z22,z7,z4,z5]),(0,[z6,z1,z336,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z337,z4,z5]),(0,[z6,z1,z2,z7,z338,z4,z5])],[(0,[z6,z1,z2,z7,z339,z4,z5]),(0,[z6,z1,z340,z2,z4,z81,z5]),(0,[z53,z1,z2,z7,z98,z4,z5]),(0,[z6,z1,z2,z7,z287,z98,z5]),(0,[z6,z1,z2,z38,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z64,z5]),(0,[z6,z1,z341,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z4,z342,z5]),(0,[z343,z6,z1,z2,z7,z4,z5]),(0,[z6,z90,z2,z7,z84,z4,z5]),(1,[z6,z1,z2,z7,z4,z234]),(0,[z6,z1,z2,z7,z4,z5,z344]),(0,[z6,z1,z345,z2,z7,z4,z5]),(0,[z6,z1,z14,z2,z7,z4,z166]),(0,[z6,z1,z2,z7,z4,z5,z346]),(0,[z347,z6,z1,z2,z7,z4,z5])],[(0,[z106,z6,z1,z2,z7,z4,z31]),(0,[z6,z1,z2,z348,z7,z4,z5]),(0,[z6,z56,z2,z7,z287,z4,z5]),(0,[z349,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z350,z5])],[(0,[z6,z1,z2,z7,z84,z4,z5]),(0,[z6,z56,z1,z2,z7,z4,z5]),(0,[z351,z6,z1,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z352,z4,z5]),(0,[z6,z1,z2,z7,z117,z4,z31]),(1,[z34,z6,z1,z2,z7,z4]),(0,[z6,z39,z1,z2,z7,z181,z5]),(0,[z6,z1,z2,z353,z7,z4,z5]),(0,[z6,z1,z354,z2,z7,z264,z5]),(0,[z355,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z91,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z92,z5])],[(0,[z17,z6,z1,z2,z7,z4,z92]),(0,[z19,z34,z6,z1,z2,z7,z4]),(0,[z6,z55,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z120,z5]),(0,[z6,z196,z1,z2,z7,z4,z356]),(0,[z6,z1,z357,z2,z7,z4,z31]),(0,[z6,z1,z358,z2,z7,z4,z5]),(0,[z6,z1,z359,z2,z7,z4,z5]),(1,[z6,z1,z2,z7,z4,z235])]],
   [[(0,[z17,z6,z1,z2,z145,z7,z4]),(0,[z6,z1,z2,z7,z100,z4,z5]),(0,[z6,z1,z2,z38,z7,z4,z31])],[(0,[z6,z1,z2,z7,z4,z300,z5]),(0,[z6,z1,z360,z2,z7,z4,z5]),(0,[z361,z6,z1,z2,z7,z4,z5]),(0,[z6,z362,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z363,z5])],[(0,[z34,z6,z1,z364,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z365,z5]),(0,[z6,z366,z1,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z98,z4,z332]),(0,[z6,z1,z2,z7,z367,z4,z5]),(0,[z6,z1,z368,z2,z7,z4,z5]),(0,[z6,z369,z1,z2,z7,z4,z5])],[(0,[z199,z6,z1,z2,z91,z7,z5]),(0,[z6,z1,z370,z2,z7,z4,z5]),(0,[z17,z6,z1,z2,z7,z371,z4]),(0,[z6,z1,z2,z7,z146,z4,z13]),(0,[z6,z1,z2,z7,z97,z4,z13]),(0,[z6,z1,z372,z2,z7,z4,z5])],[(0,[z106,z17,z6,z1,z2,z7,z4]),(0,[z6,z1,z373,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z117,z4,z5]),(0,[z53,z6,z1,z2,z7,z98,z5]),(0,[z6,z1,z374,z2,z7,z4,z5]),(0,[z6,z1,z375,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z376]),(0,[z6,z1,z52,z2,z91,z7,z5]),(0,[z6,z1,z2,z4,z58,z5,z85]),(0,[z6,z1,z2,z7,z377,z4,z5])],[(0,[z23,z34,z6,z1,z2,z7,z4]),(0,[z6,z1,z357,z2,z7,z4,z5]),(0,[z6,z378,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z379]),(0,[z6,z1,z2,z7,z4,z13,z380]),(0,[z6,z1,z2,z7,z4,z31,z140]),(0,[z381,z6,z1,z2,z7,z4,z31])],[(0,[z6,z1,z2,z7,z4,z4,z5])]],
   [[(0,[z34,z6,z1,z18,z2,z7,z4]),(0,[z17,z6,z1,z2,z7,z4,z31]),(0,[z6,z1,z132,z2,z7,z4,z5]),(0,[z6,z382,z1,z2,z7,z4,z5])],[(0,[z34,z6,z1,z2,z91,z7,z4]),(0,[z6,z1,z2,z7,z383,z4,z5]),(0,[z6,z1,z2,z7,z4,z384,z5])],[(0,[z6,z1,z18,z20,z7,z4,z5]),(0,[z6,z90,z1,z2,z7,z4,z13]),(0,[z6,z1,z105,z145,z7,z4,z5])],[(0,[z6,z1,z2,z117,z84,z4,z5]),(1,[z6,z1,z2,z385,z7,z4]),(0,[z6,z1,z2,z386,z7,z4,z5]),(0,[z6,z252,z1,z2,z7,z4,z5]),(1,[z34,z1,z2,z7,z4,z183]),(0,[z6,z387,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z287,z4,z13]),(0,[z6,z1,z2,z7,z170,z4,z13]),(0,[z6,z1,z2,z7,z4,z5,z267])],[(0,[z6,z1,z2,z76,z7,z117,z5]),(0,[z6,z1,z2,z7,z4,z388,z5]),(0,[z6,z1,z1,z2,z7,z4,z13]),(0,[z6,z1,z389,z2,z7,z4,z5]),(0,[z6,z1,z390,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z391])],[(1,[z6,z1,z2,z7,z392,z5]),(0,[z106,z1,z48,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z393,z5]),(0,[z394,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z63,z117,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z395]),(0,[z6,z1,z364,z2,z7,z4,z5]),(0,[z34,z6,z1,z2,z7,z396,z5]),(0,[z34,z6,z288,z1,z2,z7,z4]),(1,[z6,z39,z2,z63,z4,z5]),(0,[z6,z1,z2,z7,z397,z4,z5]),(0,[z6,z1,z14,z2,z7,z4,z59])],[(0,[z6,z1,z398,z2,z7,z4,z5]),(0,[z6,z1,z2,z76,z7,z4,z5]),(0,[z6,z55,z1,z145,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z399,z5]),(0,[z6,z1,z52,z2,z7,z4,z138]),(0,[z6,z1,z2,z400,z7,z4,z5])],[(0,[z34,z68,z6,z1,z2,z7,z4]),(0,[z17,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z401,z5]),(0,[z6,z1,z402,z2,z7,z4,z5]),(0,[z6,z39,z1,z2,z84,z4,z5]),(0,[z6,z1,z2,z403,z7,z4,z5]),(0,[z6,z1,z2,z404,z7,z4,z5])]],
   [[(1,[z6,z1,z21,z2,z7,z4]),(0,[z34,z6,z1,z2,z63,z7,z4]),(0,[z6,z1,z2,z7,z4,z405,z31])],[(0,[z297,z68,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z235,z36])],[(0,[z0,z6,z1,z62,z7,z4,z5]),(0,[z6,z288,z2,z7,z4,z5,z13]),(0,[z41,z6,z1,z2,z7,z4,z13])],[(0,[z6,z1,z2,z406,z7,z4,z5]),(0,[z34,z6,z1,z83,z2,z7,z4]),(0,[z6,z1,z2,z407,z7,z4,z5])],[(0,[z6,z1,z2,z7,z4,z5,z408])],[(0,[z68,z6,z48,z2,z7,z4,z5])],[(0,[z6,z409,z1,z2,z7,z4,z5]),(0,[z6,z1,z18,z2,z7,z4,z31]),(0,[z6,z1,z2,z385,z7,z117,z4]),(0,[z6,z1,z2,z7,z4,z5,z70]),(0,[z6,z1,z2,z7,z287,z81,z5]),(1,[z6,z1,z340,z2,z4,z5]),(0,[z53,z6,z1,z2,z7,z4,z13]),(0,[z34,z6,z90,z1,z2,z7,z4]),(0,[z6,z410,z1,z2,z7,z4,z5]),(0,[z6,z1,z411,z2,z7,z4,z5]),(0,[z6,z1,z412,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z413,z4,z5]),(0,[z6,z1,z205,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z405,z5]),(0,[z6,z1,z206,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z414,z5]),(0,[z6,z1,z2,z7,z4,z415,z5])]],
   [[(0,[z6,z416,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z273,z5]),(0,[z417,z6,z1,z2,z7,z4,z5])],[(1,[z6,z1,z2,z7,z4,z130]),(0,[z6,z1,z2,z7,z7,z4,z5]),(0,[z17,z6,z1,z2,z7,z98,z4]),(0,[z17,z6,z39,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z5,z5]),(0,[z17,z6,z1,z2,z7,z4,z166]),(0,[z6,z1,z2,z89,z7,z4,z5]),(0,[z6,z1,z2,z418,z7,z4,z5]),(0,[z419,z6,z1,z2,z7,z4,z5])],[(0,[z420,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z255,z2,z7,z117,z5]),(0,[z6,z1,z2,z421,z7,z4,z5]),(0,[z422,z6,z1,z2,z7,z4,z5])],[(0,[z6,z1,z2,z22,z7,z4,z31]),(1,[z6,z1,z370,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z423,z5]),(0,[z6,z1,z2,z7,z424,z4,z5]),(0,[z6,z1,z2,z7,z425,z4,z5])],[(0,[z6,z1,z255,z2,z7,z4,z5]),(1,[z6,z1,z2,z7,z426,z4]),(0,[z17,z34,z6,z1,z2,z7,z4]),(1,[z17,z6,z1,z427,z7,z4]),(0,[z17,z6,z1,z2,z7,z264,z4]),(0,[z6,z90,z1,z2,z7,z4,z112]),(0,[z6,z1,z72,z2,z7,z64,z5]),(0,[z6,z1,z2,z7,z4,z5,z428]),(0,[z6,z1,z83,z2,z7,z97,z5])],[(0,[z106,z6,z48,z2,z7,z4,z5]),(0,[z6,z1,z18,z2,z7,z4,z5]),(0,[z17,z6,z1,z160,z2,z7,z4]),(0,[z17,z6,z1,z101,z2,z7,z4]),(0,[z6,z1,z429,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z430,z5])],[(1,[z6,z1,z128,z2,z7,z4]),(0,[z86,z6,z1,z2,z97,z4,z5]),(0,[z6,z1,z2,z7,z4,z431,z5])],[(0,[z6,z1,z18,z2,z7,z4,z12]),(0,[z6,z1,z2,z7,z4,z432,z5]),(0,[z6,z1,z2,z7,z433,z4,z5]),(0,[z6,z1,z14,z101,z7,z4,z5])]],
   [[(0,[z6,z434,z1,z2,z7,z4,z5]),(0,[z17,z6,z1,z185,z2,z7,z4]),(0,[z6,z1,z2,z7,z193,z4,z5]),(0,[z19,z6,z1,z160,z7,z4,z5]),(0,[z6,z1,z2,z435,z7,z4,z5]),(0,[z6,z1,z52,z2,z7,z5,z138])],[(0,[z34,z6,z1,z2,z7,z117,z4]),(0,[z53,z6,z1,z2,z7,z81,z5]),(1,[z17,z1,z2,z7,z4,z32]),(0,[z6,z1,z2,z436,z7,z4,z5]),(0,[z6,z1,z2,z63,z7,z4,z5]),(0,[z6,z1,z2,z437,z7,z4,z5]),(0,[z6,z56,z196,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z104,z64,z5]),(0,[z438,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z439,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z440,z4,z5]),(0,[z6,z1,z2,z7,z4,z441,z5]),(0,[z6,z1,z2,z7,z4,z442,z5]),(0,[z6,z1,z2,z275,z4,z81,z5]),(0,[z6,z2,z7,z287,z4,z104,z5]),(0,[z6,z1,z443,z2,z7,z4,z5]),(0,[z6,z1,z444,z2,z7,z4,z5])],[(1,[z6,z1,z2,z7,z4,z401]),(0,[z19,z6,z1,z185,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z166])],[(0,[z34,z6,z1,z2,z445,z7,z4]),(0,[z6,z446,z1,z2,z7,z4,z5]),(0,[z19,z6,z1,z2,z7,z4,z401]),(0,[z6,z1,z447,z2,z7,z4,z5]),(0,[z6,z39,z1,z2,z7,z4,z31])],[(0,[z214,z34,z6,z1,z2,z7,z4]),(1,[z6,z1,z2,z7,z4,z356]),(0,[z6,z1,z448,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z13,z125]),(0,[z6,z1,z449,z2,z7,z4,z5]),(0,[z6,z450,z1,z2,z7,z4,z5])],[(0,[z6,z1,z2,z451,z7,z4,z5])],[(0,[z452,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z453,z4,z5]),(0,[z6,z1,z454,z2,z7,z4,z5]),(1,[z6,z1,z2,z7,z4,z224]),(0,[z6,z1,z2,z7,z455,z4,z5]),(0,[z6,z1,z456,z2,z7,z4,z5]),(0,[z6,z1,z457,z2,z7,z4,z5])]],
   [[(1,[z6,z1,z2,z7,z4,z40])],[(0,[z6,z458,z1,z2,z7,z4,z5]),(0,[z6,z1,z22,z145,z7,z4,z5]),(0,[z6,z1,z21,z2,z7,z4,z5]),(0,[z286,z6,z1,z2,z7,z4,z5]),(0,[z17,z6,z1,z2,z7,z4,z32]),(0,[z6,z1,z459,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z460,z5]),(0,[z6,z1,z72,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z461,z5])],[(0,[z6,z1,z462,z2,z7,z4,z5]),(0,[z17,z6,z1,z137,z7,z4,z5]),(0,[z6,z1,z2,z7,z463,z4,z5]),(0,[z6,z196,z2,z7,z4,z104,z5]),(0,[z6,z1,z2,z7,z464,z4,z5])],[(0,[z6,z1,z2,z465,z7,z4,z5]),(0,[z17,z6,z129,z1,z2,z7,z4]),(0,[z17,z6,z1,z2,z7,z4,z59]),(0,[z34,z6,z1,z2,z7,z4,z31]),(1,[z41,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z264,z4,z31]),(0,[z6,z1,z185,z7,z146,z4,z5])],[(0,[z6,z1,z48,z2,z7,z4,z31]),(0,[z53,z199,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z466,z5]),(0,[z6,z1,z2,z7,z467,z4,z5])],[(0,[z23,z68,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z468,z5]),(0,[z6,z55,z1,z160,z7,z4,z5]),(1,[z6,z1,z14,z7,z4,z166]),(0,[z6,z1,z469,z2,z7,z4,z5])],[(0,[z10,z6,z1,z48,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z470,z5]),(1,[z6,z1,z2,z7,z471,z5]),(0,[z6,z1,z83,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z472,z5])],[(0,[z473,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z81,z13]),(0,[z34,z6,z1,z2,z7,z4,z64]),(0,[z19,z6,z1,z2,z7,z471,z5]),(0,[z6,z1,z474,z2,z7,z4,z5]),(0,[z6,z196,z1,z2,z7,z4,z475]),(0,[z6,z1,z52,z2,z38,z7,z4]),(0,[z6,z1,z476,z2,z7,z4,z5])]],
   [[(1,[z6,z1,z477,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z478]),(0,[z17,z6,z1,z2,z7,z287,z4]),(0,[z6,z1,z2,z7,z479,z4,z5]),(0,[z6,z480,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z481,z5])],[(1,[z6,z1,z168,z2,z7,z4]),(0,[z6,z1,z2,z482,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z483])],[(0,[z17,z6,z1,z2,z7,z4,z85]),(0,[z6,z1,z2,z7,z4,z484,z5]),(0,[z485,z6,z1,z2,z7,z4,z5]),(1,[z6,z1,z2,z7,z4,z486]),(0,[z6,z1,z2,z7,z264,z4,z5]),(0,[z6,z1,z2,z487,z7,z4,z5])],[(0,[z6,z1,z48,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z488,z5]),(0,[z17,z6,z1,z2,z20,z7,z4]),(0,[z6,z1,z2,z7,z4,z5,z32]),(0,[z34,z6,z1,z2,z7,z193,z4]),(0,[z6,z1,z2,z7,z489,z4,z5]),(0,[z6,z1,z72,z354,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z490]),(0,[z6,z1,z2,z7,z4,z491,z5]),(0,[z6,z1,z492,z2,z7,z4,z5])],[(0,[z297,z6,z1,z2,z7,z4,z5]),(0,[z324,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z83,z2,z7,z287,z5]),(0,[z493,z6,z1,z2,z7,z4,z5])],[(0,[z6,z129,z1,z2,z7,z4,z488]),(0,[z6,z1,z2,z7,z4,z494,z13]),(0,[z495,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z496,z5]),(1,[z6,z1,z83,z2,z36,z5])],[(0,[z6,z1,z2,z7,z426,z4,z5]),(0,[z6,z1,z497,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z498,z4,z5]),(0,[z6,z1,z105,z2,z146,z4,z5])],[(0,[z199,z6,z1,z2,z7,z98,z5]),(1,[z6,z1,z2,z7,z4,z332]),(0,[z6,z55,z160,z2,z7,z4,z5]),(1,[z6,z1,z2,z38,z4,z58])]],
   [[(0,[z6,z1,z52,z2,z7,z98,z5]),(0,[z6,z196,z1,z2,z7,z4,z13]),(0,[z6,z1,z164,z2,z7,z5,z85])],[(0,[z6,z1,z2,z7,z4,z499,z5]),(0,[z6,z1,z2,z2,z7,z4,z5]),(0,[z500,z6,z1,z2,z7,z4,z5]),(0,[z6,z501,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z91,z97,z4,z5])],[(1,[z10,z6,z1,z2,z7,z4]),(1,[z6,z288,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z31,z13]),(0,[z6,z1,z2,z7,z4,z59,z31]),(1,[z6,z1,z72,z7,z64,z5]),(0,[z6,z1,z502,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z503,z5])],[(0,[z1,z48,z2,z22,z7,z4,z5]),(0,[z6,z1,z504,z2,z7,z4,z5]),(0,[z17,z199,z6,z1,z2,z7,z4]),(0,[z34,z6,z446,z1,z2,z7,z4]),(0,[z6,z1,z2,z145,z7,z4,z13])],[(0,[z6,z1,z370,z2,z7,z4,z81]),(0,[z34,z6,z1,z2,z7,z98,z4]),(0,[z17,z6,z1,z354,z2,z7,z4]),(1,[z6,z1,z427,z7,z4,z5]),(0,[z34,z6,z39,z1,z2,z7,z4]),(1,[z6,z1,z2,z505,z4,z5]),(0,[z506,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z507,z7,z4,z5]),(0,[z6,z1,z2,z57,z7,z4,z5]),(0,[z6,z1,z508,z2,z7,z4,z5]),(0,[z6,z509,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z85])],[(0,[z6,z1,z128,z2,z7,z4,z5]),(0,[z19,z6,z1,z2,z505,z4,z5]),(0,[z6,z1,z2,z333,z7,z4,z5]),(1,[z6,z1,z2,z7,z4,z510]),(0,[z6,z1,z2,z7,z4,z58,z13]),(0,[z6,z1,z2,z7,z4,z5,z511])],[(0,[z68,z6,z1,z2,z7,z4,z5]),(0,[z75,z6,z1,z18,z7,z4,z5]),(0,[z6,z1,z2,z7,z512,z4,z5]),(0,[z6,z513,z1,z2,z7,z4,z5]),(0,[z6,z90,z1,z2,z84,z4,z5]),(0,[z6,z196,z1,z2,z7,z287,z5]),(0,[z6,z1,z2,z7,z4,z31,z207]),(0,[z6,z1,z51,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z514,z5])],[(0,[z6,z1,z2,z7,z4,z5,z515]),(0,[z6,z1,z2,z516,z7,z4,z5]),(0,[z6,z1,z2,z517,z7,z4,z5]),(0,[z6,z1,z518,z2,z7,z4,z5]),(0,[z6,z1,z185,z105,z7,z4,z5])]],
   [[(0,[z106,z6,z1,z2,z7,z300,z5]),(0,[z6,z129,z1,z2,z7,z4,z13]),(0,[z6,z1,z519,z2,z7,z4,z5]),(0,[z34,z6,z56,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z31,z183]),(0,[z520,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z521,z5]),(0,[z6,z522,z1,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z523,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z130]),(0,[z75,z1,z2,z22,z7,z4,z5]),(0,[z75,z6,z1,z2,z7,z4,z31]),(0,[z17,z6,z1,z2,z7,z4,z138]),(0,[z524,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z525,z2,z7,z4,z5]),(0,[z6,z1,z526,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z59,z5])],[(1,[z68,z129,z2,z7,z4,z5]),(0,[z6,z1,z2,z527,z7,z4,z5]),(0,[z6,z1,z354,z2,z7,z4,z528])],[(0,[z86,z6,z1,z2,z7,z529,z5]),(0,[z34,z6,z1,z185,z2,z7,z4]),(0,[z6,z1,z2,z7,z530,z4,z5]),(0,[z6,z1,z2,z531,z7,z4,z13]),(0,[z6,z532,z1,z2,z7,z4,z5])],[(0,[z533,z6,z1,z2,z7,z4,z5]),(0,[z534,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z535,z4,z5]),(0,[z17,z6,z1,z2,z7,z4,z104]),(1,[z6,z1,z2,z7,z193,z5]),(0,[z6,z1,z2,z7,z4,z471,z5]),(0,[z19,z6,z1,z145,z7,z4,z5]),(0,[z6,z1,z160,z2,z7,z4,z13]),(0,[z536,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z101,z2,z7,z4,z13]),(0,[z6,z1,z2,z537,z7,z4,z5])],[(1,[z6,z1,z46,z7,z4,z5]),(1,[z6,z1,z2,z7,z4,z538]),(0,[z6,z1,z539,z2,z7,z4,z5]),(0,[z6,z540,z1,z2,z7,z4,z5]),(0,[z17,z6,z1,z72,z2,z7,z4]),(0,[z6,z1,z2,z541,z7,z4,z5])],[(0,[z106,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z542,z2,z7,z4,z5]),(0,[z6,z1,z543,z2,z7,z4,z5])],[(0,[z6,z1,z101,z18,z7,z4,z5]),(0,[z0,z6,z1,z504,z7,z4,z5]),(0,[z17,z6,z1,z2,z7,z4,z81]),(0,[z33,z6,z1,z2,z7,z4,z13]),(0,[z6,z1,z544,z2,z7,z4,z5]),(1,[z6,z1,z164,z2,z7,z5])]],
   [[(0,[z6,z1,z2,z7,z545,z4,z5]),(0,[z546,z17,z6,z1,z2,z7,z4]),(0,[z6,z1,z547,z2,z7,z4,z5])],[(0,[z86,z6,z1,z2,z7,z548,z5]),(0,[z17,z6,z1,z2,z7,z4,z36]),(0,[z17,z6,z1,z2,z7,z4,z58]),(0,[z6,z56,z1,z2,z7,z4,z510]),(0,[z6,z1,z2,z549,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z550,z5])],[(0,[z6,z1,z18,z7,z4,z5,z166]),(0,[z6,z1,z2,z7,z4,z551,z5]),(0,[z6,z1,z2,z445,z7,z4,z5]),(0,[z6,z1,z51,z2,z38,z4,z5]),(0,[z6,z1,z2,z38,z7,z4,z5])],[(0,[z552,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z553,z7,z4,z5]),(0,[z34,z1,z2,z7,z4,z183,z5]),(0,[z554,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z185,z2,z146,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z138])],[(0,[z6,z1,z555,z2,z7,z4,z5]),(0,[z6,z556,z1,z2,z7,z4,z5]),(0,[z34,z6,z1,z2,z7,z4,z32]),(0,[z6,z1,z2,z7,z557,z4,z5]),(0,[z6,z1,z558,z2,z7,z4,z5])],[(0,[z6,z1,z2,z169,z7,z4,z5]),(0,[z19,z6,z55,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z146,z4,z31]),(0,[z6,z1,z2,z7,z97,z4,z31]),(0,[z6,z1,z2,z7,z4,z559,z5])],[(0,[z34,z6,z129,z1,z2,z7,z4]),(0,[z1,z2,z7,z98,z4,z81,z5]),(0,[z34,z6,z1,z2,z7,z4,z59]),(0,[z6,z1,z560,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z561,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z562])],[(0,[z563,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z564,z5]),(0,[z6,z1,z354,z2,z7,z4,z13]),(1,[z381,z6,z1,z2,z7,z4])]],
   [[(0,[z6,z1,z2,z7,z4,z5,z40]),(0,[z381,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z565]),(0,[z566,z6,z1,z2,z7,z4,z5])],[(1,[z106,z48,z2,z7,z4,z5]),(1,[z6,z1,z2,z7,z529,z5]),(0,[z0,z6,z1,z2,z7,z4,z13]),(0,[z6,z1,z185,z2,z7,z4,z486])],[(0,[z6,z1,z2,z7,z170,z92,z5])],[(0,[z106,z34,z6,z1,z2,z7,z4]),(0,[z199,z6,z1,z2,z7,z81,z5]),(0,[z6,z90,z1,z2,z7,z4,z31]),(0,[z6,z567,z1,z2,z7,z4,z5])],[(0,[z6,z1,z2,z568,z7,z4,z5]),(0,[z6,z1,z52,z2,z7,z81,z5]),(0,[z6,z1,z2,z137,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z380]),(0,[z6,z1,z2,z7,z287,z4,z31]),(0,[z6,z1,z2,z7,z170,z4,z31]),(0,[z6,z1,z2,z7,z97,z4,z5])],[(0,[z34,z6,z196,z1,z2,z7,z4]),(0,[z569,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z295]),(0,[z6,z1,z103,z7,z84,z4,z5]),(1,[z6,z1,z2,z7,z4,z475]),(0,[z6,z1,z2,z7,z4,z570,z31]),(0,[z6,z1,z1,z2,z7,z4,z31]),(0,[z6,z1,z354,z2,z7,z4,z31]),(0,[z6,z1,z2,z571,z7,z4,z5])],[(0,[z34,z6,z1,z2,z20,z7,z4]),(0,[z6,z1,z572,z2,z7,z4,z5])],[(0,[z0,z6,z1,z2,z7,z4,z31]),(0,[z6,z1,z573,z2,z7,z4,z5])]],
   [[(1,[z410,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z574,z5])],[(0,[z17,z0,z6,z1,z2,z7,z4]),(0,[z6,z1,z575,z2,z7,z4,z5]),(0,[z19,z410,z1,z2,z7,z4,z5]),(0,[z6,z576,z1,z2,z7,z4,z5]),(0,[z6,z577,z1,z2,z7,z4,z5]),(0,[z6,z1,z83,z2,z4,z36,z5])],[(0,[z6,z1,z2,z7,z548,z4,z5]),(0,[z6,z90,z1,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z4,z5,z198]),(0,[z68,z6,z129,z2,z7,z4,z5]),(0,[z17,z6,z1,z2,z7,z97,z4]),(0,[z6,z1,z73,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z31,z298]),(0,[z6,z1,z2,z7,z170,z4,z5])],[(0,[z6,z1,z1,z2,z7,z4,z5]),(0,[z6,z1,z578,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z579,z4,z5]),(0,[z6,z1,z2,z63,z146,z4,z5]),(0,[z6,z1,z2,z63,z97,z4,z5]),(0,[z6,z580,z1,z2,z7,z4,z5])],[(1,[z6,z1,z2,z107,z4,z5]),(0,[z581,z6,z1,z2,z7,z4,z5]),(0,[z582,z17,z6,z1,z2,z7,z4]),(0,[z583,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z584,z2,z7,z4,z5]),(1,[z6,z1,z185,z146,z4,z5]),(0,[z6,z1,z2,z7,z585,z4,z5]),(0,[z6,z1,z2,z586,z7,z4,z5])],[(0,[z6,z1,z47,z2,z7,z4,z5]),(0,[z6,z1,z587,z2,z7,z4,z5]),(0,[z6,z1,z2,z3,z7,z4,z13])],[(1,[z297,z6,z1,z2,z7,z4]),(0,[z53,z6,z1,z2,z7,z4,z31]),(0,[z17,z6,z1,z2,z588,z7,z4]),(0,[z17,z6,z1,z2,z7,z170,z4]),(0,[z34,z6,z1,z354,z2,z7,z4]),(0,[z19,z6,z1,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z5,z213]),(0,[z589,z6,z1,z2,z7,z4,z5])]],
   [[(0,[z6,z590,z1,z2,z7,z4,z5])],[(0,[z6,z1,z591,z2,z7,z4,z5]),(0,[z6,z1,z592,z2,z7,z4,z5]),(0,[z17,z6,z1,z105,z2,z7,z4]),(0,[z17,z6,z1,z51,z2,z7,z4]),(0,[z6,z1,z51,z2,z7,z4,z85]),(0,[z6,z1,z51,z2,z4,z5,z85])],[(0,[z106,z6,z1,z2,z7,z392,z5]),(0,[z68,z129,z1,z2,z7,z4,z5]),(1,[z6,z1,z62,z7,z4,z5]),(0,[z6,z1,z593,z2,z7,z4,z5]),(0,[z6,z1,z83,z2,z84,z4,z5]),(0,[z6,z39,z1,z2,z7,z4,z273]),(0,[z6,z1,z2,z7,z78,z4,z31]),(0,[z6,z1,z105,z2,z145,z4,z5])],[(0,[z106,z6,z129,z2,z7,z4,z5]),(0,[z594,z6,z1,z2,z7,z4,z5]),(0,[z6,z595,z1,z2,z7,z4,z5]),(0,[z6,z596,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z597,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z598,z5])],[(0,[z129,z1,z48,z2,z7,z4,z5]),(0,[z17,z6,z1,z2,z3,z7,z4]),(0,[z17,z6,z1,z14,z2,z7,z4]),(0,[z34,z6,z1,z2,z7,z4,z138]),(0,[z6,z1,z2,z7,z505,z4,z5]),(0,[z6,z1,z2,z7,z4,z59,z85])],[(0,[z6,z1,z2,z22,z7,z4,z5]),(0,[z34,z6,z1,z2,z7,z4,z92]),(1,[z6,z1,z2,z7,z4,z218]),(0,[z6,z90,z39,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z510]),(0,[z6,z599,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z600]),(0,[z6,z1,z2,z7,z170,z4,z166])],[(0,[z6,z1,z2,z601,z7,z4,z5]),(0,[z6,z602,z1,z2,z7,z4,z5]),(0,[z34,z6,z1,z2,z145,z7,z4]),(0,[z19,z6,z1,z2,z7,z4,z218]),(0,[z6,z1,z2,z603,z7,z4,z5])],[(0,[z6,z1,z604,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z529,z5]),(0,[z34,z6,z1,z2,z7,z4,z104])]],
   [[(0,[z6,z1,z605,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z606,z5]),(0,[z6,z1,z105,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z528,z5]),(0,[z6,z1,z607,z2,z7,z4,z5])],[(0,[z6,z1,z2,z608,z7,z4,z5]),(0,[z17,z6,z55,z1,z2,z7,z4])],[(0,[z6,z1,z2,z385,z7,z4,z5]),(0,[z609,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z7,z4,z59,z5,z166])],[(0,[z610,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z98,z4,z187]),(0,[z611,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z104,z13]),(0,[z6,z1,z2,z7,z92,z5,z138])],[(0,[z6,z6,z1,z2,z7,z4,z5]),(0,[z0,z6,z1,z2,z3,z4,z5]),(0,[z34,z6,z1,z2,z7,z4,z58]),(0,[z6,z55,z1,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z612,z4,z5]),(0,[z6,z613,z1,z2,z7,z4,z5])],[(0,[z6,z1,z614,z2,z7,z4,z5]),(0,[z6,z1,z168,z2,z7,z117,z4]),(0,[z6,z1,z2,z7,z98,z4,z13]),(0,[z6,z1,z2,z38,z7,z4,z85])],[(0,[z6,z1,z2,z7,z426,z4,z81]),(1,[z6,z1,z2,z7,z498,z5]),(0,[z6,z39,z1,z2,z7,z4,z5]),(0,[z615,z6,z1,z2,z7,z4,z5])],[(0,[z6,z1,z18,z145,z7,z4,z5]),(0,[z6,z616,z1,z2,z7,z4,z5]),(0,[z19,z6,z1,z2,z7,z498,z5]),(0,[z6,z1,z2,z7,z617,z4,z5]),(0,[z6,z1,z2,z145,z84,z4,z5]),(0,[z6,z1,z2,z7,z4,z365,z13])]],
   [[(0,[z6,z1,z2,z7,z4,z538,z5]),(0,[z6,z56,z1,z2,z7,z287,z5])],[(0,[z6,z1,z2,z7,z4,z618,z5]),(0,[z6,z1,z2,z7,z4,z356,z5]),(0,[z6,z1,z2,z91,z7,z287,z5])],[(1,[z6,z1,z2,z7,z4,z248]),(0,[z6,z1,z427,z2,z7,z4,z5])],[(0,[z17,z6,z1,z2,z7,z146,z4]),(0,[z34,z6,z1,z2,z7,z257,z4]),(1,[z6,z1,z2,z7,z4,z619]),(1,[z6,z56,z2,z7,z287,z5]),(0,[z33,z6,z288,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z268]),(0,[z6,z1,z2,z7,z4,z620,z5])],[(0,[z75,z6,z1,z22,z7,z4,z5]),(0,[z6,z1,z2,z7,z621,z4,z5]),(0,[z6,z160,z2,z20,z7,z4,z5]),(0,[z6,z1,z622,z2,z7,z4,z5]),(0,[z6,z623,z1,z2,z7,z4,z5])],[(0,[z34,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z624,z2,z7,z4,z5]),(0,[z6,z1,z83,z2,z7,z104,z5]),(0,[z6,z1,z2,z7,z4,z619,z5]),(0,[z6,z1,z83,z2,z7,z92,z5]),(0,[z6,z625,z1,z2,z7,z4,z5])],[(0,[z75,z23,z1,z2,z7,z4,z5]),(0,[z34,z6,z1,z2,z7,z4,z396])],[(0,[z6,z1,z83,z2,z7,z4,z31]),(0,[z6,z1,z185,z2,z145,z4,z5]),(0,[z6,z1,z2,z7,z170,z4,z59])]],
   [[(0,[z6,z1,z2,z477,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z81,z31]),(0,[z610,z34,z6,z1,z2,z7,z4]),(0,[z6,z1,z626,z2,z7,z4,z31]),(0,[z6,z1,z627,z2,z7,z4,z5]),(0,[z6,z1,z51,z2,z7,z4,z58])],[(1,[z6,z1,z2,z7,z4,z9]),(0,[z19,z6,z2,z20,z7,z4,z5]),(0,[z6,z1,z333,z7,z84,z4,z5]),(0,[z6,z1,z389,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z628,z4,z5])],[(0,[z106,z68,z1,z2,z7,z4,z5]),(0,[z0,z86,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z588,z7,z4,z5]),(0,[z34,z6,z1,z454,z2,z7,z4]),(1,[z34,z6,z1,z2,z7,z193]),(1,[z6,z55,z160,z7,z4,z5])],[(1,[z6,z1,z2,z28,z4,z5]),(1,[z6,z1,z2,z275,z4,z5]),(1,[z17,z6,z1,z137,z7,z4]),(0,[z6,z1,z2,z7,z4,z13,z13]),(0,[z6,z1,z2,z7,z4,z399,z13])],[(0,[z86,z1,z2,z7,z117,z4,z5]),(0,[z6,z1,z2,z7,z4,z629,z5])],[(0,[z6,z1,z2,z7,z630,z4,z5]),(0,[z17,z6,z1,z427,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z5,z475]),(0,[z631,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z185,z2,z7,z4,z13]),(0,[z6,z1,z83,z52,z2,z7,z5]),(0,[z6,z1,z2,z7,z4,z5,z632])],[(0,[z6,z1,z2,z633,z7,z4,z5]),(0,[z6,z1,z2,z634,z7,z4,z5]),(1,[z6,z1,z364,z2,z7,z4]),(0,[z34,z6,z1,z2,z7,z97,z4]),(0,[z6,z1,z2,z7,z4,z635,z5]),(0,[z6,z1,z83,z2,z7,z4,z5])],[(0,[z636,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z81,z5]),(0,[z34,z6,z1,z2,z7,z4,z166]),(0,[z6,z39,z1,z2,z63,z4,z5]),(0,[z6,z196,z1,z2,z7,z104,z5]),(0,[z6,z56,z1,z2,z7,z4,z619]),(0,[z6,z1,z626,z2,z7,z4,z5]),(0,[z637,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z638,z5])]],
   [[(1,[z6,z1,z47,z2,z7,z4]),(0,[z6,z1,z185,z18,z7,z4,z5]),(0,[z6,z1,z639,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z307,z5]),(0,[z6,z1,z60,z2,z7,z4,z5]),(0,[z6,z1,z640,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z371,z4,z5]),(0,[z6,z196,z1,z2,z7,z4,z31]),(0,[z6,z1,z641,z2,z7,z4,z5])],[(0,[z6,z1,z642,z2,z7,z4,z5]),(0,[z6,z1,z82,z2,z7,z4,z5]),(0,[z34,z34,z6,z1,z2,z7,z4]),(0,[z34,z6,z1,z2,z7,z264,z4])],[(0,[z643,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z392,z4,z5]),(1,[z142,z6,z1,z2,z7,z4]),(0,[z644,z6,z1,z2,z7,z4,z5]),(0,[z34,z6,z1,z160,z2,z7,z4]),(0,[z34,z6,z1,z101,z2,z7,z4]),(0,[z6,z55,z1,z2,z7,z4,z131]),(0,[z6,z1,z2,z7,z4,z31,z31])],[(0,[z1,z2,z7,z4,z183,z5,z32]),(0,[z34,z6,z1,z105,z2,z7,z4]),(0,[z34,z6,z1,z51,z2,z7,z4]),(0,[z6,z1,z2,z145,z7,z4,z31]),(0,[z6,z1,z2,z215,z7,z4,z31]),(0,[z6,z1,z2,z7,z645,z4,z5]),(0,[z6,z1,z2,z7,z646,z4,z5]),(0,[z6,z1,z2,z38,z7,z4,z58])],[(0,[z106,z6,z1,z477,z7,z4,z5]),(0,[z6,z1,z2,z7,z107,z4,z5]),(0,[z6,z1,z2,z7,z4,z647,z5]),(0,[z6,z1,z2,z7,z4,z183,z5]),(0,[z6,z648,z1,z2,z7,z4,z5]),(0,[z214,z6,z1,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z494,z5]),(0,[z6,z1,z2,z7,z4,z649,z31])],[(0,[z6,z1,z2,z7,z650,z4,z5]),(0,[z651,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z58,z31]),(0,[z652,z6,z1,z2,z7,z4,z5])],[(0,[z34,z6,z1,z2,z3,z7,z4]),(0,[z653,z6,z1,z2,z7,z4,z5]),(1,[z53,z1,z2,z7,z98,z5]),(0,[z6,z1,z2,z7,z4,z654,z5]),(0,[z34,z6,z1,z14,z2,z7,z4])]],
   [[(0,[z655,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z72,z2,z7,z264,z5]),(0,[z6,z1,z2,z7,z4,z656,z5])],[(0,[z6,z129,z1,z2,z7,z4,z31]),(0,[z17,z6,z1,z2,z22,z7,z4]),(0,[z546,z6,z1,z2,z7,z4,z5]),(1,[z6,z1,z2,z7,z396,z5]),(0,[z6,z1,z2,z7,z4,z657,z5])],[(0,[z17,z75,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z31,z5]),(0,[z6,z1,z429,z2,z7,z4,z13]),(0,[z6,z658,z1,z2,z7,z4,z5])],[(0,[z75,z6,z1,z2,z7,z4,z5]),(0,[z199,z6,z1,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z112,z5]),(0,[z6,z1,z2,z145,z7,z4,z5]),(0,[z6,z1,z2,z7,z659,z4,z5])],[(0,[z6,z1,z2,z7,z4,z649,z5]),(1,[z6,z2,z7,z4,z31,z13]),(0,[z6,z1,z52,z2,z7,z4,z13])],[(0,[z0,z6,z1,z2,z117,z4,z5]),(0,[z6,z1,z160,z2,z7,z4,z31]),(0,[z6,z1,z101,z2,z7,z4,z31]),(0,[z6,z1,z2,z7,z4,z58,z5]),(0,[z6,z1,z2,z7,z170,z4,z138])],[(0,[z6,z1,z18,z160,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z660,z5]),(0,[z6,z1,z661,z2,z7,z4,z5]),(0,[z6,z1,z51,z2,z7,z170,z4]),(0,[z6,z1,z2,z7,z170,z4,z92])],[(1,[z23,z1,z18,z7,z4,z5]),(0,[z6,z662,z1,z2,z7,z4,z5]),(0,[z142,z6,z1,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z663,z5])]],
   [[(0,[z664,z6,z1,z2,z7,z4,z5]),(0,[z644,z34,z6,z1,z2,z7,z4]),(0,[z33,z6,z1,z2,z7,z4,z31]),(0,[z6,z1,z665,z2,z7,z4,z5]),(0,[z666,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z667,z4,z5])],[(0,[z6,z1,z2,z7,z668,z4,z5]),(0,[z6,z669,z1,z2,z7,z4,z5]),(0,[z17,z86,z6,z1,z2,z7,z4]),(0,[z199,z6,z1,z2,z7,z4,z31]),(0,[z6,z1,z103,z2,z7,z4,z5]),(0,[z670,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z287,z64,z5]),(0,[z671,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z354,z2,z7,z4,z267]),(0,[z6,z1,z2,z672,z7,z4,z5]),(0,[z673,z6,z1,z2,z7,z4,z5])],[(0,[z6,z1,z2,z3,z84,z4,z5]),(0,[z6,z1,z2,z7,z81,z104,z5]),(0,[z17,z6,z1,z2,z7,z84,z4]),(0,[z6,z1,z2,z7,z4,z5,z224]),(0,[z6,z1,z52,z2,z7,z4,z31]),(0,[z6,z1,z354,z2,z7,z64,z5])],[(0,[z86,z6,z1,z2,z7,z4,z13]),(0,[z6,z1,z2,z674,z7,z4,z5]),(0,[z6,z1,z2,z20,z7,z4,z13]),(0,[z6,z1,z2,z675,z7,z4,z5]),(0,[z6,z1,z2,z531,z7,z4,z5])],[(0,[z6,z676,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z677,z5]),(0,[z6,z1,z340,z2,z7,z4,z5]),(0,[z653,z34,z6,z1,z2,z7,z4]),(1,[z34,z6,z1,z2,z7,z396]),(0,[z6,z1,z678,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z31,z166]),(0,[z6,z679,z1,z2,z7,z4,z5]),(1,[z6,z1,z2,z7,z4,z528]),(0,[z6,z1,z101,z2,z7,z4,z5])],[(0,[z655,z34,z6,z1,z2,z7,z4]),(0,[z6,z1,z680,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z681,z4,z5]),(0,[z6,z1,z2,z7,z682,z4,z5])],[(1,[z6,z1,z2,z7,z4,z488]),(0,[z6,z1,z2,z7,z4,z683,z5]),(0,[z34,z6,z1,z2,z7,z287,z4]),(0,[z34,z6,z1,z2,z7,z146,z4]),(0,[z6,z1,z72,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z5,z684])],[(0,[z6,z685,z1,z2,z7,z4,z5]),(1,[z6,z1,z504,z7,z4,z5]),(0,[z33,z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z146,z4,z5]),(0,[z6,z1,z2,z7,z4,z58,z166])]],
   [[(0,[z686,z6,z1,z2,z7,z4,z5]),(0,[z75,z34,z6,z1,z2,z7,z4]),(0,[z6,z1,z687,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z688,z4,z5]),(0,[z34,z6,z1,z2,z7,z4,z85]),(0,[z6,z288,z1,z2,z7,z4,z13]),(0,[z6,z1,z354,z7,z264,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z689])],[(0,[z86,z6,z1,z2,z7,z4,z31]),(0,[z53,z6,z1,z83,z2,z7,z5]),(0,[z33,z17,z6,z1,z2,z7,z4]),(0,[z6,z1,z690,z2,z7,z4,z5])],[(0,[z106,z6,z1,z46,z7,z4,z5]),(0,[z106,z6,z1,z2,z7,z4,z538]),(1,[z6,z1,z2,z7,z548,z5]),(0,[z6,z1,z2,z691,z7,z4,z5]),(0,[z6,z1,z2,z7,z692,z4,z5]),(0,[z6,z1,z693,z2,z7,z4,z5]),(0,[z6,z1,z2,z38,z7,z170,z4])],[(0,[z6,z1,z2,z694,z7,z4,z5]),(0,[z6,z1,z695,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z696,z4,z5]),(0,[z6,z1,z7,z264,z4,z64,z5])],[(0,[z17,z6,z1,z48,z2,z7,z4]),(0,[z19,z6,z1,z20,z7,z4,z5]),(0,[z6,z2,z63,z7,z84,z4,z5]),(0,[z6,z1,z2,z91,z7,z97,z5])],[(0,[z6,z1,z2,z7,z4,z5,z697]),(1,[z17,z34,z1,z2,z7,z4]),(0,[z17,z6,z1,z427,z7,z4,z5]),(1,[z6,z1,z2,z57,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z486]),(0,[z698,z6,z1,z2,z7,z4,z5]),(1,[z6,z1,z354,z7,z264,z5]),(0,[z6,z699,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z700,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z5,z701])],[(0,[z582,z6,z1,z2,z7,z4,z5]),(0,[z6,z702,z1,z2,z7,z4,z5]),(1,[z6,z1,z2,z7,z4,z123]),(0,[z6,z1,z2,z3,z7,z4,z123]),(0,[z6,z1,z703,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z287,z4,z5]),(0,[z6,z288,z1,z2,z7,z4,z31]),(0,[z6,z1,z704,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z4,z570,z5]),(0,[z705,z6,z1,z2,z7,z4,z5]),(1,[z6,z1,z2,z7,z4,z187]),(0,[z6,z1,z2,z7,z4,z396,z5]),(0,[z6,z1,z706,z2,z7,z4,z5]),(0,[z6,z1,z354,z2,z7,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z6,z56,z82,z2,z7,z4]),(0,[z6,z1,z2,z505,z471,z5]),(0,[z6,z1,z707,z2,z7,z5]),(0,[z708,z1,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z392,z13]),(0,[z6,z1,z2,z7,z709,z5]),(0,[z34,z6,z1,z2,z7,z193]),(0,[z6,z1,z2,z7,z710,z5]),(0,[z6,z1,z2,z7,z151,z5]),(0,[z6,z1,z2,z182,z4,z31])],[(0,[z17,z6,z1,z137,z7,z4]),(0,[z34,z6,z39,z2,z63,z4]),(0,[z6,z90,z333,z84,z4,z5]),(0,[z6,z1,z711,z7,z4,z5]),(0,[z6,z1,z2,z7,z712,z5])],[],[(0,[z17,z6,z1,z713,z7,z4])],[(0,[z6,z1,z714,z7,z4,z5]),(0,[z715,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z716]),(0,[z6,z1,z626,z7,z4,z59])],[(0,[z6,z1,z2,z7,z4,z717])],[(0,[z6,z1,z2,z7,z718,z4])],[(0,[z86,z1,z2,z719,z4,z5]),(0,[z17,z410,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z181,z5]),(0,[z6,z1,z2,z7,z4,z720]),(0,[z6,z1,z704,z7,z4,z59])],[(0,[z6,z1,z2,z721,z4,z5]),(0,[z86,z34,z1,z2,z117,z4]),(0,[z17,z417,z1,z2,z7,z4]),(0,[z722,z6,z1,z2,z7,z4]),(0,[z33,z6,z2,z7,z4,z31]),(0,[z6,z1,z52,z2,z7,z310])],[(0,[z6,z1,z723,z2,z4,z5]),(0,[z6,z1,z2,z7,z170,z92])],[(0,[z6,z1,z2,z7,z4,z724]),(0,[z6,z1,z2,z7,z4,z725])],[(0,[z6,z1,z2,z7,z726,z5]),(0,[z6,z1,z2,z7,z4,z727])],[(0,[z6,z1,z2,z7,z4,z728]),(0,[z410,z1,z160,z7,z4,z5]),(0,[z6,z196,z2,z7,z104,z5])],[(0,[z53,z1,z2,z7,z98,z5])],[(0,[z223,z6,z1,z83,z2,z5]),(0,[z6,z1,z2,z7,z4,z729]),(0,[z17,z6,z1,z730,z7,z4]),(0,[z17,z652,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z731])]],
   [[(0,[z6,z1,z504,z7,z4,z732]),(0,[z6,z1,z340,z2,z287,z5]),(0,[z6,z1,z340,z52,z2,z5]),(0,[z6,z1,z2,z694,z97,z5])],[(1,[z1,z2,z7,z733,z5]),(0,[z17,z6,z1,z2,z275,z4]),(0,[z139,z6,z1,z2,z7,z30]),(0,[z734,z6,z1,z2,z7,z4])],[(0,[z6,z1,z2,z7,z4,z735]),(0,[z736,z6,z1,z2,z7,z4])],[(0,[z6,z1,z2,z28,z4,z538]),(0,[z34,z1,z2,z7,z4,z565]),(0,[z6,z737,z1,z2,z7,z4]),(0,[z6,z1,z2,z738,z4,z5]),(0,[z6,z2,z7,z4,z31,z13]),(0,[z615,z6,z1,z83,z2,z5])],[(0,[z6,z1,z739,z7,z4,z5]),(0,[z142,z6,z1,z2,z7,z740]),(0,[z6,z1,z741,z7,z4,z5]),(0,[z6,z1,z2,z7,z742,z5]),(0,[z6,z743,z1,z2,z7,z4])],[(0,[z6,z1,z2,z7,z4,z744]),(0,[z6,z1,z168,z2,z76,z7]),(0,[z6,z2,z7,z4,z745,z5]),(0,[z746,z6,z1,z2,z7,z4])],[(0,[z23,z1,z18,z7,z4,z5]),(0,[z297,z6,z252,z2,z7,z4]),(0,[z6,z1,z2,z7,z747,z5])],[(0,[z6,z1,z83,z2,z748,z5])],[(0,[z349,z1,z22,z7,z4,z5]),(0,[z1,z2,z7,z733,z81,z5]),(0,[z6,z1,z2,z7,z749,z5]),(0,[z19,z6,z20,z7,z4,z401])],[(0,[z1,z750,z2,z7,z4,z5]),(0,[z6,z1,z52,z2,z7,z281]),(0,[z6,z1,z751,z2,z7,z4]),(0,[z6,z2,z7,z667,z4,z13])],[],[(0,[z0,z1,z2,z425,z4,z5]),(0,[z199,z34,z1,z2,z7,z81]),(0,[z6,z1,z2,z7,z170,z396])],[(0,[z6,z1,z255,z2,z84,z5]),(0,[z199,z6,z1,z340,z2,z5]),(0,[z410,z1,z2,z7,z471,z5]),(0,[z6,z1,z2,z7,z752,z5])],[(0,[z106,z48,z2,z7,z4,z9]),(0,[z6,z1,z2,z7,z4,z753])],[(0,[z6,z1,z2,z28,z392,z5]),(0,[z6,z1,z2,z754,z4,z5]),(0,[z6,z1,z2,z7,z4,z755]),(0,[z6,z1,z2,z7,z4,z756]),(0,[z6,z757,z1,z2,z7,z4]),(0,[z758,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z759,z5]),(0,[z6,z1,z2,z760,z4,z5]),(0,[z6,z1,z2,z4,z5,z761])],[(0,[z6,z1,z762,z2,z7,z4]),(0,[z6,z1,z763,z2,z7,z4]),(0,[z6,z1,z2,z7,z764,z31]),(0,[z6,z1,z765,z2,z7,z4])]],
   [[(0,[z1,z766,z2,z7,z4,z5]),(0,[z6,z1,z2,z91,z97,z5])],[],[(0,[z6,z293,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z471,z13])],[(0,[z6,z1,z767,z2,z7,z4]),(0,[z6,z1,z255,z2,z7,z5]),(0,[z41,z1,z2,z7,z4,z32])],[(0,[z6,z1,z477,z7,z4,z13]),(0,[z6,z1,z768,z2,z4,z5]),(0,[z17,z34,z1,z2,z7,z4])],[(0,[z6,z1,z2,z7,z4,z769]),(0,[z6,z1,z2,z7,z4,z123]),(0,[z6,z1,z770,z7,z4,z5]),(0,[z6,z1,z185,z146,z4,z486]),(0,[z6,z1,z2,z771,z4,z5])],[(0,[z6,z1,z2,z772,z4,z5]),(0,[z6,z1,z773,z2,z7,z5])],[(0,[z6,z1,z2,z7,z774,z5]),(0,[z653,z6,z1,z2,z7,z396]),(0,[z775,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z267])],[(0,[z6,z1,z2,z7,z300,z31]),(0,[z6,z1,z776,z2,z7,z4]),(0,[z6,z1,z2,z4,z5,z777]),(0,[z6,z2,z7,z4,z13,z701]),(0,[z6,z1,z2,z7,z4,z778])],[(0,[z6,z1,z2,z107,z4,z9]),(0,[z6,z1,z779,z7,z4,z5]),(0,[z199,z1,z2,z7,z81,z31]),(0,[z780,z6,z1,z2,z7,z4]),(0,[z19,z6,z20,z7,z4,z5]),(0,[z6,z1,z2,z7,z471,z218]),(0,[z6,z1,z2,z7,z781,z5]),(0,[z6,z1,z2,z7,z4,z782])],[(0,[z6,z1,z783,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z784])],[(0,[z68,z129,z2,z7,z4,z488]),(0,[z17,z6,z1,z2,z89,z4]),(0,[z153,z34,z1,z2,z7,z4]),(0,[z6,z623,z2,z7,z4,z13])],[(0,[z6,z1,z2,z7,z785,z5]),(0,[z6,z1,z2,z7,z4,z786])],[(0,[z17,z6,z1,z2,z7,z300]),(0,[z6,z1,z128,z137,z7,z4]),(0,[z6,z1,z2,z7,z4,z787]),(0,[z17,z278,z1,z2,z7,z4]),(0,[z6,z1,z2,z57,z4,z510])],[(0,[z86,z1,z2,z76,z117,z5]),(0,[z1,z2,z3,z719,z4,z5]),(0,[z6,z1,z2,z7,z788,z5]),(0,[z6,z1,z2,z789,z4,z5]),(0,[z6,z1,z2,z7,z4,z790]),(0,[z6,z1,z791,z7,z4,z5]),(0,[z6,z1,z72,z7,z64,z13])],[(0,[z6,z1,z2,z7,z4,z792])]],
   [[(0,[z34,z637,z1,z2,z7,z4])],[(1,[z750,z2,z7,z4,z5])],[(0,[z6,z1,z2,z793,z4,z5]),(0,[z6,z1,z333,z7,z4,z31])],[(0,[z75,z1,z22,z7,z4,z5]),(0,[z794,z1,z2,z7,z4,z5]),(0,[z1,z2,z7,z795,z4,z13])],[(0,[z17,z6,z1,z796,z7,z4]),(0,[z17,z6,z1,z2,z7,z181])],[(0,[z6,z1,z2,z7,z4,z5]),(0,[z6,z1,z797,z2,z7,z4]),(0,[z17,z6,z1,z798,z7,z4]),(0,[z186,z6,z1,z2,z257,z4]),(0,[z6,z1,z2,z7,z799,z5])],[(0,[z6,z1,z2,z800,z4,z5]),(0,[z6,z1,z2,z7,z4,z801])],[(0,[z17,z6,z1,z2,z7,z4]),(0,[z75,z34,z1,z22,z7,z4]),(0,[z6,z1,z2,z7,z4,z802]),(0,[z34,z6,z1,z2,z7,z45]),(0,[z803,z1,z2,z7,z4,z5])],[(0,[z106,z6,z364,z2,z7,z4]),(0,[z6,z1,z2,z7,z151,z273]),(0,[z6,z1,z374,z7,z64,z5]),(0,[z6,z1,z2,z7,z804,z5]),(0,[z805,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z170,z323])],[(0,[z6,z1,z46,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z806])],[(0,[z6,z1,z807,z7,z4,z5])],[(0,[z6,z1,z808,z7,z4,z5]),(0,[z6,z1,z2,z809,z7,z4]),(0,[z34,z6,z1,z2,z7,z810]),(0,[z1,z2,z7,z4,z13,z811]),(0,[z6,z1,z7,z4,z5,z812]),(0,[z813,z6,z1,z2,z7,z4])],[(0,[z6,z1,z2,z7,z4,z814]),(0,[z6,z1,z2,z7,z170,z815])],[(0,[z86,z1,z2,z117,z4,z5])],[(0,[z816,z1,z2,z7,z4,z5]),(0,[z817,z1,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z181,z273])]],
   [[(0,[z6,z1,z2,z505,z498,z5])],[(0,[z6,z1,z2,z7,z4,z818]),(0,[z6,z252,z2,z7,z4,z31]),(0,[z6,z196,z2,z7,z104,z356])],[],[],[(0,[z6,z1,z2,z7,z4,z819])],[(0,[z6,z1,z2,z7,z529,z13]),(0,[z6,z1,z255,z168,z2,z7]),(0,[z6,z1,z83,z2,z161,z5])],[(0,[z6,z1,z51,z2,z7,z193]),(0,[z6,z1,z2,z7,z4,z820]),(0,[z6,z1,z7,z4,z812,z166])],[(0,[z6,z1,z2,z7,z4,z821]),(0,[z6,z2,z7,z4,z13,z149])],[(0,[z6,z1,z2,z7,z4,z822])],[],[(0,[z6,z1,z2,z7,z392,z31])],[(0,[z17,z6,z1,z2,z7,z823]),(0,[z824,z6,z1,z2,z7,z4])],[(0,[z6,z1,z825,z7,z4,z5]),(0,[z34,z6,z1,z2,z7,z740]),(0,[z6,z1,z83,z2,z188,z5])],[(0,[z6,z1,z2,z7,z826,z5]),(0,[z129,z750,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z827,z4]),(0,[z6,z1,z828,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z829]),(0,[z17,z34,z1,z427,z7,z4]),(1,[z6,z2,z7,z4,z745])],[(0,[z106,z17,z48,z2,z7,z4]),(0,[z6,z1,z2,z7,z830,z5]),(0,[z6,z1,z2,z7,z92,z815])],[]],
   [[(0,[z6,z1,z2,z831,z7,z4]),(0,[z6,z1,z137,z7,z4,z5]),(0,[z17,z6,z1,z714,z7,z4]),(0,[z6,z1,z832,z7,z4,z5])],[(0,[z6,z1,z101,z137,z7,z4]),(0,[z6,z1,z690,z145,z4,z5]),(0,[z6,z1,z185,z146,z4,z13]),(0,[z6,z1,z389,z2,z4,z125]),(0,[z6,z1,z105,z145,z4,z5]),(0,[z6,z1,z2,z7,z4,z833])],[(0,[z34,z6,z1,z103,z7,z4]),(0,[z6,z1,z2,z4,z5,z834]),(0,[z6,z90,z2,z835,z4,z5])],[(0,[z17,z194,z1,z2,z7,z4])],[(0,[z6,z82,z2,z7,z4,z31]),(0,[z6,z1,z2,z182,z4,z510])],[(0,[z297,z6,z1,z836,z7,z4]),(0,[z6,z1,z2,z7,z4,z837]),(0,[z0,z1,z62,z3,z4,z5]),(0,[z6,z1,z2,z7,z4,z838]),(0,[z6,z1,z14,z137,z7,z4])],[(0,[z6,z1,z46,z28,z4,z5]),(0,[z6,z1,z2,z839,z7,z4]),(0,[z6,z1,z62,z7,z4,z13]),(0,[z6,z1,z60,z2,z7,z98]),(0,[z6,z1,z2,z7,z4,z840]),(0,[z6,z1,z52,z2,z7,z815])],[(0,[z6,z1,z2,z7,z810,z5]),(0,[z554,z1,z18,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z841]),(0,[z6,z1,z842,z2,z7,z4])],[(0,[z6,z1,z843,z2,z7,z4]),(0,[z6,z1,z2,z7,z844,z5]),(1,[z6,z1,z7,z845,z5])],[(0,[z6,z1,z2,z7,z846,z5]),(0,[z6,z1,z2,z7,z4,z847])],[(0,[z6,z1,z340,z2,z4,z5]),(0,[z34,z6,z1,z2,z57,z4]),(1,[z6,z1,z2,z7,z815])],[(0,[z6,z1,z2,z4,z848,z5]),(0,[z6,z1,z2,z849,z7,z5]),(0,[z850,z6,z1,z2,z7,z4]),(0,[z6,z1,z851,z2,z7,z4]),(0,[z6,z2,z7,z852,z4,z5])],[(0,[z6,z1,z2,z7,z4,z853]),(0,[z6,z1,z2,z7,z4,z854]),(0,[z6,z1,z2,z7,z4,z855]),(0,[z6,z1,z2,z7,z4,z856]),(0,[z41,z34,z1,z2,z7,z4]),(0,[z410,z1,z2,z7,z498,z5]),(0,[z6,z2,z7,z4,z209,z31])],[(0,[z6,z1,z82,z427,z7,z4]),(0,[z6,z1,z2,z7,z5,z857])],[(0,[z6,z1,z2,z7,z4,z858]),(0,[z6,z1,z2,z7,z4,z859])],[(0,[z6,z1,z860,z2,z7,z4])]],
   [[(0,[z6,z1,z2,z7,z426,z4]),(0,[z17,z6,z1,z2,z7,z498]),(0,[z17,z6,z196,z2,z7,z104]),(0,[z655,z6,z1,z2,z7,z193]),(0,[z6,z1,z2,z7,z4,z861]),(0,[z6,z39,z2,z63,z151,z5])],[(0,[z6,z1,z862,z7,z4,z5]),(0,[z17,z6,z1,z62,z7,z4])],[(0,[z6,z1,z128,z2,z7,z4]),(0,[z6,z1,z2,z863,z4,z5]),(0,[z6,z1,z2,z7,z498,z13]),(0,[z6,z1,z2,z7,z4,z864])],[(0,[z142,z6,z1,z2,z7,z785]),(0,[z6,z1,z2,z7,z865,z529]),(0,[z6,z56,z2,z57,z287,z5]),(0,[z6,z1,z2,z7,z4,z866]),(0,[z6,z1,z51,z2,z4,z85])],[(0,[z17,z6,z1,z2,z107,z4]),(0,[z17,z6,z1,z2,z7,z529]),(0,[z17,z1,z269,z2,z7,z4]),(0,[z6,z1,z2,z7,z867,z5])],[(0,[z6,z1,z868,z7,z4,z5]),(0,[z6,z1,z101,z7,z4,z12])],[],[(0,[z6,z1,z2,z7,z5,z869]),(0,[z17,z1,z2,z7,z4,z461]),(0,[z6,z1,z2,z7,z4,z401]),(0,[z6,z39,z2,z63,z181,z5]),(0,[z6,z56,z2,z7,z287,z13])],[(0,[z381,z6,z1,z2,z7,z764]),(0,[z6,z1,z2,z7,z4,z870])],[(0,[z17,z68,z129,z2,z7,z4]),(0,[z871,z6,z1,z2,z7,z4]),(0,[z34,z1,z2,z7,z4,z716]),(0,[z6,z1,z2,z7,z498,z218]),(0,[z872,z1,z2,z7,z4,z5]),(0,[z6,z154,z2,z7,z4,z31])],[(0,[z6,z1,z2,z7,z4,z732]),(0,[z6,z1,z2,z215,z4,z649])],[(0,[z6,z1,z2,z7,z471,z31])],[(0,[z6,z1,z2,z7,z4,z273])],[(0,[z6,z1,z477,z7,z4,z31]),(0,[z6,z1,z2,z835,z4,z5])],[(0,[z53,z34,z1,z2,z7,z98])],[(0,[z41,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z873,z5]),(0,[z6,z1,z874,z7,z4,z13])]],
   [[(0,[z34,z171,z1,z2,z7,z4])],[(0,[z1,z2,z719,z117,z4,z5]),(0,[z875,z6,z1,z2,z7,z4]),(0,[z876,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z295]),(0,[z6,z1,z2,z89,z471,z5])],[(0,[z6,z1,z2,z877,z4,z5])],[(0,[z6,z1,z137,z7,z4,z85]),(0,[z6,z1,z103,z146,z4,z5]),(0,[z6,z1,z2,z7,z4,z878])],[(0,[z19,z6,z20,z505,z4,z5]),(0,[z6,z1,z2,z7,z4,z879])],[(0,[z6,z1,z2,z7,z4,z70]),(0,[z6,z1,z168,z2,z7,z4]),(0,[z34,z6,z1,z105,z145,z4]),(0,[z6,z2,z7,z4,z31,z258]),(0,[z6,z1,z60,z2,z91,z7])],[(0,[z880,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z215,z4,z58])],[(0,[z17,z34,z1,z2,z7,z396]),(0,[z17,z1,z607,z2,z7,z4]),(0,[z6,z90,z2,z84,z4,z224]),(0,[z6,z288,z2,z7,z4,z745]),(0,[z6,z1,z72,z7,z64,z31])],[(0,[z6,z1,z52,z2,z7,z396]),(0,[z6,z1,z101,z7,z4,z307])],[(0,[z53,z1,z2,z7,z98,z187]),(0,[z286,z6,z1,z137,z7,z4]),(0,[z6,z1,z881,z7,z4,z31]),(0,[z6,z1,z83,z2,z36,z5])],[(0,[z6,z1,z2,z7,z4,z882]),(0,[z6,z1,z2,z7,z4,z883]),(0,[z884,z1,z2,z7,z4,z5])],[(0,[z53,z1,z2,z7,z98,z13]),(0,[z6,z219,z2,z7,z4,z13]),(0,[z6,z1,z14,z7,z4,z298])],[(0,[z6,z1,z885,z2,z7,z4]),(0,[z54,z1,z2,z7,z471,z5]),(0,[z6,z56,z2,z7,z287,z619])],[(0,[z886,z6,z1,z2,z7,z4]),(0,[z6,z1,z7,z4,z5,z887])],[(0,[z6,z1,z2,z888,z4,z5]),(0,[z10,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z889,z5]),(0,[z17,z6,z1,z2,z890,z4]),(0,[z17,z6,z1,z164,z2,z7])],[(0,[z34,z6,z1,z2,z7,z891]),(0,[z6,z1,z101,z7,z4,z59])]],
   [[(0,[z6,z1,z836,z7,z4,z5]),(0,[z17,z6,z1,z354,z7,z264]),(0,[z6,z1,z2,z505,z4,z5])],[(0,[z6,z1,z2,z892,z7,z5]),(0,[z6,z1,z2,z893,z4,z5]),(0,[z6,z1,z894,z2,z7,z4])],[(0,[z6,z1,z46,z7,z4,z31]),(0,[z6,z1,z895,z2,z7,z5]),(0,[z6,z1,z2,z7,z4,z896])],[(0,[z6,z1,z2,z7,z300,z538]),(0,[z23,z1,z18,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z897])],[(0,[z6,z1,z2,z7,z4,z898]),(0,[z6,z1,z899,z7,z4,z5])],[(0,[z6,z1,z2,z7,z4,z900]),(0,[z6,z1,z2,z7,z4,z901]),(0,[z6,z1,z340,z2,z426,z4]),(0,[z902,z1,z2,z7,z4,z5])],[(0,[z68,z129,z2,z7,z4,z5]),(0,[z17,z6,z1,z2,z28,z4]),(0,[z6,z1,z2,z7,z4,z903]),(0,[z53,z1,z2,z7,z733,z5]),(0,[z6,z1,z2,z7,z4,z235])],[(0,[z6,z1,z2,z7,z4,z904]),(0,[z17,z6,z1,z2,z7,z905]),(0,[z6,z1,z2,z7,z906,z5])],[(0,[z17,z6,z1,z825,z7,z4]),(0,[z6,z160,z832,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z907])],[(0,[z6,z1,z908,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z909]),(0,[z6,z1,z626,z7,z4,z120]),(0,[z6,z1,z101,z7,z4,z812])],[(0,[z6,z1,z2,z28,z4,z9]),(0,[z0,z1,z504,z3,z4,z5]),(0,[z17,z6,z1,z2,z7,z396]),(0,[z6,z1,z137,z7,z4,z58]),(0,[z6,z56,z2,z182,z287,z5]),(0,[z6,z1,z2,z7,z4,z910])],[(0,[z6,z1,z504,z7,z4,z13])],[(0,[z6,z1,z2,z7,z911,z4]),(0,[z41,z68,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z912,z5]),(0,[z6,z1,z2,z7,z4,z913]),(0,[z6,z1,z2,z914,z4,z5]),(0,[z6,z1,z2,z7,z4,z915])],[(0,[z6,z1,z2,z7,z4,z916]),(0,[z917,z6,z1,z2,z7,z4]),(0,[z6,z1,z14,z7,z4,z812])],[(0,[z6,z1,z2,z7,z918,z5]),(0,[z6,z1,z2,z7,z529,z31]),(0,[z6,z1,z2,z7,z548,z13]),(0,[z6,z1,z2,z7,z4,z919])],[(0,[z34,z419,z1,z2,z7,z4]),(0,[z34,z1,z2,z7,z4,z203])]],
   [[(0,[z6,z920,z2,z7,z4,z5]),(0,[z6,z82,z2,z7,z4,z104]),(0,[z921,z6,z1,z2,z7,z4]),(0,[z6,z1,z7,z4,z31,z922])],[(0,[z6,z1,z2,z7,z4,z923]),(0,[z0,z1,z2,z3,z4,z123]),(0,[z924,z6,z1,z2,z7,z4])],[(0,[z6,z1,z925,z2,z7,z4]),(0,[z19,z17,z6,z20,z7,z4]),(0,[z34,z1,z2,z7,z4,z183]),(0,[z34,z6,z1,z72,z7,z64]),(0,[z6,z1,z2,z7,z4,z926]),(0,[z6,z1,z502,z7,z4,z166]),(0,[z6,z1,z2,z7,z4,z927])],[(0,[z6,z1,z2,z928,z4,z5]),(0,[z6,z1,z767,z2,z7,z529]),(0,[z17,z6,z1,z185,z146,z4])],[(0,[z17,z23,z1,z18,z7,z4]),(0,[z6,z1,z2,z7,z548,z31]),(0,[z6,z39,z2,z63,z4,z5]),(0,[z6,z1,z2,z91,z5,z233])],[(0,[z106,z48,z2,z7,z4,z5]),(0,[z17,z6,z1,z2,z7,z929]),(0,[z6,z1,z2,z7,z4,z930])],[(0,[z6,z364,z2,z7,z4,z13]),(0,[z19,z6,z20,z7,z4,z13]),(0,[z6,z1,z83,z2,z235,z36])],[(0,[z6,z1,z2,z7,z931,z5]),(0,[z6,z1,z2,z57,z287,z5])],[(0,[z142,z6,z364,z2,z7,z4]),(0,[z932,z1,z2,z7,z4,z5]),(0,[z6,z2,z404,z7,z4,z13]),(0,[z6,z1,z7,z4,z845,z5]),(0,[z6,z1,z2,z7,z4,z933])],[(0,[z1,z280,z22,z7,z4,z5]),(0,[z6,z1,z934,z2,z7,z4]),(0,[z34,z6,z1,z2,z7,z873])],[(0,[z15,z1,z22,z7,z4,z5]),(0,[z6,z1,z185,z146,z4,z31]),(0,[z6,z1,z51,z2,z4,z268])],[(0,[z6,z1,z2,z7,z935,z5]),(0,[z34,z1,z2,z7,z682,z4]),(0,[z6,z1,z2,z7,z4,z936]),(0,[z6,z1,z2,z7,z13,z937])],[(0,[z6,z1,z2,z7,z13,z45]),(0,[z6,z1,z51,z164,z2,z85])],[(0,[z1,z2,z7,z98,z733,z5]),(0,[z17,z53,z1,z2,z7,z98]),(0,[z19,z6,z20,z7,z4,z218]),(0,[z6,z1,z51,z2,z4,z927])],[(0,[z6,z1,z2,z7,z938,z5]),(0,[z17,z6,z1,z333,z7,z4]),(0,[z6,z2,z7,z287,z852,z5]),(0,[z6,z1,z83,z60,z2,z7])],[(0,[z6,z1,z939,z7,z4,z5]),(0,[z6,z1,z62,z7,z4,z31]),(0,[z6,z1,z103,z145,z4,z5]),(0,[z6,z1,z2,z7,z852,z5]),(0,[z6,z1,z940,z7,z4,z5])]],
   [[(0,[z75,z1,z22,z7,z4,z13]),(0,[z17,z34,z1,z2,z7,z193])],[(0,[z6,z1,z2,z107,z4,z5]),(0,[z941,z1,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z942,z5]),(0,[z286,z6,z1,z2,z7,z281]),(0,[z17,z6,z1,z2,z7,z471]),(0,[z943,z1,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z944,z5]),(0,[z17,z6,z1,z427,z7,z4]),(0,[z6,z1,z2,z445,z7,z193])],[(0,[z6,z1,z2,z7,z4,z945]),(0,[z803,z1,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z946])],[(0,[z6,z1,z2,z7,z392,z538])],[(0,[z6,z1,z2,z947,z4,z5]),(0,[z6,z1,z2,z7,z4,z948])],[(0,[z750,z48,z2,z7,z4,z5]),(0,[z6,z1,z454,z7,z4,z166])],[(0,[z6,z1,z2,z949,z7,z5]),(0,[z6,z1,z2,z7,z4,z950]),(0,[z6,z1,z2,z7,z951,z4])],[(0,[z6,z1,z2,z7,z4,z952]),(0,[z6,z1,z2,z7,z953,z5]),(0,[z109,z6,z82,z2,z7,z4])],[(0,[z6,z1,z954,z2,z7,z4]),(0,[z34,z6,z1,z255,z2,z7])],[(0,[z34,z6,z1,z340,z2,z4]),(0,[z17,z1,z2,z7,z4,z503]),(0,[z6,z1,z2,z7,z498,z31]),(0,[z6,z1,z185,z146,z4,z234]),(0,[z6,z1,z955,z2,z7,z4])],[(0,[z6,z1,z2,z7,z4,z956]),(0,[z6,z1,z2,z7,z4,z957]),(0,[z6,z1,z730,z7,z4,z5]),(0,[z17,z6,z90,z2,z84,z4]),(0,[z6,z1,z2,z7,z4,z356]),(0,[z958,z1,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z4,z959])],[(0,[z6,z1,z960,z7,z4,z5]),(0,[z6,z56,z2,z7,z852,z5])],[(0,[z41,z53,z1,z2,z7,z4])]],
   [[(0,[z6,z1,z2,z7,z4,z961]),(0,[z6,z1,z2,z962,z4,z5]),(0,[z381,z68,z1,z2,z7,z4]),(0,[z6,z1,z2,z963,z4,z5]),(0,[z6,z1,z964,z2,z7,z4]),(0,[z6,z965,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z966]),(0,[z6,z56,z2,z7,z287,z31]),(0,[z6,z1,z707,z2,z7,z13])],[(0,[z6,z1,z477,z7,z300,z5]),(0,[z6,z1,z2,z7,z4,z967]),(0,[z297,z6,z1,z137,z7,z4]),(0,[z34,z54,z1,z2,z7,z4]),(0,[z6,z1,z185,z505,z4,z5]),(0,[z6,z1,z2,z89,z498,z5]),(0,[z6,z1,z2,z7,z151,z13])],[(0,[z106,z750,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z968]),(0,[z1,z2,z7,z4,z5,z716]),(0,[z6,z1,z2,z505,z4,z401]),(0,[z969,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z970]),(0,[z6,z522,z2,z63,z4,z5]),(0,[z6,z1,z2,z38,z4,z494])],[(0,[z6,z1,z2,z971,z7,z4]),(0,[z6,z1,z2,z7,z4,z972]),(0,[z6,z1,z2,z973,z4,z5]),(0,[z17,z6,z1,z2,z7,z193])],[(0,[z6,z1,z2,z974,z4,z5]),(0,[z17,z673,z1,z2,z7,z4]),(0,[z17,z6,z1,z2,z975,z4]),(0,[z17,z6,z39,z2,z63,z4]),(0,[z6,z1,z2,z976,z7,z4])],[],[(0,[z6,z456,z2,z7,z4,z31]),(0,[z6,z1,z2,z7,z4,z977]),(0,[z6,z1,z2,z7,z4,z978]),(0,[z6,z1,z2,z7,z815,z138])],[(0,[z6,z595,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z151,z31])],[(0,[z6,z1,z2,z7,z181,z13])],[(0,[z6,z1,z2,z979,z4,z5]),(0,[z6,z1,z2,z91,z71,z5]),(0,[z6,z270,z2,z7,z4,z13]),(0,[z33,z6,z2,z7,z4,z745]),(0,[z6,z1,z2,z7,z4,z486]),(1,[z6,z1,z2,z4,z927])],[(0,[z6,z1,z2,z980,z7,z4]),(0,[z6,z1,z60,z2,z7,z81]),(0,[z6,z1,z2,z7,z193,z138]),(0,[z6,z981,z2,z7,z4,z5]),(0,[z6,z1,z640,z7,z4,z166])],[(0,[z6,z1,z2,z982,z4,z5])],[(0,[z581,z6,z20,z7,z4,z5]),(0,[z17,z1,z622,z2,z7,z4]),(0,[z54,z1,z2,z7,z498,z5])],[(0,[z6,z616,z2,z7,z287,z5]),(0,[z6,z1,z137,z7,z4,z13]),(0,[z6,z196,z2,z7,z104,z13])],[(0,[z6,z1,z2,z7,z4,z983]),(0,[z6,z1,z7,z984,z4,z5]),(0,[z6,z1,z985,z2,z7,z5]),(0,[z17,z1,z2,z691,z7,z4])],[(0,[z6,z1,z986,z7,z4,z5]),(1,[z6,z832,z7,z4,z5])]],
   [[(0,[z75,z1,z21,z22,z7,z4]),(0,[z6,z1,z2,z7,z4,z987]),(0,[z6,z1,z2,z7,z748,z5])],[(0,[z6,z988,z2,z7,z4,z5]),(0,[z417,z1,z2,z7,z98,z5]),(0,[z6,z1,z2,z4,z13,z834])],[(0,[z23,z1,z317,z7,z4,z5]),(0,[z34,z6,z1,z2,z962,z4]),(0,[z989,z1,z2,z7,z4,z5]),(0,[z6,z599,z2,z84,z4,z5])],[(0,[z6,z1,z2,z7,z4,z990]),(0,[z6,z1,z427,z7,z4,z5]),(0,[z34,z6,z1,z504,z7,z4]),(0,[z6,z1,z2,z7,z4,z991]),(0,[z6,z1,z132,z2,z7,z380]),(0,[z6,z1,z7,z264,z845,z5])],[(0,[z6,z1,z47,z2,z7,z4]),(0,[z53,z1,z2,z7,z98,z31]),(0,[z34,z6,z1,z2,z7,z992]),(0,[z6,z1,z2,z7,z4,z993])],[(0,[z1,z18,z741,z7,z4,z5]),(0,[z324,z6,z1,z2,z371,z4]),(0,[z34,z6,z1,z2,z7,z151]),(0,[z6,z2,z7,z4,z745,z13])],[(0,[z6,z1,z46,z7,z300,z5]),(0,[z334,z1,z22,z7,z4,z5]),(0,[z17,z1,z375,z2,z7,z4]),(0,[z34,z6,z1,z2,z91,z97])],[],[(0,[z6,z1,z477,z7,z4,z538]),(0,[z6,z1,z2,z7,z4,z994])],[(0,[z6,z2,z7,z4,z31,z745])],[(0,[z6,z1,z2,z995,z4,z5]),(1,[z1,z2,z7,z4,z716])],[(0,[z6,z1,z996,z2,z7,z4]),(0,[z17,z6,z1,z2,z7,z548]),(0,[z6,z1,z2,z97,z432,z5]),(0,[z6,z1,z2,z7,z193,z5]),(0,[z6,z39,z2,z63,z4,z273]),(0,[z6,z658,z2,z7,z104,z5])],[(0,[z6,z1,z997,z7,z4,z5]),(0,[z6,z1,z998,z2,z7,z4]),(0,[z23,z1,z18,z7,z4,z31])],[(0,[z17,z6,z999,z2,z7,z4]),(0,[z6,z288,z82,z2,z7,z4]),(0,[z6,z1,z427,z7,z4,z166]),(0,[z410,z1,z185,z7,z4,z5]),(0,[z6,z1,z7,z4,z1000,z5])],[(0,[z410,z1,z2,z7,z4,z401]),(0,[z6,z1,z164,z2,z7,z5])],[(0,[z6,z1,z1001,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z1002]),(0,[z6,z1,z2,z7,z4,z1003]),(0,[z6,z1,z2,z7,z4,z1004]),(0,[z6,z2,z7,z4,z521,z31])]],
   [[(0,[z6,z1,z2,z97,z529,z5]),(0,[z86,z1,z2,z385,z117,z4]),(0,[z6,z1,z2,z91,z97,z13])],[(0,[z41,z75,z1,z2,z7,z4]),(0,[z6,z1005,z1,z2,z7,z4])],[(0,[z6,z2,z7,z4,z1006,z5]),(0,[z17,z493,z1,z2,z7,z4]),(0,[z34,z6,z1,z2,z863,z4]),(0,[z6,z1,z2,z7,z4,z1007]),(0,[z6,z1,z145,z505,z4,z5])],[(0,[z6,z1,z477,z7,z392,z5]),(0,[z6,z1,z255,z2,z7,z13]),(0,[z53,z6,z1,z340,z2,z5]),(0,[z1008,z6,z1,z2,z7,z4]),(0,[z6,z1,z354,z7,z264,z267])],[(0,[z6,z1,z2,z1009,z7,z4]),(0,[z6,z1,z2,z7,z4,z1010]),(0,[z6,z1,z504,z7,z4,z31]),(0,[z6,z1,z2,z7,z1011,z5])],[(0,[z23,z1,z18,z7,z4,z12]),(0,[z6,z1,z2,z7,z193,z166])],[(0,[z381,z6,z1,z2,z7,z4]),(0,[z6,z1,z1012,z2,z7,z4]),(0,[z6,z1,z2,z7,z992,z5]),(0,[z175,z1,z22,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z1013]),(0,[z6,z1,z2,z7,z4,z1014]),(0,[z6,z1,z773,z2,z7,z13])],[],[(0,[z1015,z1,z2,z7,z4,z5]),(0,[z6,z1,z164,z2,z7,z166])],[(0,[z6,z1,z2,z7,z740,z5]),(1,[z1,z741,z7,z4,z5]),(0,[z34,z6,z1,z1016,z7,z4]),(0,[z6,z1,z2,z7,z4,z1017]),(0,[z6,z1,z1018,z2,z7,z5])],[],[(0,[z1,z2,z7,z4,z183,z716]),(0,[z6,z1,z1019,z2,z7,z4])],[(0,[z6,z1,z2,z7,z1020,z5]),(0,[z1021,z1,z2,z7,z4,z5]),(1,[z6,z2,z835,z4,z5]),(0,[z6,z1,z2,z7,z785,z13])],[(0,[z6,z1,z46,z7,z4,z538]),(0,[z6,z1,z2,z1022,z4,z5])],[(0,[z6,z1,z2,z7,z4,z1023]),(0,[z6,z82,z2,z7,z84,z4]),(0,[z34,z6,z1,z2,z7,z785])],[(0,[z410,z1,z2,z7,z4,z5]),(0,[z6,z1,z1024,z2,z7,z4]),(0,[z6,z1025,z1,z2,z7,z4]),(0,[z19,z6,z20,z7,z4,z31])]],
   [[],[(0,[z0,z1,z2,z3,z4,z70]),(0,[z6,z1,z354,z7,z264,z5])],[(0,[z106,z34,z48,z2,z7,z4])],[(0,[z6,z1,z2,z7,z4,z1026]),(0,[z68,z6,z364,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z187])],[(0,[z0,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z426,z92]),(0,[z34,z1,z2,z7,z193,z183]),(0,[z19,z6,z20,z89,z4,z5]),(0,[z6,z1,z444,z52,z2,z7])],[(0,[z297,z6,z1,z2,z7,z4]),(0,[z75,z1,z741,z7,z4,z5])],[(0,[z17,z6,z1,z83,z2,z36]),(0,[z610,z6,z364,z2,z7,z4]),(0,[z6,z1,z52,z2,z7,z201]),(1,[z6,z1,z2,z748,z5])],[(0,[z6,z1,z46,z7,z392,z5]),(0,[z6,z1,z2,z7,z4,z1027])],[(0,[z75,z1,z22,z7,z4,z31]),(0,[z6,z1,z2,z7,z4,z1028]),(0,[z6,z1,z2,z1029,z7,z4]),(0,[z6,z1,z2,z7,z1030,z70]),(0,[z19,z6,z518,z7,z4,z5]),(0,[z6,z1,z2,z7,z5,z1031]),(0,[z6,z1,z2,z7,z4,z1032])],[(0,[z6,z999,z2,z7,z4,z5]),(0,[z17,z1,z2,z7,z579,z4]),(0,[z6,z1,z1033,z2,z7,z4]),(0,[z6,z1,z7,z4,z5,z1034])],[(0,[z6,z1,z1035,z7,z4,z5]),(0,[z34,z6,z1,z1036,z7,z4]),(0,[z1037,z1,z2,z7,z4,z5])],[(0,[z6,z1,z83,z2,z529,z5]),(0,[z6,z1,z2,z719,z4,z5]),(0,[z6,z1,z2,z7,z4,z1038]),(0,[z6,z1,z2,z7,z4,z218]),(0,[z6,z1,z2,z84,z181,z5])],[(0,[z6,z1,z2,z7,z1039,z5]),(0,[z86,z1,z2,z117,z4,z13]),(0,[z1040,z1,z2,z7,z4,z5])],[(0,[z262,z1,z2,z7,z98,z5]),(0,[z6,z1,z2,z7,z804,z31])],[(0,[z6,z1,z2,z385,z76,z7]),(0,[z6,z2,z63,z835,z4,z5])]],
   [[(0,[z6,z1,z2,z76,z7,z5]),(0,[z6,z1,z2,z7,z4,z1041]),(0,[z6,z2,z7,z4,z13,z600])],[(0,[z6,z1,z2,z7,z4,z1042]),(0,[z655,z6,z1,z454,z7,z4])],[(0,[z34,z6,z1,z477,z7,z4]),(0,[z6,z1,z2,z7,z4,z1043]),(0,[z199,z1,z370,z2,z7,z81]),(0,[z6,z1,z2,z7,z4,z1044])],[(0,[z86,z1,z2,z117,z4,z31]),(0,[z6,z1,z1045,z2,z7,z4]),(0,[z6,z1,z2,z507,z97,z5])],[(0,[z34,z6,z56,z2,z7,z287]),(0,[z1046,z6,z1,z2,z7,z4]),(0,[z6,z1,z1047,z2,z7,z4])],[(0,[z6,z1,z357,z7,z4,z298]),(0,[z6,z1,z2,z7,z78,z92])],[(0,[z6,z1,z2,z7,z426,z396]),(0,[z17,z6,z1,z1048,z7,z4]),(0,[z17,z422,z1,z2,z7,z4])],[(0,[z34,z6,z1,z2,z7,z774]),(0,[z6,z1,z2,z7,z4,z112])],[(0,[z6,z1,z2,z7,z4,z1049])],[(0,[z6,z1,z73,z7,z4,z213]),(0,[z6,z1050,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z4,z1051]),(0,[z6,z1,z2,z7,z300,z9]),(0,[z192,z1,z22,z7,z4,z5]),(0,[z6,z1,z2,z7,z1052,z5]),(0,[z6,z55,z160,z7,z4,z295]),(0,[z6,z1,z2,z7,z4,z1053]),(0,[z6,z1,z2,z7,z1054,z5]),(0,[z6,z1,z2,z7,z4,z619])],[(0,[z272,z1,z2,z117,z4,z5]),(0,[z6,z1,z2,z7,z1055,z5])],[(0,[z6,z1,z477,z7,z4,z9]),(0,[z6,z39,z82,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z131]),(0,[z1056,z6,z1,z2,z7,z4]),(0,[z142,z1,z2,z7,z4,z365]),(0,[z6,z1,z2,z7,z4,z1057])],[(0,[z34,z1,z2,z7,z4,z632]),(0,[z6,z1,z1058,z2,z7,z5]),(0,[z6,z1,z2,z7,z4,z1059])],[(0,[z6,z1,z2,z7,z4,z1060]),(0,[z6,z1,z2,z7,z929,z5]),(0,[z6,z90,z2,z84,z4,z5]),(0,[z6,z1,z2,z7,z4,z1061]),(0,[z6,z1,z52,z2,z7,z384])],[(0,[z23,z1,z741,z7,z4,z5]),(0,[z6,z1,z2,z1062,z4,z5]),(0,[z6,z1,z2,z7,z4,z1063])]],
   [[(0,[z17,z6,z1,z2,z1064,z4]),(0,[z6,z1,z2,z7,z4,z1065]),(0,[z6,z1,z73,z7,z4,z166])],[(0,[z106,z48,z2,z107,z4,z5]),(0,[z6,z1,z2,z7,z4,z1066]),(0,[z6,z55,z160,z7,z4,z5]),(0,[z6,z1,z2,z7,z181,z31]),(0,[z6,z1,z105,z145,z4,z13]),(0,[z6,z1,z2,z531,z4,z494])],[(0,[z6,z1,z2,z28,z4,z5]),(0,[z6,z1,z1067,z2,z4,z5]),(0,[z6,z1,z2,z275,z4,z5])],[(0,[z6,z1,z1068,z2,z4,z5]),(0,[z6,z56,z2,z7,z287,z510]),(0,[z1069,z6,z1,z2,z7,z4])],[(0,[z17,z6,z1,z103,z7,z4]),(0,[z6,z1,z2,z7,z4,z1070]),(0,[z6,z1,z83,z2,z638,z5])],[(0,[z6,z1,z364,z2,z7,z4]),(0,[z17,z0,z1,z2,z3,z4]),(0,[z6,z1,z2,z7,z4,z1071])],[(0,[z6,z1,z137,z7,z4,z31]),(0,[z6,z1,z1072,z2,z4,z5]),(0,[z6,z196,z2,z7,z104,z31]),(0,[z6,z1,z2,z4,z58,z927])],[(0,[z6,z1,z2,z7,z4,z1073]),(0,[z6,z1,z1074,z2,z7,z4]),(0,[z17,z671,z1,z2,z7,z4]),(0,[z6,z1,z137,z7,z30,z4]),(0,[z6,z1,z105,z145,z4,z31]),(0,[z6,z191,z2,z7,z4,z31]),(0,[z6,z1,z197,z7,z4,z59])],[(0,[z17,z1,z412,z2,z7,z4]),(0,[z34,z6,z1,z2,z7,z953]),(0,[z1075,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z182,z4,z5]),(0,[z41,z1,z2,z7,z4,z198])],[],[(0,[z142,z6,z1,z2,z7,z4]),(0,[z106,z47,z48,z2,z7,z4]),(0,[z6,z1,z340,z2,z4,z13]),(0,[z17,z1,z2,z7,z4,z140])],[(0,[z17,z1,z2,z7,z337,z4]),(0,[z172,z6,z1,z445,z7,z4]),(0,[z178,z6,z1,z2,z7,z193]),(0,[z6,z1,z2,z7,z4,z1076])],[(0,[z144,z1,z18,z7,z4,z5]),(0,[z6,z1077,z1,z2,z7,z4]),(0,[z17,z6,z1,z2,z57,z4]),(0,[z34,z6,z1,z2,z1078,z4])],[(0,[z1079,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z1080])],[(0,[z6,z1,z2,z7,z4,z1081]),(0,[z34,z6,z1,z2,z182,z4]),(0,[z1,z1082,z2,z7,z4,z5])],[(0,[z297,z6,z1,z427,z7,z4]),(0,[z6,z2,z7,z852,z104,z5]),(0,[z6,z1,z2,z7,z1083,z4]),(0,[z6,z1,z1084,z2,z7,z4])]],
   [[(0,[z34,z6,z1,z46,z7,z4]),(0,[z106,z10,z48,z2,z7,z4]),(0,[z6,z1,z2,z7,z396,z5]),(0,[z1085,z6,z1,z2,z7,z4])],[(0,[z6,z1,z46,z7,z4,z9]),(0,[z53,z1,z2,z7,z98,z332]),(0,[z17,z381,z1,z2,z7,z4])],[(0,[z6,z1,z2,z7,z1086,z5]),(0,[z6,z1,z2,z4,z5,z1087]),(0,[z6,z1,z2,z7,z4,z1088])],[(0,[z6,z1,z7,z4,z1089,z5])],[(0,[z644,z6,z1,z2,z169,z4]),(0,[z6,z522,z2,z7,z287,z5])],[(0,[z6,z1,z2,z7,z1090,z5])],[(0,[z6,z1,z2,z7,z1091,z4]),(0,[z6,z1,z205,z2,z4,z268])],[(0,[z6,z1,z1092,z2,z7,z4]),(0,[z6,z1093,z1,z2,z7,z4]),(0,[z6,z1,z1094,z7,z4,z5]),(0,[z6,z382,z2,z7,z4,z13]),(0,[z6,z1,z354,z7,z845,z5])],[(0,[z297,z68,z129,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z1095])],[(0,[z6,z1,z2,z7,z891,z5]),(0,[z17,z6,z1,z881,z7,z4]),(0,[z872,z1,z2,z7,z4,z13]),(0,[z6,z1,z2,z91,z97,z31])],[(0,[z17,z86,z1,z2,z117,z4]),(0,[z6,z1,z1096,z2,z7,z5]),(0,[z6,z1,z389,z2,z4,z85]),(0,[z6,z1,z2,z7,z31,z1097])],[(0,[z41,z1,z2,z3,z7,z4]),(0,[z6,z1,z2,z7,z1098,z4]),(0,[z17,z1,z2,z7,z4,z716]),(0,[z6,z1,z2,z7,z4,z528])],[(0,[z6,z1,z2,z7,z392,z9]),(0,[z6,z1,z2,z7,z4,z1099]),(0,[z6,z1,z255,z2,z7,z31])],[(0,[z6,z1,z1100,z2,z7,z4]),(0,[z6,z1,z1101,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z1102])],[(0,[z6,z1,z255,z2,z63,z5]),(0,[z1103,z6,z1,z2,z7,z4]),(0,[z6,z1,z770,z7,z4,z31]),(0,[z6,z1,z206,z2,z7,z207])],[(0,[z106,z48,z2,z28,z4,z5]),(0,[z6,z2,z835,z84,z4,z5])]],
   [[(0,[z6,z1,z2,z1104,z4,z5]),(0,[z6,z1,z145,z111,z4,z5]),(0,[z6,z1,z72,z7,z845,z5]),(0,[z6,z1,z2,z220,z4,z58])],[],[(0,[z6,z1,z1105,z2,z4,z5]),(0,[z6,z1,z185,z229,z4,z5]),(0,[z1106,z1,z2,z7,z4,z5])],[(0,[z6,z1,z2,z1107,z7,z4]),(0,[z6,z1,z2,z7,z4,z1108])],[(0,[z106,z6,z82,z2,z7,z4]),(0,[z652,z1,z2,z7,z81,z5]),(0,[z34,z6,z55,z160,z7,z4]),(0,[z6,z1,z2,z57,z4,z5]),(0,[z6,z1,z2,z7,z4,z1109])],[(0,[z34,z6,z1,z2,z76,z7])],[(0,[z19,z34,z6,z20,z7,z4]),(0,[z6,z1,z2,z7,z764,z5])],[(0,[z6,z1,z2,z7,z823,z5]),(0,[z17,z6,z1,z2,z772,z4]),(0,[z17,z6,z1,z105,z145,z4])],[(0,[z6,z1,z1110,z2,z7,z4]),(0,[z6,z1,z2,z748,z36,z5])],[(0,[z6,z750,z2,z7,z4,z5]),(0,[z6,z1,z1111,z7,z4,z5]),(0,[z6,z1,z83,z2,z36,z13])],[(0,[z34,z1,z2,z7,z396,z183]),(0,[z410,z1,z2,z505,z4,z5]),(0,[z6,z2,z7,z835,z4,z5]),(0,[z6,z1,z1112,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z1113]),(0,[z6,z2,z7,z4,z574,z31])],[(0,[z6,z1,z2,z1114,z4,z5])],[(0,[z17,z6,z1,z2,z7,z45]),(0,[z1115,z6,z1,z2,z7,z4]),(0,[z6,z450,z2,z7,z104,z5]),(0,[z6,z1,z2,z7,z4,z1116]),(0,[z6,z1,z429,z7,z4,z307])],[(0,[z6,z1,z2,z7,z4,z1117]),(0,[z6,z1,z2,z7,z4,z1118]),(0,[z6,z263,z2,z7,z104,z5]),(0,[z6,z2,z832,z7,z4,z5]),(0,[z6,z1,z2,z1119,z4,z5])],[(0,[z6,z1,z2,z7,z4,z31]),(0,[z6,z1,z2,z1120,z4,z5]),(0,[z1121,z6,z1,z2,z7,z4])],[(0,[z23,z34,z1,z18,z7,z4]),(0,[z546,z6,z1,z427,z7,z4]),(0,[z1122,z6,z1,z2,z7,z4])]],
   [[(0,[z41,z86,z1,z2,z7,z4]),(0,[z6,z1,z427,z7,z4,z13]),(0,[z6,z1,z2,z505,z4,z13]),(0,[z1123,z6,z1,z2,z7,z4])],[(0,[z410,z1,z145,z7,z4,z5])],[],[(0,[z17,z75,z1,z22,z7,z4]),(0,[z17,z6,z1,z2,z7,z918])],[(0,[z6,z1,z2,z89,z4,z5]),(0,[z6,z1,z2,z7,z4,z1124])],[(0,[z6,z1,z1125,z7,z4,z5]),(0,[z6,z1,z51,z2,z371,z4])],[(0,[z68,z129,z2,z7,z4,z13]),(0,[z6,z1,z1126,z2,z7,z4]),(0,[z6,z1,z2,z7,z193,z187]),(0,[z6,z1,z1127,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z1128]),(0,[z6,z1,z836,z7,z4,z31])],[(0,[z6,z1,z2,z7,z4,z12]),(0,[z6,z1,z2,z505,z4,z218]),(0,[z6,z1,z2,z7,z4,z1129])],[(0,[z6,z1,z2,z7,z4,z1130]),(0,[z6,z1,z2,z7,z193,z13]),(0,[z6,z1,z103,z7,z4,z5]),(0,[z6,z1,z2,z7,z151,z40])],[(0,[z6,z1,z2,z7,z4,z1131]),(0,[z6,z1,z2,z7,z1132,z4]),(0,[z6,z1,z1133,z2,z7,z4]),(0,[z34,z6,z1,z2,z505,z4]),(0,[z6,z1,z2,z7,z4,z1134]),(0,[z6,z1,z333,z7,z4,z5])],[(0,[z6,z1,z2,z7,z4,z1135]),(0,[z6,z1,z2,z7,z5,z1136]),(0,[z17,z438,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z1137]),(0,[z6,z1,z2,z7,z4,z1138])],[(0,[z1,z48,z477,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z1139]),(0,[z6,z1,z2,z1140,z4,z5]),(0,[z6,z1,z164,z2,z7,z13])],[(0,[z142,z68,z129,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z1141]),(0,[z6,z1,z448,z7,z264,z5])],[(0,[z6,z1,z2,z7,z1142,z5]),(0,[z6,z1,z2,z7,z4,z1143]),(0,[z6,z532,z2,z7,z287,z5]),(0,[z6,z1,z7,z1144,z4,z5])],[(0,[z736,z54,z1,z2,z7,z4]),(0,[z6,z1,z1145,z2,z4,z5])],[(0,[z54,z1,z2,z7,z4,z5]),(0,[z581,z48,z2,z7,z4,z5]),(0,[z6,z1,z713,z7,z4,z5]),(0,[z6,z1,z1146,z7,z4,z5]),(0,[z6,z1,z2,z7,z181,z40]),(0,[z6,z1,z2,z7,z4,z234])]],
   [[(0,[z6,z1,z1147,z2,z7,z4]),(0,[z6,z1,z2,z169,z7,z193]),(0,[z6,z1,z83,z60,z2,z36])],[(0,[z86,z1,z412,z2,z4,z5]),(0,[z41,z1,z2,z7,z4,z81])],[(0,[z6,z1,z2,z7,z4,z1148]),(0,[z6,z1,z2,z7,z4,z1149]),(0,[z1150,z1,z2,z7,z4,z5])],[(0,[z110,z6,z1,z137,z7,z4]),(0,[z6,z284,z2,z7,z4,z31]),(0,[z6,z1,z2,z7,z4,z1151])],[(0,[z17,z6,z1,z72,z7,z64]),(0,[z6,z39,z2,z63,z4,z13])],[(0,[z106,z48,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z1152]),(0,[z6,z1,z137,z7,z371,z4]),(0,[z381,z1,z2,z7,z4,z570]),(0,[z6,z1,z51,z2,z45,z85])],[(0,[z6,z1,z128,z101,z7,z4]),(0,[z6,z1,z2,z7,z4,z1153]),(0,[z6,z1,z1154,z2,z7,z5]),(0,[z6,z1,z798,z7,z4,z5])],[(0,[z34,z6,z1,z2,z7,z392]),(0,[z6,z1,z2,z38,z7,z193])],[(0,[z6,z1,z1155,z7,z4,z5])],[],[(0,[z6,z1,z2,z7,z4,z1156]),(0,[z6,z39,z2,z63,z4,z31])],[(0,[z1157,z6,z1,z2,z7,z4]),(0,[z6,z1,z185,z1144,z4,z5])],[(0,[z6,z1,z2,z7,z733,z5]),(0,[z410,z1,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z1158])],[],[(0,[z6,z1,z2,z7,z4,z1159])],[(0,[z6,z1,z2,z7,z4,z1160]),(0,[z6,z1,z1161,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z1162]),(0,[z6,z1,z2,z385,z7,z4]),(0,[z110,z6,z1,z2,z588,z4]),(0,[z6,z1,z2,z7,z4,z1163])]],
   [[(0,[z34,z6,z1,z137,z7,z4]),(0,[z6,z1,z2,z7,z4,z1164]),(0,[z6,z1,z2,z91,z748,z5])],[(0,[z6,z1,z2,z107,z4,z13]),(0,[z6,z1,z340,z2,z104,z5]),(0,[z6,z1,z340,z2,z92,z5]),(1,[z6,z2,z7,z852,z5]),(0,[z6,z1,z2,z7,z1165,z5])],[(0,[z6,z1,z2,z7,z4,z1166]),(0,[z6,z1,z2,z1167,z4,z5])],[(0,[z41,z1,z48,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z1168]),(0,[z6,z1,z340,z2,z4,z31]),(0,[z410,z1,z2,z7,z4,z218])],[],[(0,[z6,z1,z1169,z2,z7,z4]),(0,[z17,z1,z2,z7,z4,z514]),(0,[z6,z1,z101,z445,z7,z4]),(0,[z34,z1,z2,z335,z7,z4]),(0,[z19,z54,z20,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z1170])],[(0,[z34,z410,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z170,z399])],[(0,[z19,z6,z832,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z1171]),(0,[z6,z1,z2,z7,z4,z815])],[(0,[z6,z1,z2,z7,z4,z1172]),(0,[z6,z1,z1173,z2,z7,z4]),(0,[z6,z1,z2,z38,z4,z598])],[(0,[z6,z1174,z1,z2,z7,z4])],[(0,[z6,z1,z2,z7,z1175,z5]),(0,[z68,z195,z2,z7,z4,z5])],[(0,[z6,z1,z2,z7,z31,z45]),(0,[z6,z1,z2,z7,z1176,z5]),(0,[z6,z1,z2,z7,z4,z812]),(0,[z6,z1,z51,z2,z681,z4])],[(0,[z6,z1,z2,z1177,z4,z5]),(0,[z17,z6,z1,z255,z2,z7]),(0,[z6,z1,z2,z63,z181,z5])],[(0,[z6,z1,z2,z7,z4,z130]),(0,[z68,z750,z2,z7,z4,z5]),(0,[z17,z6,z1,z340,z2,z4]),(0,[z6,z1,z2,z169,z4,z85]),(0,[z6,z1,z2,z1144,z4,z5])],[],[(0,[z34,z6,z1,z2,z275,z4]),(0,[z6,z1,z1178,z2,z7,z4])]],
   [[],[(0,[z6,z1,z2,z7,z1179,z4]),(0,[z6,z1,z2,z7,z4,z1180]),(0,[z1,z2,z7,z4,z5,z1181])],[(0,[z6,z1,z1182,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z1183]),(0,[z1,z2,z7,z4,z1184,z5]),(0,[z6,z1,z7,z4,z5,z922]),(0,[z41,z6,z1,z1094,z7,z4])],[(0,[z17,z54,z1,z2,z7,z4]),(0,[z6,z1,z7,z845,z64,z5]),(0,[z6,z1,z7,z4,z59,z812])],[(0,[z6,z1,z2,z7,z1185,z5]),(0,[z1186,z6,z1,z2,z7,z4]),(0,[z6,z1,z1187,z7,z4,z5])],[(0,[z6,z1,z1188,z2,z7,z5])],[(0,[z6,z2,z7,z4,z249,z13]),(0,[z6,z1,z2,z89,z4,z401]),(0,[z19,z6,z20,z7,z471,z5]),(0,[z6,z1,z103,z7,z4,z948]),(0,[z6,z1,z52,z2,z7,z138])],[],[(0,[z6,z1,z52,z2,z7,z426]),(0,[z6,z1,z52,z2,z325,z7])],[(0,[z1189,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z1190]),(0,[z6,z625,z2,z7,z4,z31]),(0,[z6,z1,z2,z7,z4,z1191]),(0,[z6,z1,z208,z2,z4,z85]),(0,[z6,z1,z2,z7,z5,z815])],[(0,[z17,z6,z1,z2,z849,z7]),(0,[z6,z1,z1192,z2,z7,z4])],[(0,[z6,z1,z1193,z2,z7,z4])],[(0,[z6,z1,z18,z7,z4,z486]),(0,[z6,z1,z1194,z2,z7,z4]),(0,[z6,z1,z145,z1144,z4,z5])],[(0,[z6,z1,z2,z7,z4,z1195]),(0,[z17,z6,z1,z1196,z2,z7]),(0,[z6,z1,z2,z1197,z4,z5])],[(0,[z6,z1,z2,z7,z1198,z5]),(0,[z6,z1,z427,z137,z7,z4])],[(0,[z6,z1,z2,z28,z4,z13]),(0,[z6,z1,z2,z7,z4,z1199]),(0,[z34,z6,z1,z899,z7,z4]),(0,[z1200,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z1201,z5]),(0,[z6,z1,z2,z7,z4,z1202])]],
   [[(0,[z6,z1,z2,z7,z4,z1203])],[(0,[z6,z1,z2,z7,z4,z1204]),(0,[z6,z1,z2,z7,z30,z92]),(0,[z54,z1,z2,z7,z4,z401]),(0,[z6,z196,z2,z7,z104,z475])],[(0,[z6,z1,z2,z7,z300,z5]),(0,[z6,z1,z2,z7,z4,z1205]),(0,[z6,z1,z2,z7,z4,z1206]),(0,[z6,z1,z83,z2,z124,z5]),(0,[z6,z1,z1207,z7,z4,z5]),(0,[z1208,z6,z1,z2,z7,z4]),(0,[z6,z1,z83,z2,z36,z31]),(0,[z6,z1,z2,z7,z4,z1209])],[(0,[z6,z292,z2,z7,z4,z13]),(0,[z199,z1,z2,z7,z81,z5]),(0,[z6,z469,z2,z7,z4,z13])],[(0,[z6,z1,z477,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z1210]),(0,[z53,z1,z2,z603,z7,z5]),(0,[z17,z1,z359,z2,z7,z4])],[(0,[z6,z1,z2,z7,z4,z1211]),(0,[z17,z6,z1,z504,z7,z4]),(0,[z6,z369,z2,z63,z4,z5])],[],[(0,[z6,z1,z2,z7,z4,z1212]),(0,[z6,z1,z2,z1213,z4,z5]),(0,[z381,z1,z48,z2,z7,z4]),(0,[z17,z6,z1,z2,z7,z151]),(0,[z34,z1,z2,z7,z4,z365]),(0,[z6,z1,z2,z7,z78,z405])],[(0,[z17,z6,z1,z2,z91,z97]),(0,[z6,z1,z2,z588,z4,z58]),(0,[z34,z6,z1,z2,z7,z1090]),(0,[z6,z39,z2,z835,z4,z5])],[(0,[z6,z1,z427,z7,z4,z31]),(0,[z34,z6,z1,z2,z89,z4]),(0,[z6,z1,z2,z505,z4,z31])],[(0,[z6,z1214,z2,z7,z4,z5])],[(0,[z34,z6,z1,z2,z7,z300]),(0,[z6,z1,z2,z7,z4,z332]),(0,[z1215,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z38,z4,z58])],[(0,[z6,z1,z2,z7,z1216,z4]),(0,[z6,z1,z370,z2,z275,z4]),(0,[z17,z6,z1217,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z1218])],[(0,[z6,z1,z2,z1219,z4,z5]),(0,[z6,z1217,z2,z7,z4,z5])],[(0,[z17,z6,z1,z1125,z7,z4])],[(0,[z68,z129,z2,z7,z4,z31]),(0,[z6,z1,z1220,z7,z4,z5])]],
   [[(0,[z6,z1,z2,z1064,z4,z5]),(0,[z438,z1,z2,z7,z98,z5]),(0,[z17,z1,z137,z7,z4,z32])],[(0,[z6,z501,z2,z63,z4,z5]),(0,[z6,z1,z364,z2,z7,z193]),(0,[z6,z1,z2,z7,z193,z31]),(0,[z6,z1,z2,z7,z4,z510])],[(0,[z6,z1,z427,z7,z4,z12]),(0,[z349,z34,z1,z2,z7,z4]),(0,[z34,z6,z1,z2,z7,z181]),(0,[z6,z1,z2,z38,z257,z4])],[(0,[z6,z1,z103,z505,z4,z5]),(0,[z1,z2,z7,z795,z4,z5])],[(0,[z1221,z6,z1,z2,z7,z4]),(0,[z6,z1,z164,z2,z7,z31])],[(0,[z34,z6,z1,z2,z7,z4]),(0,[z1,z2,z719,z7,z4,z5]),(0,[z6,z1222,z1,z2,z7,z4]),(0,[z6,z1,z1223,z7,z4,z5])],[(0,[z6,z1,z1048,z7,z4,z5]),(0,[z142,z6,z1,z2,z7,z193]),(0,[z34,z157,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z1224,z5])],[(0,[z86,z6,z1,z255,z2,z5])],[(0,[z34,z1,z508,z2,z7,z4]),(0,[z1225,z6,z1,z2,z7,z4]),(0,[z6,z1,z1226,z2,z7,z4])],[(0,[z6,z1,z46,z7,z4,z5]),(0,[z6,z1,z2,z7,z4,z538]),(0,[z34,z6,z1,z164,z2,z7]),(0,[z410,z1,z20,z7,z4,z5]),(0,[z6,z1,z2,z7,z740,z13])],[(0,[z637,z1,z18,z7,z4,z5]),(0,[z670,z1,z2,z7,z81,z5]),(0,[z6,z1,z340,z2,z36,z5]),(0,[z54,z1,z2,z505,z4,z5])],[(0,[z6,z1,z1227,z7,z4,z5]),(0,[z6,z1,z1228,z2,z7,z4])],[(0,[z6,z1,z128,z7,z4,z166]),(0,[z6,z1,z1229,z2,z7,z70]),(0,[z6,z1,z105,z1144,z4,z5])],[(0,[z6,z1,z1230,z7,z4,z5]),(0,[z34,z6,z1,z2,z1231,z4])],[(0,[z106,z48,z2,z7,z4,z31])],[(0,[z6,z1,z1229,z2,z7,z5]),(0,[z6,z509,z2,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z1232])]],
   [[(0,[z6,z1,z1233,z2,z4,z5])],[(0,[z6,z1,z83,z2,z388,z5]),(0,[z6,z1,z2,z57,z4,z13]),(0,[z6,z1,z354,z7,z264,z13])],[(0,[z6,z331,z160,z7,z4,z5]),(0,[z0,z6,z1,z255,z2,z5]),(0,[z6,z1234,z2,z7,z4,z5]),(0,[z6,z1235,z1,z2,z7,z4]),(0,[z6,z1,z2,z4,z5,z927])],[(0,[z6,z1,z2,z1078,z4,z5])],[(0,[z6,z1,z2,z7,z392,z5]),(0,[z0,z1,z2,z3,z4,z13])],[(0,[z6,z1,z1236,z7,z4,z5]),(0,[z6,z1,z2,z7,z529,z5]),(0,[z410,z1,z2,z7,z4,z31])],[(0,[z6,z1,z103,z7,z4,z1014]),(0,[z6,z1,z2,z7,z4,z1237])],[(0,[z6,z1,z2,z890,z4,z5]),(0,[z6,z1,z2,z7,z4,z1238]),(0,[z6,z1,z21,z2,z7,z4]),(0,[z23,z1,z18,z7,z4,z248]),(0,[z6,z1,z164,z2,z38,z7])],[(0,[z199,z1,z340,z2,z81,z5]),(0,[z6,z1,z2,z7,z4,z1239])],[(0,[z6,z1,z2,z7,z1240,z5])],[(0,[z6,z1,z2,z107,z4,z31]),(0,[z6,z1,z796,z7,z4,z5]),(0,[z0,z1,z2,z3,z4,z31])],[(0,[z6,z1,z2,z107,z300,z5]),(0,[z6,z1,z2,z7,z1241,z5]),(0,[z6,z1,z364,z2,z7,z396]),(0,[z410,z1,z2,z89,z4,z5]),(0,[z6,z1,z2,z7,z4,z1242]),(0,[z6,z1,z2,z7,z13,z1031])],[(0,[z41,z1,z18,z2,z7,z4]),(0,[z6,z1,z427,z7,z4,z59]),(0,[z6,z1,z2,z7,z4,z1243]),(0,[z6,z1,z7,z4,z13,z1034])],[(0,[z6,z1,z2,z7,z1244,z5]),(0,[z86,z1,z2,z117,z529,z5]),(0,[z118,z6,z2,z7,z4,z31])],[(0,[z6,z1,z1245,z2,z7,z4]),(0,[z34,z6,z1,z2,z7,z944]),(0,[z1246,z6,z1,z2,z7,z4]),(0,[z1247,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z38,z4,z927])],[]],
   [[(0,[z6,z1,z2,z1231,z4,z5]),(0,[z6,z1,z2,z76,z7,z13]),(0,[z6,z1,z2,z975,z4,z5]),(0,[z1,z2,z7,z733,z4,z5]),(0,[z6,z1,z137,z7,z170,z4]),(0,[z142,z6,z1,z2,z7,z396])],[(0,[z17,z6,z1,z1207,z7,z4])],[(0,[z6,z1,z2,z1248,z4,z5]),(0,[z6,z1,z22,z7,z4,z486]),(0,[z6,z1,z370,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z1249]),(0,[z381,z6,z1,z2,z7,z804])],[(0,[z297,z6,z82,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z1250]),(0,[z86,z1,z2,z117,z548,z5])],[(0,[z17,z6,z1,z477,z7,z4]),(0,[z6,z1,z1016,z7,z4,z5]),(0,[z86,z1,z255,z2,z117,z5]),(0,[z17,z1,z74,z2,z7,z4]),(0,[z6,z1,z2,z7,z193,z59]),(0,[z6,z1,z2,z7,z471,z401])],[(0,[z6,z1,z103,z7,z4,z13]),(0,[z6,z1,z1251,z2,z7,z4])],[(0,[z6,z1,z2,z1252,z4,z5]),(0,[z19,z6,z20,z7,z498,z5]),(0,[z6,z1,z2,z57,z4,z619])],[(0,[z6,z1,z1036,z7,z4,z5]),(0,[z17,z566,z1,z2,z7,z4]),(0,[z6,z1,z164,z2,z7,z59])],[(0,[z68,z1,z477,z7,z4,z5]),(0,[z17,z334,z1,z2,z7,z4]),(0,[z17,z1,z2,z7,z4,z32]),(0,[z6,z1,z2,z4,z1253,z5])],[(0,[z41,z142,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z1254]),(0,[z6,z55,z403,z7,z4,z5]),(0,[z6,z1,z2,z7,z5,z1097])],[(0,[z1255,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z1256])],[(0,[z6,z1,z2,z7,z4,z1257]),(0,[z17,z272,z1,z2,z7,z4]),(0,[z1258,z6,z1,z2,z7,z4]),(0,[z1259,z1,z2,z7,z4,z5]),(0,[z6,z55,z832,z7,z4,z5])],[(0,[z1260,z6,z1,z2,z7,z4]),(0,[z54,z1,z2,z7,z4,z13])],[(0,[z6,z1,z52,z137,z7,z4]),(0,[z1,z2,z7,z4,z716,z32])],[(0,[z68,z129,z2,z7,z4,z130]),(0,[z34,z6,z1,z427,z7,z4]),(0,[z34,z6,z1,z2,z7,z498]),(0,[z34,z6,z196,z2,z7,z104]),(0,[z6,z1,z2,z7,z4,z224]),(0,[z6,z90,z2,z84,z4,z13]),(0,[z6,z1,z2,z4,z748,z5])],[(0,[z34,z6,z1,z62,z7,z4]),(0,[z615,z1,z2,z7,z81,z5]),(0,[z17,z6,z1214,z2,z7,z4]),(0,[z17,z6,z1234,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z40])]],
   [[(0,[z1,z741,z22,z7,z4,z5]),(0,[z199,z1,z2,z7,z426,z81]),(0,[z6,z1,z2,z7,z4,z1261])],[(0,[z6,z55,z160,z7,z4,z13])],[(0,[z34,z6,z1,z2,z107,z4]),(0,[z34,z6,z1,z2,z7,z529]),(0,[z6,z1,z2,z275,z4,z13])],[(0,[z34,z50,z1,z2,z7,z4]),(0,[z54,z1,z2,z7,z4,z218]),(0,[z6,z1,z2,z7,z4,z1262])],[(0,[z6,z1,z1263,z2,z7,z4]),(0,[z6,z1,z2,z7,z100,z399]),(0,[z6,z1,z14,z7,z4,z166])],[(0,[z0,z34,z1,z2,z3,z4]),(0,[z6,z1,z2,z7,z4,z1264]),(0,[z6,z1,z2,z7,z471,z5]),(0,[z6,z1,z2,z7,z4,z1265]),(0,[z6,z1,z1155,z7,z4,z13])],[(0,[z6,z1,z1266,z2,z7,z4]),(0,[z6,z1,z2,z426,z275,z4]),(0,[z6,z1,z1072,z2,z4,z13]),(0,[z6,z457,z2,z7,z4,z31])],[(0,[z34,z68,z129,z2,z7,z4]),(0,[z186,z6,z1,z2,z7,z193]),(0,[z6,z56,z2,z7,z287,z5]),(0,[z1267,z6,z1,z2,z7,z4])],[(0,[z6,z1,z2,z28,z4,z31]),(0,[z6,z1,z2,z7,z1268,z5]),(0,[z6,z1,z2,z275,z4,z31]),(0,[z6,z1,z2,z182,z4,z13])],[(0,[z297,z1,z2,z7,z4,z140])],[(0,[z6,z1,z340,z2,z529,z5]),(0,[z6,z1,z340,z370,z2,z4]),(0,[z6,z1,z132,z2,z7,z138])],[(0,[z6,z1,z2,z7,z1269,z5]),(0,[z6,z1,z2,z7,z193,z92])],[(0,[z6,z1,z82,z137,z7,z4]),(0,[z6,z580,z2,z84,z4,z5])],[(0,[z6,z1,z2,z7,z4,z9]),(0,[z6,z1,z2,z107,z392,z5])],[(0,[z6,z90,z103,z84,z4,z5])],[(0,[z6,z1,z2,z7,z1270,z4]),(0,[z34,z6,z1,z2,z7,z942]),(0,[z6,z1,z874,z7,z4,z5]),(0,[z6,z1,z2,z7,z1271,z5])]],
   [[(0,[z6,z1,z2,z1272,z4,z5]),(0,[z297,z381,z1,z2,z7,z4]),(0,[z17,z6,z1,z2,z182,z4]),(0,[z6,z1,z2,z7,z396,z13]),(0,[z6,z90,z2,z84,z4,z112])],[(0,[z6,z1,z1273,z2,z7,z5]),(0,[z6,z288,z2,z7,z4,z13]),(0,[z355,z6,z2,z7,z4,z31]),(0,[z6,z1,z2,z7,z4,z1274]),(0,[z6,z1,z72,z7,z64,z5])],[(0,[z17,z6,z1,z46,z7,z4]),(0,[z6,z1,z336,z145,z4,z5]),(0,[z17,z6,z1,z1035,z7,z4])],[(0,[z6,z1,z881,z7,z4,z5]),(0,[z6,z196,z2,z7,z852,z5]),(0,[z6,z1,z1275,z2,z7,z4])],[(0,[z6,z176,z2,z7,z4,z31]),(0,[z6,z1,z2,z1276,z7,z4])],[(0,[z6,z832,z20,z7,z4,z5])],[(0,[z6,z1,z1277,z7,z4,z5]),(0,[z6,z1,z1278,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z1279]),(0,[z6,z1,z2,z7,z396,z31]),(0,[z6,z1,z2,z7,z1280,z5])],[(0,[z17,z199,z1,z2,z7,z81]),(0,[z199,z1,z412,z2,z7,z5]),(0,[z6,z1,z1094,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z1281]),(0,[z6,z1,z354,z7,z264,z528])],[(0,[z297,z6,z1,z881,z7,z4]),(0,[z6,z55,z160,z7,z4,z131])],[(0,[z6,z1,z1282,z2,z7,z5]),(0,[z6,z1,z1283,z2,z7,z4]),(0,[z34,z6,z1,z997,z7,z4])],[(0,[z6,z1,z2,z1284,z4,z5]),(0,[z6,z1,z2,z7,z845,z5])],[(0,[z6,z1,z2,z7,z4,z1285]),(0,[z34,z6,z1,z2,z7,z1286]),(0,[z1287,z410,z1,z2,z7,z4]),(0,[z6,z39,z2,z63,z4,z40]),(0,[z6,z1,z2,z7,z4,z1288])],[(0,[z6,z1,z2,z7,z193,z396]),(0,[z1,z2,z7,z4,z5,z811])],[(0,[z1289,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z182,z4,z619])],[(0,[z75,z1,z128,z22,z7,z4]),(0,[z6,z1,z2,z7,z4,z1290]),(0,[z34,z6,z1,z354,z7,z264]),(0,[z6,z1,z51,z164,z2,z7])],[(0,[z68,z6,z82,z2,z7,z4]),(0,[z199,z1,z2,z7,z733,z5])]],
   [[(0,[z0,z1,z2,z719,z4,z5]),(0,[z1,z2,z7,z4,z13,z1181])],[(0,[z6,z1,z2,z7,z5,z1030]),(0,[z41,z6,z1,z874,z7,z4])],[(0,[z106,z48,z2,z7,z300,z5]),(0,[z6,z1,z2,z7,z1291,z5]),(0,[z6,z1,z2,z4,z927,z85])],[(0,[z6,z1,z504,z7,z4,z787])],[(0,[z106,z48,z477,z7,z4,z5]),(0,[z34,z6,z1,z2,z28,z4]),(0,[z6,z1,z1292,z2,z7,z4]),(0,[z1293,z1,z2,z7,z4,z5]),(0,[z6,z1,z1144,z146,z4,z5])],[(0,[z6,z1294,z2,z7,z4,z5]),(0,[z351,z34,z1,z2,z7,z4])],[(0,[z6,z1,z2,z7,z4,z1295]),(0,[z34,z6,z1,z2,z7,z548]),(0,[z17,z6,z55,z160,z7,z4]),(0,[z6,z1,z1296,z2,z7,z4])],[(0,[z6,z1,z2,z7,z4,z1297]),(0,[z17,z6,z1,z2,z76,z7]),(0,[z6,z1,z1196,z2,z7,z5])],[(0,[z6,z1,z2,z7,z4,z1298]),(0,[z6,z1,z2,z7,z1299,z5]),(0,[z34,z6,z1,z2,z7,z396]),(0,[z6,z1,z2,z57,z104,z5])],[(0,[z6,z1,z1300,z7,z4,z5])],[(0,[z6,z1,z2,z7,z4,z488]),(0,[z6,z1,z1301,z2,z7,z4]),(0,[z6,z1,z2,z7,z1302,z4]),(0,[z6,z1,z2,z7,z92,z187]),(0,[z582,z6,z1,z137,z7,z4]),(0,[z6,z1,z2,z1303,z4,z5]),(0,[z6,z1,z2,z57,z4,z31]),(0,[z6,z1,z354,z7,z264,z31])],[(0,[z6,z1,z504,z7,z4,z5]),(0,[z1304,z6,z1,z2,z7,z4])],[(0,[z6,z1,z2,z7,z4,z475])],[],[(0,[z6,z1,z2,z7,z548,z5]),(0,[z6,z1,z2,z7,z4,z745])],[(0,[z6,z1,z2,z7,z300,z13]),(0,[z6,z1,z1305,z2,z7,z4]),(0,[z6,z1,z2,z7,z1306,z5]),(0,[z6,z1,z1111,z7,z4,z31]),(0,[z6,z1,z2,z7,z92,z202])]],
   [[(0,[z6,z1,z477,z107,z4,z5]),(0,[z199,z1,z2,z7,z81,z13]),(0,[z33,z6,z364,z2,z7,z4]),(0,[z875,z54,z1,z2,z7,z4])],[(0,[z1,z2,z741,z7,z4,z5]),(0,[z6,z1307,z1,z2,z7,z4]),(0,[z34,z6,z1,z185,z146,z4]),(0,[z6,z1,z2,z7,z4,z1308])],[(0,[z6,z575,z2,z7,z4,z13]),(0,[z6,z1,z52,z2,z7,z187])],[(0,[z381,z1,z2,z7,z4,z183]),(0,[z1309,z1,z2,z7,z4,z5])],[(0,[z6,z1,z1310,z7,z4,z5]),(0,[z6,z1,z2,z89,z4,z13]),(0,[z6,z1,z2,z7,z498,z401]),(0,[z6,z1,z1311,z2,z7,z4]),(0,[z6,z1,z185,z146,z4,z5])],[(0,[z6,z1,z2,z7,z905,z5]),(0,[z6,z1,z2,z7,z4,z1312])],[(0,[z6,z1,z2,z7,z4,z1313]),(0,[z6,z1,z255,z2,z385,z7])],[],[(0,[z6,z1,z2,z7,z4,z1314]),(0,[z6,z411,z2,z7,z4,z31]),(0,[z6,z1,z52,z2,z7,z207])],[(0,[z106,z48,z46,z7,z4,z5]),(0,[z106,z48,z2,z7,z4,z538]),(0,[z6,z1,z62,z7,z4,z5]),(0,[z6,z1,z2,z76,z7,z31]),(0,[z17,z6,z1,z836,z7,z4]),(0,[z17,z6,z56,z2,z7,z287]),(0,[z6,z1,z2,z7,z5,z937]),(0,[z6,z1,z333,z7,z4,z13]),(0,[z6,z1,z2,z7,z4,z1315]),(1,[z6,z1,z7,z4,z812])],[(0,[z6,z1,z7,z4,z12,z166]),(0,[z6,z1,z2,z89,z4,z31]),(0,[z6,z1,z2,z7,z5,z45])],[(0,[z6,z1,z2,z1316,z4,z5]),(0,[z6,z1,z2,z7,z1286,z5]),(0,[z6,z1,z2,z7,z4,z1317]),(0,[z17,z347,z1,z2,z7,z4]),(0,[z17,z6,z1,z2,z505,z4]),(0,[z6,z1,z2,z89,z4,z218]),(1,[z6,z1,z1144,z4,z5])],[(0,[z34,z6,z1,z333,z7,z4]),(0,[z6,z1,z2,z91,z455,z5])],[(0,[z6,z1,z2,z7,z4,z1318]),(0,[z6,z2,z7,z1319,z4,z5]),(0,[z6,z590,z2,z7,z4,z13]),(0,[z6,z1,z60,z2,z7,z4])],[(0,[z6,z1,z103,z7,z4,z31]),(0,[z6,z1,z7,z4,z31,z887])],[(0,[z17,z34,z1,z137,z7,z4]),(0,[z142,z6,z446,z2,z7,z4]),(0,[z6,z446,z2,z7,z4,z13])]],
   [[(0,[z34,z6,z1,z2,z7,z471]),(0,[z6,z1,z2,z1320,z7,z4])],[(0,[z6,z1,z82,z2,z7,z4]),(0,[z6,z1,z2,z1321,z7,z5]),(0,[z6,z1,z2,z7,z4,z1322]),(0,[z1323,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z7,z4,z1324])],[(0,[z204,z1,z2,z3,z4,z5]),(0,[z34,z6,z1,z83,z2,z36]),(0,[z1325,z1,z2,z7,z4,z5]),(0,[z6,z1,z2,z7,z1326,z5]),(0,[z1150,z1,z2,z7,z4,z13]),(0,[z6,z1,z1327,z7,z4,z5])],[(0,[z6,z1,z2,z7,z865,z4]),(0,[z17,z1,z427,z7,z4,z32])],[(0,[z106,z48,z2,z7,z392,z5]),(1,[z1,z2,z719,z4,z5]),(0,[z6,z416,z2,z84,z4,z5]),(0,[z6,z1,z2,z7,z4,z1328]),(0,[z6,z1,z2,z7,z4,z1329])],[(0,[z6,z1,z46,z107,z4,z5]),(0,[z6,z1,z2,z107,z4,z538]),(0,[z54,z1,z2,z7,z4,z31]),(0,[z6,z1,z2,z7,z498,z5])],[(0,[z6,z1,z2,z7,z4,z1330]),(0,[z86,z1,z168,z2,z117,z4]),(0,[z6,z1,z1058,z2,z7,z31])],[(0,[z6,z90,z2,z84,z4,z31]),(0,[z6,z1,z2,z7,z4,z1331])],[(0,[z6,z669,z2,z7,z4,z13]),(0,[z6,z1,z340,z2,z97,z5])],[(0,[z17,z6,z1,z2,z7,z392]),(0,[z6,z1,z2,z7,z4,z248]),(0,[z6,z1,z2,z7,z1332,z5]),(0,[z6,z1,z83,z2,z681,z5]),(0,[z6,z1,z1333,z2,z7,z4])],[(0,[z6,z1334,z2,z7,z4,z5]),(0,[z34,z6,z90,z2,z84,z4]),(0,[z780,z410,z1,z2,z7,z4]),(0,[z19,z410,z20,z7,z4,z5]),(0,[z1287,z6,z1,z2,z7,z4]),(0,[z6,z1,z2,z1335,z4,z5])],[(0,[z54,z1,z2,z89,z4,z5]),(0,[z6,z1,z2,z97,z748,z5])],[(0,[z6,z1,z2,z28,z300,z5]),(0,[z6,z1,z2,z7,z170,z346]),(0,[z6,z1,z2,z7,z4,z1336])],[(0,[z6,z1,z2,z1337,z4,z5]),(0,[z6,z1,z2,z7,z4,z1338]),(0,[z199,z1,z2,z275,z81,z5])],[(0,[z6,z1,z477,z28,z4,z5]),(0,[z1339,z6,z1,z2,z7,z4])],[]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 512) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 512).take 509) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1021).take 365) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1386)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [512, 509, 365] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 172).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 172).take 166).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 338).take 174).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [172, 166, 174] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38691

theorem PEqualNP.Outside.L_meta_38691 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4241025224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4241025224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38691.solve