import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41488

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
  Nat.testBit (4276813032 * 2 ^ 32 + 4276791296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x04144436018556f1#64 ++ 0x00105110d806155b#64 ++ 0x0cf4447e038ffffe#64 ++ 0xec33d111f80e3fff#64 : BitVec 256),
   (0x11481d8b0cb3315a#64 ++ 0x044520762c32ccc5#64 ++ 0x33487f8f1cf331fd#64 ++ 0xb4cd21fe3c73ccc7#64 : BitVec 256),
   (0x428986d160dc3a1c#64 ++ 0x090a261b458370e8#64 ++ 0xc38f87f1e0fc3e3b#64 ++ 0xfb0e3e1fc783f0f8#64 : BitVec 256),
   (0xac0ee801b7002da0#64 ++ 0x12b03ba006dc00b6#64 ++ 0xfc0ff801ff003ff7#64 ++ 0xdff03fe007fc00ff#64 : BitVec 256),
   (0xfbe00000da6a8000#64 ++ 0x03ef80000369aa00#64 ++ 0xfff00001ffffc02f#64 ++ 0x9fffc00007ffff00#64 : BitVec 256),
   (0xfff7736c00000000#64 ++ 0x23ffddcdb0000000#64 ++ 0xfffffffe0000001f#64 ++ 0xe3fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.or, [6, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [10, 3]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [13, 4]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0cf4447e038ffffe 0xec33d111f80e3fff

def z1 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33487f8f1cf331fd 0xb4cd21fe3c73ccc7

def z2 : W := mkw 0x4281065000841210 0x010a041940021048 0xc38f87f0008c3e3b 0xeb0e3e1fc00230f8

def z3 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc38f87f1e0fc3e3b 0xfb0e3e1fc783f0f8

def z4 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfc0ff801ff003ff7 0xdff03fe007fc00ff

def z5 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xfff00001ffffc02f 0x9fffc00007ffff00

def z6 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xfffffffe0000001f 0xe3fffffff8000000

def z7 : W := mkw 0x00000412018556f1 0x000000104806155b 0x00000000038fffe0 0x0c000000000e3fff

def z8 : W := mkw 0xfbe3334800000000 0x23ef8ccd20000000 0xf30bbb8000000001 0x03cc2eee00000000

def z9 : W := mkw 0x428986d120943a1c 0x090a261b448250e8 0xc38f87f000003e1b 0xe30e3e1fc00000f8

def z10 : W := mkw 0x428986d360dd3a5c 0x090a261b4d8374e9 0xc3cfc7ffe0ff3fff 0xff0f3f1fff83fcff

def z11 : W := mkw 0xa80aa801b6002900 0x12a02aa006d800a4 0xf00bb801fc000001 0x13c02ee007f00000

def z12 : W := mkw 0xfffffb6db7002da0 0x33ffffedb6dc00b6 0xffffffffff003fff 0xfffffffffffc00ff

def z13 : W := mkw 0x428982c16058280c 0x090a260b058160a0 0xc38f87f1e070001b 0xf30e3e1fc781c000

def z14 : W := mkw 0x1140110800000000 0x0045004420000000 0x33487f8e0000001d 0xa0cd21fe38000000

def z15 : W := mkw 0xffff7fef0cb3315a 0x27fffdffbc32ccc5 0xffffffff1cf331ff 0xf7fffffffc73ccc7

def z16 : W := mkw 0xbd76712c9a228000 0x22f5d9c4b2688a00 0x3c70780e1f03c004 0x04f1c1e0387c0f00

def z17 : W := mkw 0xfff7736cda6a8000 0x23ffddcdb369aa00 0xffffffffffffc03f 0xffffffffffffff00

def z18 : W := mkw 0x4281024040480000 0x010a040901012000 0xc38f87f1e0fc003b 0xfb0e3e1fc783f000

def z19 : W := mkw 0x1140190a0c230142 0x0445006428308c05 0x3040780e1c0301c4 0x04c101e038700c07

def z20 : W := mkw 0x42818250604c0a04 0x090a060941813028 0xc0878070e00c0e02 0x4b021e01c3803038

def z21 : W := mkw 0x11489d8b2cb3395a 0x044522762cb2cce5 0xf34fff8ffcf33fff 0xffcd3ffe3ff3ccff

def z22 : W := mkw 0x0414443600855251 0x00105110d8021549 0x0cf4447e008fc01e 0xe033d111f8023f00

def z23 : W := mkw 0x0417736c00000000 0x20105dcdb0000000 0x000ffffe00000010 0x60003ffff8000000

def z24 : W := mkw 0xfff7777e018556f1 0x23ffddddf806155b 0xfffffffe038fffff 0xeffffffff80e3fff

def z25 : W := mkw 0x1554553e018556f1 0x00555154f806155b 0x3ffc7ffe038fffff 0xecfff1fff80e3fff

def z26 : W := mkw 0x0000049040dc121c 0x0800001241037048 0x0000000000fc0000 0x000000000003f000

def z27 : W := mkw 0x469dc6f761dd7efd 0x091a771bdd8775fb 0xcfffc7ffe3ffffff 0xff3fff1fff8fffff

def z28 : W := mkw 0x428982c16058280c 0x090a260b058160a0 0xc30b8381e0700001 0x130c2e0e0781c000

def z29 : W := mkw 0x53c99fdb6cff3b5e 0x0d4f267f6db3fced 0xf3cffffffcff3fff 0xffcf3ffffff3fcff

def z30 : W := mkw 0xac0ee801b6002900 0x12b03ba006d800a4 0xfc0ff801fc000017 0xd3f03fe007f00000

def z31 : W := mkw 0xac0efd8bb7913dfa 0x16b03bf62ede44f7 0xfc0fff8fff003ff7 0xfff03ffe3ffc00ff

def z32 : W := mkw 0x1140110800000000 0x0045004420000000 0x0340078e00000008 0x200d001e38000000

def z33 : W := mkw 0xac066000010004a0 0x02b0198000040012 0xfc0ff80003003ff7 0xcff03fe0000c00ff

def z34 : W := mkw 0x4695c67661cd5ef5 0x091a5719d987357b 0xccf7c47ee38ffffe 0xef33df11fb8e3fff

def z35 : W := mkw 0x0008800120002800 0x00002200048000a0 0x00000001e0003e20 0x18000000078000f8

def z36 : W := mkw 0xac066800970005a0 0x12b019a0025c0016 0xfc007801ff0001e7 0x9ff001e007fc0007

def z37 : W := mkw 0x0000041200851250 0x0000001048021449 0x00c4447e008f3ffe 0xec031111f8023cff

def z38 : W := mkw 0x041c5dbf059577fb 0x04107176fc1655df 0x0cfc7ffe038ffffe 0xec33f1fff80e3fff

def z39 : W := mkw 0x040ee80125002da0 0x10103ba0049400b6 0x300ff8011c003ff5 0xd4c03fe0047000ff

def z40 : W := mkw 0x0000001000040200 0x0000000040001008 0x00840070000c0e02 0x48021001c0003038

def z41 : W := mkw 0x00000412dbefd6f1 0x000000104b6fbf5b 0x00000001ffffffe0 0x1c00000007ffffff

def z42 : W := mkw 0x0008080104002100 0x0000202004100084 0x300878011c0031f5 0x94c021e0047000c7

def z43 : W := mkw 0x1140158a08b3105a 0x044500562822cc41 0x0340078e00f30008 0x200d001e3803cc00

def z44 : W := mkw 0x0001024000000000 0x0000040900000000 0x000f87f000000010 0x60003e1fc0000000

def z45 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x03487f8e00f331d8 0x200d21fe3803ccc7

def z46 : W := mkw 0xbd76792c970005a0 0x32f5d9e4b25c0016 0x3c70780e1f0001c4 0x04f1c1e0387c0007

def z47 : W := mkw 0x00080c830cb3315a 0x040020320c32ccc5 0x300878011cf331f5 0x94c021e00473ccc7

def z48 : W := mkw 0xea8986d1f2dc3a1c 0x0baa261b47cb70e8 0xff8f87f1fffc3e3f 0xfffe3e1fc7fff0f8

def z49 : W := mkw 0x041ccc37b7857ff1 0x10107330dede15ff 0x0cf4447fff8ffffe 0xfc33d111fffe3fff

def z50 : W := mkw 0x115015be08b7525b 0x04454056f822dd49 0x03f007fe00ffc008 0x200fc01ff803ff00

def z51 : W := mkw 0xfffeec37ffeffff1 0x13fffbb0dfffbfff 0xfffffc7fffffffff 0xfffffff1ffffffff

def z52 : W := mkw 0xfff7736c40480000 0x23ffddcdb1012000 0xffffffffe0fc003f 0xfbffffffff83f000

def z53 : W := mkw 0xeeb7626400000000 0x23badd8990000000 0xccf7c47e0000001e 0xe333df11f8000000

def z54 : W := mkw 0xeaa00000d2488000 0x03aa800003492200 0xccb00000e30cc002 0x0b32c000038c3300

def z55 : W := mkw 0x1140000008220000 0x0045000000208800 0x334000011cf3002d 0x94cd00000473cc00

def z56 : W := mkw 0xb96000009a228000 0x02e5800002688a00 0x300000001c000000 0x00c0000000700000

def z57 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0004447e00003fd0 0x60001111f80000ff

def z58 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xf3000001fc700001 0x13cc000007f1c000

def z59 : W := mkw 0x4280000040480000 0x010a000001012000 0xc0800000e00c0002 0x0b02000003803000

def z60 : W := mkw 0x0008080104002100 0x0000202004100084 0x00087800000031d0 0x000021e0000000c7

def z61 : W := mkw 0x53e00000486a8000 0x014f80000121aa00 0x03f0000000ffc008 0x000fc0000003ff00

def z62 : W := mkw 0xffeee801ff6aada0 0x13ffbba007fdaab6 0xfffff801ffffffff 0xdfffffe007ffffff

def z63 : W := mkw 0xac06600000000000 0x02b0198000000000 0xfc0ff80000000017 0xc3f03fe000000000

def z64 : W := mkw 0x04144034010446a1 0x00105100d004111a 0x0cb40070030cce02 0x4832d001c00c3338

def z65 : W := mkw 0xfbe81989de7aa10a 0x07efa0662779ea84 0xf3083b81fc700001 0x13cc20ee07f1c000

def z66 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x00f4447e008fffd8 0x6003d111f8023fff

def z67 : W := mkw 0x428186d060dc1a1c 0x090a061b41837068 0xc38787f0e0fc0e0a 0x6b0e1e1fc383f038

def z68 : W := mkw 0x0008849160dc3a1c 0x08002212458370e8 0x03080781e0fc3e39 0xb80c201e0783f0f8

def z69 : W := mkw 0xbd77736c00000000 0x22f5ddcdb0000000 0x3c7ffffe00000014 0x60f1fffff8000000

def z70 : W := mkw 0x4281024000000000 0x010a040900000000 0xc38f87f00000001b 0xe30e3e1fc0000000

def z71 : W := mkw 0xfbe10240da6a8000 0x03ef84090369aa00 0xffff87f1ffffc03f 0xfffffe1fc7ffff00

def z72 : W := mkw 0x0000040200811050 0x0000001008020441 0x0040440e008331fc 0xa401011038020cc7

def z73 : W := mkw 0x04144434018456b1 0x00105110d006115a 0x0cb40470038cfe3a 0xe832d011c00e33f8

def z74 : W := mkw 0x00080c830cb3315a 0x040020320c32ccc5 0x000000011cf331e0 0x140000000473ccc7

def z75 : W := mkw 0x00100436018556f1 0x00004010d806155b 0x00f0047e038fffe8 0x2c03c011f80e3fff

def z76 : W := mkw 0x114819890c32210a 0x044520662430c884 0x33083b811c700001 0x10cc20ee0471c000

def z77 : W := mkw 0x04144026010144e1 0x0010510098040513 0x0000400e000001c0 0x0000010038000007

def z78 : W := mkw 0x0008048100903018 0x00002012040240c0 0x0008078000003010 0x2000201e000000c0

def z79 : W := mkw 0xbd4efd8bbfb33dfa 0x16f53bf62efeccf7 0xff4fff8ffff33fff 0xfffd3ffe3fffccff

def z80 : W := mkw 0x00000412018556f1 0x000000104806155b 0x0040440e038ffffc 0xac010110380e3fff

def z81 : W := mkw 0xeebfe6f560dc3a1c 0x2bbaff9bd58370e8 0xcfbf87f1e0fc3e3b 0xfb3efe1fc783f0f8

def z82 : W := mkw 0x53e986d168feba1c 0x094fa61b45a3fae8 0xc3ff87f1e0fffe3b 0xfb0ffe1fc783fff8

def z83 : W := mkw 0x04144436dbefd6f1 0x00105110db6fbf5b 0x0cf4447ffffffffe 0xfc33d111ffffffff

def z84 : W := mkw 0x00000010010446a1 0x000000004004111a 0x00000000030cce00 0x08000000000c3338

def z85 : W := mkw 0xb96000009a228000 0x02e5800002688a00 0x3c7000001f03c004 0x04f1c000007c0f00

def z86 : W := mkw 0xbd76712c00000000 0x22f5d9c4b0000000 0x3c70780e00000004 0x00f1c1e038000000

def z87 : W := mkw 0xfbe88491fafeba1c 0x0befa21247ebfae8 0xfff00001fffffe2f 0x9fffc00007fffff8

def z88 : W := mkw 0x041eec3725857ff1 0x10107bb0dc9615ff 0x0cfffc7e038ffffe 0xec33fff1f80e3fff

def z89 : W := mkw 0x155c5dbf0db777fb 0x04557176fc36dddf 0x3ffc7fff1fffffff 0xfcfff1fffc7fffff

def z90 : W := mkw 0x42818250604c0a04 0x090a060941813028 0xc38f87f0e00c0e1b 0xeb0e3e1fc3803038

def z91 : W := mkw 0xea8baac1f658290c 0x1baa2eab07d960a4 0xf30bbb81fc700001 0x13cc2eee07f1c000

def z92 : W := mkw 0x4694443641cd56f1 0x011a5110d907355b 0xcff4447fe3ffffff 0xff3fd111ff8fffff

def z93 : W := mkw 0xfbe000009a228000 0x03ef800002688a00 0xfff000001f03c00f 0x87ffc000007c0f00

def z94 : W := mkw 0x11481d8bdefbb15a 0x044520762f7beec5 0x33487f8ffffff1fd 0xbccd21fe3fffffc7

def z95 : W := mkw 0xee8feac1f7582dac 0x1bba3fab07dd60b6 0xff0ffb81ff703ff7 0xdffc3fee07fdc0ff

def z96 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc30f87f1e0703e11 0x730c3e1fc781c0f8

def z97 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xfffffffe038fc03f 0xeffffffff80e3f00

def z98 : W := mkw 0x0414402400000000 0x0010510090000000 0x0cf4447e0000001e 0xe033d111f8000000

def z99 : W := mkw 0xfbe80801de6aa100 0x03efa0200779aa84 0xfff87801fffff1ff 0x9fffe1e007ffffc7

def z100 : W := mkw 0x00081d8b0491315a 0x040020762c1244c5 0x00087f8e000031d0 0x200021fe380000c7

def z101 : W := mkw 0x00000000486a8000 0x000000000121aa00 0x0000000000ffc000 0x000000000003ff00

def z102 : W := mkw 0xfbe81d8bdefbb15a 0x07efa0762f7beec5 0xfff87f8ffffff1ff 0xbfffe1fe3fffffc7

def z103 : W := mkw 0xfffff7fd60dc3a1c 0x2bffffdff58370e8 0xffffffffe0fc3e3f 0xfbffffffff83f0f8

def z104 : W := mkw 0x0000800020000800 0x0000020000800020 0xc0078000e0000e02 0x4b001e0003800038

def z105 : W := mkw 0xbd4ef909b7002da0 0x12f53be426dc00b6 0xff4fff8fff003fff 0xfffd3ffe3ffc00ff

def z106 : W := mkw 0x428982d1605c2a0c 0x090a260b458170a8 0xc38f83f1e07c0e03 0x5b0e3e0fc781f038

def z107 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x3ff87f8f1ffff1ff 0xbcffe1fe3c7fffc7

def z108 : W := mkw 0xb96000009a228000 0x02e5800002688a00 0xfc700001ff03c027 0x9ff1c00007fc0f00

def z109 : W := mkw 0x4280000040480000 0x010a000001012000 0xc3800001e0fc002b 0x9b0e00000783f000

def z110 : W := mkw 0xfffff7fd20943a1c 0x2bffffdff48250e8 0xfffffffe00003e1f 0xe3fffffff80000f8

def z111 : W := mkw 0x00088801b7002da0 0x1000222006dc00b6 0xc00f8001ff003ff3 0xdf003e0007fc00ff

def z112 : W := mkw 0x1148190904002100 0x0045206424100084 0x33487f8f1c0031fd 0xb4cd21fe3c7000c7

def z113 : W := mkw 0xfbe0000092000000 0x03ef800002480000 0xfff00001ff00002f 0x9fffc00007fc0000

def z114 : W := mkw 0x0000041000841210 0x0000001040021048 0x00000000008c3e20 0x08000000000230f8

def z115 : W := mkw 0xac066000930004a0 0x12b01980024c0012 0x0c00000003000000 0x00300000000c0000

def z116 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0cf4047e038fce0a 0x6833d011f80e3f38

def z117 : W := mkw 0x42a0000040488000 0x010a800001012200 0x00b00000000cc000 0x0002c00000003300

def z118 : W := mkw 0xfbe0158adafb905a 0x07ef80562b6bee41 0xfff0078fffffc02f 0xbfffc01e3fffff00

def z119 : W := mkw 0xeeb76676018556f1 0x23badd99d806155b 0xccf7c47e038ffffe 0xef33df11f80e3fff

def z120 : W := mkw 0x000986d120943a1c 0x0800261b448250e8 0x000f87f000003e10 0x60003e1fc00000f8

def z121 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0x3c007801ff003fe4 0x1cf001e007fc00ff

def z122 : W := mkw 0xfffffb6d25002da0 0x33ffffedb49400b6 0xfffffffe00003fdf 0xe3fffffff80000ff

def z123 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z124 : W := mkw 0xfff7736c010004a0 0x23ffddcdb0040012 0xfffffffe03003fff 0xeffffffff80c00ff

def z125 : W := mkw 0xa800000092000000 0x02a0000002480000 0xcc000000e3000002 0x0b300000038c0000

def z126 : W := mkw 0x04144026010144e1 0x0010510098040513 0x0cf0400e038fc1ee 0x8c33c100380e3f07

def z127 : W := mkw 0xfbf00436daefd251 0x03efc010db6bbf49 0xfff0047fffffc02f 0xbfffc011ffffff00

def z128 : W := mkw 0x0417736c00000000 0x20105dcdb0000000 0x0cfffffe0000001e 0xe033fffff8000000

def z129 : W := mkw 0xbd46790a9f2305e2 0x16f519e42a7c8c17 0x3c40780e1f0301c4 0x04f101e0387c0c07

def z130 : W := mkw 0x00088c936cff3b5e 0x0c0022324db3fced 0x00000001fcff3fe0 0x1c00000007f3fcff

def z131 : W := mkw 0x0008880125002da0 0x10002220049400b6 0x0000000000003fc0 0x00000000000000ff

def z132 : W := mkw 0x0008008100102008 0x0000200204004080 0x0308038100700001 0x100c200e0401c000

def z133 : W := mkw 0xfbf3336c00000000 0x23efcccdb0000000 0xf3fbbffe00000009 0x23cfeefff8000000

def z134 : W := mkw 0x428982c16058280c 0x090a260b058160a0 0xc30f8381e0703e33 0xdb0c3e0e0781c0f8

def z135 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xfff00001fc70000f 0x93ffc00007f1c000

def z136 : W := mkw 0x0008048100903018 0x00002012040240c0 0x0308078100f03039 0xb00c201e0403c0c0

def z137 : W := mkw 0x040ee80125002da0 0x10103ba0049400b6 0xc00ff801e0003ff3 0xdb003fe0078000ff

def z138 : W := mkw 0x4697736c00000000 0x211a5dcdb0000000 0xc38ffffe0000001b 0xe30e3ffff8000000

def z139 : W := mkw 0x155c5daf0db375fb 0x04557176bc36cdd7 0x3f787f8f1ff3f1fd 0xb4fde1fe3c7fcfc7

def z140 : W := mkw 0x0000110800000000 0x0000004420000000 0x00087f8e00000010 0x200021fe38000000

def z141 : W := mkw 0xac066800970005a0 0x12b019a0025c0016 0x3c0078001f0001c4 0x04f001e0007c0007

def z142 : W := mkw 0xee8feed1f7dc3fbc 0x1bba3fbb47df70fe 0xff8ffff1fffc3fff 0xfffe3fffc7fff0ff

def z143 : W := mkw 0xac1eec37b7857ff1 0x12b07bb0dede15ff 0xfcfffc7fff8fffff 0xfff3fff1fffe3fff

def z144 : W := mkw 0x0008849120943a1c 0x08002212448250e8 0x0000000000003e00 0x00000000000000f8

def z145 : W := mkw 0xfffffb6dff6aada0 0x33ffffedb7fdaab6 0xffffffffffffffff 0xffffffffffffffff

def z146 : W := mkw 0xfff7737c010446a1 0x23ffddcdf004111a 0xfffffffe030cce1f 0xebfffffff80c3338

def z147 : W := mkw 0xb960190a9e238142 0x06e580642a788e05 0x3c70780e1f03c1c4 0x04f1c1e0387c0f07

def z148 : W := mkw 0xac0ee80125002da0 0x12b03ba0049400b6 0xfc0ff80000003fd7 0xc3f03fe0000000ff

def z149 : W := mkw 0x0000040200811050 0x0000001008020441 0x0000440e000031d0 0x20000110380000c7

def z150 : W := mkw 0x0000000000000000 0x0000000000000000 0x0cf00000038fc02e 0x8c33c000000e3f00

def z151 : W := mkw 0x0008800120002800 0x00002200048000a0 0xc00f8001e0003e33 0xdb003e00078000f8

def z152 : W := mkw 0x4288849160dc3a1c 0x090a2212458370e8 0xc3800001e0fc3e2b 0x9b0e00000783f0f8

def z153 : W := mkw 0xac1ffb6db7002da0 0x32b07fedb6dc00b6 0xfc0fffffff003ff7 0xfff03ffffffc00ff

def z154 : W := mkw 0x0008080104002100 0x0000202004100084 0x000000011c0031e0 0x14000000047000c7

def z155 : W := mkw 0xb960000000000000 0x02e5800000000000 0x3c70000000000004 0x00f1c00000000000

def z156 : W := mkw 0x041ff7fd20943a1c 0x28107fdff48250e8 0x000ffffe00003e10 0x60003ffff80000f8

def z157 : W := mkw 0x53f997fd60dc3a1c 0x294fe65ff58370e8 0xc3ff87ffe0fc3e3b 0xfb0ffe1fff83f0f8

def z158 : W := mkw 0xfbebb7d960dc3a1c 0x2befaedf658370e8 0xf38fbff1e0fc3e3b 0xfbce3effc783f0f8

def z159 : W := mkw 0xac06e000b3000ca0 0x12b01b8002cc0032 0xcc078000e3000e02 0x4b301e00038c0038

def z160 : W := mkw 0x04044000010004a0 0x0010110000040012 0x0cf44000038ffffe 0xcc33d100000e3fff

def z161 : W := mkw 0x57f5577e018556f1 0x215fd55df806155b 0x0ff447fe038ffffe 0xec3fd11ff80e3fff

def z162 : W := mkw 0xbd7440269b23c4e1 0x02f5d1009a6c8f13 0x3c70400e1f03c1c4 0x04f1c100387c0f07

def z163 : W := mkw 0x000986d120943a1c 0x0800261b448250e8 0x008f87f0008c3e3a 0xe8023e1fc00230f8

def z164 : W := mkw 0x040ee80125002da0 0x10103ba0049400b6 0x0c0ff80003003ff6 0xcc303fe0000c00ff

def z165 : W := mkw 0x42898ed164dc3b1c 0x090a263b459370ec 0xf38ffff1fcfc3fff 0xffce3fffc7f3f0ff

def z166 : W := mkw 0xac166c36978557f1 0x12b059b0da5e155f 0x3cf47c7e1f8ffffe 0xecf3d1f1f87e3fff

def z167 : W := mkw 0xee8fea41b7002da0 0x13ba3fa906dc00b6 0xff8ffff1ff003fff 0xfffe3fffc7fc00ff

def z168 : W := mkw 0x000986d160dc3a1c 0x0800261b458370e8 0x000f87f1e0fc3e30 0x78003e1fc783f0f8

def z169 : W := mkw 0xac06600000000000 0x02b0198000000000 0x3c00780000000004 0x00f001e000000000

def z170 : W := mkw 0xffeefd8bfffbbdfa 0x17ffbbf62fffeef7 0xffffff8fffffffff 0xfffffffe3fffffff

def z171 : W := mkw 0x0000040200811050 0x0000001008020441 0x0cf0440e038ff1fe 0xac33c110380e3fc7

def z172 : W := mkw 0xfbe0000000000000 0x03ef800000000000 0xfff000000000000f 0x83ffc00000000000

def z173 : W := mkw 0x155f7fef0cb3315a 0x24557dffbc32ccc5 0x334fffff1cf331fd 0xf4cd3ffffc73ccc7

def z174 : W := mkw 0x0000040200811050 0x0000001008020441 0x0040040e00830008 0x2001001038020c00

def z175 : W := mkw 0xa80aa801b7002da0 0x12a02aa006dc00b6 0xf00bb801ff003fe1 0x1fc02ee007fc00ff

def z176 : W := mkw 0xac0feed1b7943fbc 0x1ab03fbb46de50fe 0xfc0ffff1ff003ff7 0xfff03fffc7fc00ff

def z177 : W := mkw 0xfbe81d8b0cb3315a 0x07efa0762c32ccc5 0xfff87f8f1cf331ff 0xb7ffe1fe3c73ccc7

def z178 : W := mkw 0x468feed165dc3fbc 0x191a3fbb459770fe 0xc38ffff1e0fc3ffb 0xfb0e3fffc783f0ff

def z179 : W := mkw 0x11481d9b0cb7335a 0x044520766c32dccd 0x33cc7fff1cff3fff 0xfccf31fffc73fcff

def z180 : W := mkw 0x0010043600855251 0x00004010d8021549 0x00f0047e008fc008 0x2003c011f8023f00

def z181 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xf30ffffe00000011 0x63cc3ffff8000000

def z182 : W := mkw 0x04144034010446a1 0x00105100d004111a 0x0cf4447e030cce1e 0xe833d111f80c3338

def z183 : W := mkw 0x040c4801050025a0 0x0010312004140096 0x3c0c78011f003ff7 0xdcf031e0047c00ff

def z184 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xf00ff801fc003fd1 0x53c03fe007f000ff

def z185 : W := mkw 0xbd7444369ba7d6f1 0x02f5d110da6e9f5b 0x3cf4447e1f8ffffe 0xecf3d111f87e3fff

def z186 : W := mkw 0xfff44436dbefd6f1 0x03ffd110db6fbf5b 0xfff4447fffffffff 0xffffd111ffffffff

def z187 : W := mkw 0x0417777e018556f1 0x20105dddf806155b 0x000ffffe00003fd0 0x60003ffff80000ff

def z188 : W := mkw 0x00080c830cb3315a 0x040020320c32ccc5 0x0040440f1cf331fc 0xb40101103c73ccc7

def z189 : W := mkw 0xac0e6801970025a0 0x12b039a0065c0096 0x3c0878011f0031f5 0x94f021e0047c00c7

def z190 : W := mkw 0x041c4c37058577f1 0x00107130dc1615df 0x3cfc7c7f1f8fffff 0xfcf3f1f1fc7e3fff

def z191 : W := mkw 0x53c81d8b4cfb315a 0x054f20762d33ecc5 0xf3c87f8ffcff31ff 0xbfcf21fe3ff3fcc7

def z192 : W := mkw 0x000808810c32210a 0x040020220430c884 0x000000011c700000 0x100000000471c000

def z193 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xf3000001ffffc021 0x1fcc000007ffff00

def z194 : W := mkw 0xa808080196002100 0x02a0202006580084 0xfc087801ff0031f7 0x9ff021e007fc00c7

def z195 : W := mkw 0x114808010c222100 0x0045202004308884 0x334878011cf331fd 0x94cd21e00473ccc7

def z196 : W := mkw 0xeeb76264d2488000 0x23badd8993492200 0xccb78070e30cc002 0x4b32de01c38c3300

def z197 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc38b87f1e0fc0009 0x330e2e1fc783f000

def z198 : W := mkw 0xfbe99fdbfeffbb5e 0x0fefa67f6ffbfeed 0xffffffffffffffff 0xffffffffffffffff

def z199 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0x3ff000001fffc00c 0x04ffc000007fff00

def z200 : W := mkw 0x1140040208a31050 0x0045001008228c41 0x3340440f1cf331fd 0xb4cd01103c73ccc7

def z201 : W := mkw 0xffcfffdbffff3ffe 0x1fff3fff6ffffcff 0xffcfffffffff3fff 0xffff3ffffffffcff

def z202 : W := mkw 0x0414443400841210 0x00105110d0021048 0x0cf4447e008c3e3e 0xe833d111f80230f8

def z203 : W := mkw 0xac066800970005a0 0x12b019a0025c0016 0xfc0ff8001f0001d7 0xc7f03fe0007c0007

def z204 : W := mkw 0x00000000da6a8000 0x000000000369aa00 0x00000001ffffc020 0x1c00000007ffff00

def z205 : W := mkw 0x0000041000841210 0x0000001040021048 0x00840470008c3e3a 0xe8021011c00230f8

def z206 : W := mkw 0x04144026010144e1 0x0010510098040513 0x0c70400e0303c1c4 0x0431c100380c0f07

def z207 : W := mkw 0xee9feef7f7dd7ffd 0x1bba7fbbdfdf75ff 0xffffffffffffffff 0xffffffffffffffff

def z208 : W := mkw 0x1554443609a756f1 0x00555110d8269d5b 0x3ff4447f1fffffff 0xfcffd111fc7fffff

def z209 : W := mkw 0xffe66800df6a85a0 0x13ff99a0037daa16 0xfff07801ffffc1ef 0x9fffc1e007ffff07

def z210 : W := mkw 0xfffff7ff61dd7efd 0x2bffffdffd8775fb 0xffffffffe3ffffff 0xffffffffff8fffff

def z211 : W := mkw 0xfff6712c00000000 0x23ffd9c4b0000000 0xfff0780e0000000f 0x83ffc1e038000000

def z212 : W := mkw 0x00088c83bfb33dfa 0x140022320efeccf7 0x00000001fff33fe0 0x1c00000007ffccff

def z213 : W := mkw 0x11401d8a0cb3115a 0x044500762832cc45 0x33407f8e1cf301cc 0x24cd01fe3873cc07

def z214 : W := mkw 0x0008849160dc3a1c 0x08002212458370e8 0x00000001e0fc3e20 0x180000000783f0f8

def z215 : W := mkw 0x0011136c00000000 0x2000444db0000000 0x000007fe00000000 0x2000001ff8000000

def z216 : W := mkw 0x428986c160d8381c 0x090a261b058360e0 0xc30b8781e0f03039 0xb30c2e1e0783c0c0

def z217 : W := mkw 0x000819890410210a 0x0400206624104084 0x00083b8000000000 0x000020ee00000000

def z218 : W := mkw 0xb94abd8bbeb3395a 0x16e52af62efacce5 0xf34bff8ffcf331fd 0xb7cd2ffe3ff3ccc7

def z219 : W := mkw 0xfbe3334800000000 0x23ef8ccd20000000 0xfffbbb800000000f 0x83ffeeee00000000

def z220 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0cf0447e038fc1cc 0x2433c111f80e3f07

def z221 : W := mkw 0xfff6712cda6a8000 0x23ffd9c4b369aa00 0xfff0780fffffc02f 0x9fffc1e03fffff00

def z222 : W := mkw 0xac06600092000000 0x02b0198002480000 0xfc0ff801ff000037 0xdff03fe007fc0000

def z223 : W := mkw 0xa802200000000000 0x02a0088000000000 0xf00bb80000000001 0x03c02ee000000000

def z224 : W := mkw 0xeeaee801f748ada0 0x13babba007dd22b6 0xfcbff801ff0cfff7 0xdff2ffe007fc33ff

def z225 : W := mkw 0xb9600000da6a8000 0x02e580000369aa00 0x3c700001ffffc024 0x1cf1c00007ffff00

def z226 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xffbfbbf000000003 0x43fefeefc0000000

def z227 : W := mkw 0xfbe33348da6a8000 0x23ef8ccd2369aa00 0xfffbbb81ffffc02f 0x9fffeeee07ffff00

def z228 : W := mkw 0x53e0158a48fb905a 0x054f80562923ee41 0x03f0078e00ffc008 0x200fc01e3803ff00

def z229 : W := mkw 0x428982c16058280c 0x090a260b058160a0 0xc38b8381e0fc002b 0x9b0e2e0e0783f000

def z230 : W := mkw 0xa820000092008000 0x02a0800002480200 0x0c3000000300c000 0x0030c000000c0300

def z231 : W := mkw 0x428106d040dc121c 0x090a041b41037048 0x038007f000fc0008 0x200e001fc003f000

def z232 : W := mkw 0xb96000009a228000 0x02e5800002688a00 0x3cf000001f8fc02e 0x8cf3c000007e3f00

def z233 : W := mkw 0x00080c8104903118 0x00002032041240c4 0x33087f811cf031fd 0xb4cc21fe0473c0c7

def z234 : W := mkw 0xeaa3224000000000 0x23aa8c8900000000 0xc003800000000000 0x03000e0000000000

def z235 : W := mkw 0xffe44000db6a84a0 0x03ff9100036daa12 0xfff44001ffffffff 0xdfffd10007ffffff

def z236 : W := mkw 0x04044410018416b0 0x001011104006105a 0x0c844470038c3ffe 0xec321111c00e30ff

def z237 : W := mkw 0x57f7736c00000000 0x215fddcdb0000000 0x03fffffe00000018 0x600ffffff8000000

def z238 : W := mkw 0xfbe982c1fa7aa80c 0x0befa60b07e9eaa0 0xfffb8381ffffc02f 0x9fffee0e07ffff00

def z239 : W := mkw 0x469ff7fd60dc3a1c 0x291a7fdff58370e8 0xc38fffffe0fc3e3b 0xfb0e3fffff83f0f8

def z240 : W := mkw 0x469dc6f761dd7efd 0x091a771bdd8775fb 0xc38fc7ffe0fc3ffb 0xfb0e3f1fff83f0ff

def z241 : W := mkw 0xac36602400000000 0x22b0d98090000000 0x0c30000000000000 0x0030c00000000000

def z242 : W := mkw 0xfffff3ed6058280c 0x2bffffcfb58160a0 0xffffffffe070001f 0xf3ffffffff81c000

def z243 : W := mkw 0xfff7736c486a8000 0x23ffddcdb121aa00 0xfffffffe00ffc01f 0xe3fffffff803ff00

def z244 : W := mkw 0xac1ee825b7002da0 0x12b07ba096dc00b6 0xfcfffc7fff003fff 0xfff3fff1fffc00ff

def z245 : W := mkw 0x42818250604c0a04 0x090a060941813028 0xc3878071e0fc0e2b 0xdb0e1e01c783f038

def z246 : W := mkw 0x00080c830491315a 0x040020320c1244c5 0x00000000000031c0 0x00000000000000c7

def z247 : W := mkw 0xb96000009a228000 0x02e5800002688a00 0x3f7000011ff3c02d 0x94fdc000047fcf00

def z248 : W := mkw 0x1140110a08230042 0x0445004428208c01 0x0040000e00030000 0x0001000038000c00

def z249 : W := mkw 0xbd76712c00000000 0x22f5d9c4b0000000 0x3f787f8e0000001d 0xa0fde1fe38000000

def z250 : W := mkw 0xeeb7626400000000 0x23badd8990000000 0xfcbff87000000017 0xc3f2ffe1c0000000

def z251 : W := mkw 0xfbe01108da6a8000 0x03ef80442369aa00 0xfff87f8fffffc03f 0xbfffe1fe3fffff00

def z252 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0x3c0ff8001f003fd4 0x44f03fe0007c00ff

def z253 : W := mkw 0x429986f760dd7a5d 0x090a661bdd8375e9 0xc3ff87ffe0fffe3b 0xfb0ffe1fff83fff8

def z254 : W := mkw 0x040cc801b7002da0 0x1010332006dc00b6 0x0c044001ff003ff6 0xdc30110007fc00ff

def z255 : W := mkw 0x00008000b3000ca0 0x1000020002cc0032 0x00000000e3000e00 0x08000000038c0038

def z256 : W := mkw 0x53f1136c00000000 0x214fc44db0000000 0x33f87ffe0000001d 0xa0cfe1fff8000000

def z257 : W := mkw 0xa8088001b2002800 0x02a0220006c800a0 0xfc0f8001ff003e37 0xdff03e0007fc00f8

def z258 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0x038f87f000fc3e18 0x600e3e1fc003f0f8

def z259 : W := mkw 0x0414402400000000 0x0010510090000000 0x0cf4447e038fc03e 0xec33d111f80e3f00

def z260 : W := mkw 0xbd76712c00000000 0x22f5d9c4b0000000 0x3cf47c7e0000001e 0xe0f3d1f1f8000000

def z261 : W := mkw 0x0000190a04010142 0x0400006428100405 0x0000780e000001c0 0x000001e038000007

def z262 : W := mkw 0xeaa00000da6a8000 0x03aa80000369aa00 0xccb00001ffffc022 0x1f32c00007ffff00

def z263 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0c70400e038fffe4 0x0c31c100380e3fff

def z264 : W := mkw 0x53e00000486a8000 0x014f80000121aa00 0x0ff0000003ffc02e 0x8c3fc000000fff00

def z265 : W := mkw 0x00000000da6a8000 0x000000000369aa00 0x0cf00001ffffc02e 0x9c33c00007ffff00

def z266 : W := mkw 0x1140000008220000 0x0045000000208800 0x304000001c030004 0x04c1000000700c00

def z267 : W := mkw 0x53f1136c00000000 0x214fc44db0000000 0xc3ff87fe0000001b 0xe30ffe1ff8000000

def z268 : W := mkw 0xfbe986d1fafeba1c 0x0befa61b47ebfae8 0xffff87f1fffffe3f 0xfffffe1fc7fffff8

def z269 : W := mkw 0x114011880832000a 0x044500462020c800 0x0300038000700000 0x000c000e0001c000

def z270 : W := mkw 0xb94000009a220000 0x02e5000002688800 0xff400001fff3002f 0x9ffd000007ffcc00

def z271 : W := mkw 0x000106d00094121c 0x0800041b40025048 0x000007f000000000 0x2000001fc0000000

def z272 : W := mkw 0x0000158a0091105a 0x0400005628024441 0x0000078e00000000 0x2000001e38000000

def z273 : W := mkw 0x0417626400000000 0x20105d8990000000 0x0007807000000000 0x40001e01c0000000

def z274 : W := mkw 0xa800000092000000 0x02a0000002480000 0xfc000001ff000027 0x9ff0000007fc0000

def z275 : W := mkw 0xfff7736c92000000 0x23ffddcdb2480000 0xffffffffff00003f 0xfffffffffffc0000

def z276 : W := mkw 0x53c99fcb6cfb395e 0x0d4f267f2db3ece5 0xf34bff8ffcf331fd 0xb7cd2ffe3ff3ccc7

def z277 : W := mkw 0x0008048100903018 0x00002012040240c0 0x0000000100f03020 0x100000000403c0c0

def z278 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc30b8381e0fc3e21 0x1b0c2e0e0783f0f8

def z279 : W := mkw 0x0000000092000000 0x0000000002480000 0x00000001ff000020 0x1c00000007fc0000

def z280 : W := mkw 0xbd4e7d8b0cb3315a 0x06f539f62c32ccc5 0xff4fff8f1cf331ff 0xf7fd3ffe3c73ccc7

def z281 : W := mkw 0xfbeaa801fe6aa900 0x13efaaa007f9aaa4 0xfffbb801ffffc02f 0x9fffeee007ffff00

def z282 : W := mkw 0xfbe80481dafab018 0x03efa012076beac0 0xfff80781fffff03f 0xbfffe01e07ffffc0

def z283 : W := mkw 0xbd76792e0c230142 0x26f5d9e4b8308c05 0x3c70780e1c0301c4 0x04f1c1e038700c07

def z284 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0084447e008c3ffa 0xe8021111f80230ff

def z285 : W := mkw 0xfff7f36cb3000ca0 0x33ffdfcdb2cc0032 0xfffffffee3000e1f 0xebfffffffb8c0038

def z286 : W := mkw 0xfbebb3c96058280c 0x2befaecf258160a0 0xf30bbb81e0700001 0x13cc2eee0781c000

def z287 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c7000000303c004 0x0431c000000c0f00

def z288 : W := mkw 0x53e81d8b4cfbb15a 0x054fa0762d33eec5 0x33f87f8f1cfff1fd 0xb4cfe1fe3c73ffc7

def z289 : W := mkw 0x1140158a08b3105a 0x044500562822cc41 0x0340478e00f331fc 0xa40d011e3803ccc7

def z290 : W := mkw 0xbd6668009f2285a0 0x12f599a0027c8a16 0x3c7078001f03c1c4 0x04f1c1e0007c0f07

def z291 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xfcf7f87e00000006 0x43f3dfe1f8000000

def z292 : W := mkw 0xbd76753e018556f1 0x22f5d9d4f806155b 0x3cf47c7e038ffffe 0xecf3d1f1f80e3fff

def z293 : W := mkw 0xa800000092000000 0x02a0000002480000 0xfcf00001ff8fc02f 0x9ff3c00007fe3f00

def z294 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x0340078f1cf331e8 0x340d001e3c73ccc7

def z295 : W := mkw 0x0000000000000000 0x0000000000000000 0x0cf000000000000e 0x8033c00000000000

def z296 : W := mkw 0x53f1177e00855251 0x214fc45df8021549 0x03f007fe008fc008 0x200fc01ff8023f00

def z297 : W := mkw 0xffeffb49b7002da0 0x33ffbfed26dc00b6 0xff0ffb81ff003ff7 0xdffc3fee07fc00ff

def z298 : W := mkw 0x000008020c230142 0x0400002008308c05 0x000000001c0301c0 0x0400000000700c07

def z299 : W := mkw 0x155c5daf0cb3315a 0x04557176bc32ccc5 0x3ffc7fff1cf331ff 0xf4fff1fffc73ccc7

def z300 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc08f87f0e00c3e12 0x6b023e1fc38030f8

def z301 : W := mkw 0xeeb7626400000000 0x23badd8990000000 0xccb7807000000002 0x4332de01c0000000

def z302 : W := mkw 0xfbe88001fa6aa800 0x03efa20007e9aaa0 0xffff8001fffffe3f 0xdffffe0007fffff8

def z303 : W := mkw 0x0000000000000000 0x0000000000000000 0x008404700000001a 0xe0021011c0000000

def z304 : W := mkw 0x53f1136c00000000 0x214fc44db0000000 0x03f007fe00000008 0x200fc01ff8000000

def z305 : W := mkw 0x42810250404c0204 0x090a040941013008 0x00800070000c0000 0x00020001c0003000

def z306 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xff7bfb8e00000005 0x03fdefee38000000

def z307 : W := mkw 0xfff7736c08220000 0x23ffddcdb0208800 0xffffffff1cf3003f 0xf7fffffffc73cc00

def z308 : W := mkw 0xfff77b6c970005a0 0x33ffddedb25c0016 0xfffffffe1f0001df 0xe7fffffff87c0007

def z309 : W := mkw 0xee8fe6d160dc3a1c 0x0bba3f9b458370e8 0xff8ffff1e0fc3e3f 0xfbfe3fffc783f0f8

def z310 : W := mkw 0x1140110800000000 0x0045004420000000 0x3040780e00000004 0x00c101e038000000

def z311 : W := mkw 0x4288048140d83018 0x010a2012050360c0 0xc3880781e0fc303b 0xbb0e201e0783f0c0

def z312 : W := mkw 0xac17736c00000000 0x22b05dcdb0000000 0xfc0ffffe00000017 0xe3f03ffff8000000

def z313 : W := mkw 0x041dc6f721957efd 0x0810771bdc8655fb 0x000fc7fe00003fd0 0x60003f1ff80000ff

def z314 : W := mkw 0x0001825020040a04 0x0800060940801028 0x0007807000000e00 0x40001e01c0000038

def z315 : W := mkw 0xee87e250f34c0ea4 0x1bba1f8943cd303a 0xcc878070e30c0e02 0x4b321e01c38c3038

def z316 : W := mkw 0xbd4ef989bf322daa 0x16f53be626fcc8b6 0xff0ffb81ff703ff7 0xdffc3fee07fdc0ff

def z317 : W := mkw 0xfbe81989de7aa10a 0x07efa0662779ea84 0xfff83b81ffffc02f 0x9fffe0ee07ffff00

def z318 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33087f8f1c7031d1 0x30cc21fe3c71c0c7

def z319 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfcfff801ff8fffff 0xdff3ffe007fe3fff

def z320 : W := mkw 0x469dc6f560dc3a1c 0x091a771bd58370e8 0xcfffc7ffe0fc3e3f 0xfb3fff1fff83f0f8

def z321 : W := mkw 0x0000000000000000 0x0000000000000000 0x3008780000000015 0x80c021e000000000

def z322 : W := mkw 0x42800000da6a8000 0x010a00000369aa00 0xc3800001ffffc02b 0x9f0e000007ffff00

def z323 : W := mkw 0xbd4ef90bbf232de2 0x16f53be42efc8cb7 0xfc4ff80fff033ff7 0xdff13fe03ffc0cff

def z324 : W := mkw 0xfbe88801ff6aada0 0x13efa22007fdaab6 0xfff00001ffffffef 0x9fffc00007ffffff

def z325 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0cb40070038fffe2 0x4c32d001c00e3fff

def z326 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xcc078001ff003fe2 0x5f301e0007fc00ff

def z327 : W := mkw 0x53e106d048fe921c 0x094f841b4123fa48 0x03f007f000ffc008 0x200fc01fc003ff00

def z328 : W := mkw 0x0008880124002900 0x00002220049000a4 0xf00ff801fc003ff7 0xdfc03fe007f000ff

def z329 : W := mkw 0xeaa18250f24c8a04 0x0baa860943c93228 0xccb78070e30cce02 0x4b32de01c38c3338

def z330 : W := mkw 0x04044412018556f1 0x001011104806155b 0x0c044000038ffff6 0xcc301100000e3fff

def z331 : W := mkw 0xa8088801b7002da0 0x12a0222006dc00b6 0xfc000001ff003fe7 0x9ff0000007fc00ff

def z332 : W := mkw 0x0010002600014041 0x0000400098000501 0x0070000e0003c000 0x0001c00038000f00

def z333 : W := mkw 0xac166826970145e1 0x12b059a09a5c0517 0x3c70780e1f03c1c4 0x04f1c1e0387c0f07

def z334 : W := mkw 0xfbe0000000000000 0x03ef800000000000 0xf300000000000001 0x03cc000000000000

def z335 : W := mkw 0xac06e800b7000da0 0x12b01ba002dc0036 0xfc07f800ff000fc6 0x4ff01fe003fc003f

def z336 : W := mkw 0xac06e000b3000ca0 0x12b01b8002cc0032 0xfc078001ff000e27 0xdff01e0007fc0038

def z337 : W := mkw 0x00000800970005a0 0x10000020025c0016 0x000000001f0001c0 0x04000000007c0007

def z338 : W := mkw 0x00088801b7002da0 0x1000222006dc00b6 0x00000001ff003fe0 0x1c00000007fc00ff

def z339 : W := mkw 0xeaa00000d2488000 0x03aa800003492200 0xc0000000e0000000 0x0300000003800000

def z340 : W := mkw 0x00088c13b7857ff1 0x100022304ede15ff 0x00000001ff8fffe0 0x1c00000007fe3fff

def z341 : W := mkw 0x53c1134800000000 0x014f044d20000000 0xf3cffffe0000001f 0xe3cf3ffff8000000

def z342 : W := mkw 0xfbeb3bc90c32210a 0x27efacef2430c884 0xf30bbb811c700001 0x13cc2eee0471c000

def z343 : W := mkw 0x469546f641dd56fd 0x091a551bd907755b 0x0ff447fe03fffffe 0xec3fd11ff80fffff

def z344 : W := mkw 0xfffff7fdfafeba1c 0x2bffffdff7ebfae8 0xfffffffffffffe3f 0xfffffffffffffff8

def z345 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x3040780f1cf331e4 0x14c101e03c73ccc7

def z346 : W := mkw 0x1140150a00811050 0x0045005428020441 0x33487f8e008331fd 0xa4cd21fe38020cc7

def z347 : W := mkw 0x4281024000000000 0x010a040900000000 0xc087807000000002 0x43021e01c0000000

def z348 : W := mkw 0x15545d3e0da757f3 0x04555174f8369d5f 0x3cf47c7e1f8ffffe 0xecf3d1f1f87e3fff

def z349 : W := mkw 0x53c997db68ff3a5e 0x0d4f265f6da3fce9 0xc3cf87ffe0ff3e3b 0xfb0f3e1fff83fcf8

def z350 : W := mkw 0x0000040000801010 0x0000001000020040 0x0000040000803038 0xa0000010000200c0

def z351 : W := mkw 0x11401d0a0ca31152 0x0445007428328c45 0x30407c0e1c8331fc 0xa4c101f038720cc7

def z352 : W := mkw 0x0008848120903818 0x00002212048240e0 0xc30f8781e0f03e3b 0xfb0c3e1e0783c0f8

def z353 : W := mkw 0x1140000000000000 0x0045000000000000 0x334000000000000d 0x80cd000000000000

def z354 : W := mkw 0x041cc4b761dd7efd 0x08107312dd8775fb 0x0cf4447fe3fffffe 0xfc33d111ff8fffff

def z355 : W := mkw 0xa8000000da6a8000 0x02a000000369aa00 0xfc000001ffffc027 0x9ff0000007ffff00

def z356 : W := mkw 0x154c5d8b0db335fa 0x045531762c36ccd7 0x3f4c7f8f1ff33fff 0xfcfd31fe3c7fccff

def z357 : W := mkw 0xeeb7736c00000000 0x23baddcdb0000000 0xccbffffe00000012 0x6332fffff8000000

def z358 : W := mkw 0x00080c83defbb15a 0x040020320f7beec5 0x00000001fffff1e0 0x1c00000007ffffc7

def z359 : W := mkw 0xee8ee801f7482da0 0x13ba3ba007dd20b6 0xff8ff801fffc3fff 0xdffe3fe007fff0ff

def z360 : W := mkw 0x1148048108b23018 0x004520120422c8c0 0x334807811cf3303d 0xb4cd201e0473ccc0

def z361 : W := mkw 0x4288800160482800 0x010a2200058120a0 0xc38f8001e0fc3e3b 0xdb0e3e000783f0f8

def z362 : W := mkw 0xac0ee801ff6aada0 0x12b03ba007fdaab6 0xfc0ff801fffffff7 0xdff03fe007ffffff

def z363 : W := mkw 0x00000002010144e1 0x0000000008040513 0x000000000303c1c0 0x04000000000c0f07

def z364 : W := mkw 0xfff77b6e0c230142 0x27ffddedb8308c05 0xfffffffe1c0301df 0xe7fffffff8700c07

def z365 : W := mkw 0x53c986d168fe3a1c 0x094f261b45a3f8e8 0xf3cf87f1fcff3e3f 0xffcf3e1fc7f3fcf8

def z366 : W := mkw 0xb9481d8b9eb3315a 0x06e520762e7accc5 0xff487f8ffff331ff 0xbffd21fe3fffccc7

def z367 : W := mkw 0x04044000010004a0 0x0010110000040012 0x0c04400003003ff6 0xcc301100000c00ff

def z368 : W := mkw 0x11400000da6a8000 0x004500000369aa00 0x33400001ffffc02d 0x9ccd000007ffff00

def z369 : W := mkw 0xac06600000000000 0x02b0198000000000 0xcc07800000000002 0x43301e0000000000

def z370 : W := mkw 0xac0eec91f7dc3fbc 0x1ab03bb247df70fe 0xfc0ff801fffc3ff7 0xdff03fe007fff0ff

def z371 : W := mkw 0xeea6e000f3488ca0 0x13ba9b8003cd2232 0xccb78000e30cce02 0x4b32de00038c3338

def z372 : W := mkw 0x0000000000000000 0x0000000000000000 0x0cb00000030cc002 0x0832c000000c3300

def z373 : W := mkw 0x000aa80124002900 0x10002aa0049000a4 0x000bb80000000000 0x00002ee000000000

def z374 : W := mkw 0x46954676018556f1 0x011a5519d806155b 0xcfffc7fe038fffff 0xef3fff1ff80e3fff

def z375 : W := mkw 0xa800000000000000 0x02a0000000000000 0xfc00000000000007 0x83f0000000000000

def z376 : W := mkw 0xffe6600000000000 0x03ff998000000000 0xfffff8000000001f 0xc3ffffe000000000

def z377 : W := mkw 0x0406600000000000 0x0010198000000000 0x000ff80000000010 0x40003fe000000000

def z378 : W := mkw 0xac0eec03b7813df0 0x12b03bb00ede04f7 0xfc4ffc0fff833fff 0xfff13ff03ffe0cff

def z379 : W := mkw 0x1140000008220000 0x0045000000208800 0x330000011c700001 0x10cc00000471c000

def z380 : W := mkw 0x040ee80125002da0 0x10103ba0049400b6 0x000ff80000003fd0 0x40003fe0000000ff

def z381 : W := mkw 0xfffff36d20002800 0x23ffffcdb48000a0 0xffffffffe0003e3f 0xfbffffffff8000f8

def z382 : W := mkw 0x0000040200811050 0x0000001008020441 0x00000000008331e0 0x0400000000020cc7

def z383 : W := mkw 0x53f117fc40dc121c 0x294fc45ff1037048 0x03f007fe00fc0008 0x200fc01ff803f000

def z384 : W := mkw 0xffe66000da6a8000 0x03ff99800369aa00 0xfffff801ffffc03f 0xdfffffe007ffff00

def z385 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfc0fb801ff000e03 0x5bf03ee007fc0038

def z386 : W := mkw 0x0000000000000000 0x0000000000000000 0x0300000100f00029 0x900c00000403c000

def z387 : W := mkw 0x4281024000000000 0x010a040900000000 0xc30b838000000001 0x030c2e0e00000000

def z388 : W := mkw 0x0000000000000000 0x0000000000000000 0x300000011c000025 0x94c0000004700000

def z389 : W := mkw 0x0008849160dc3a1c 0x08002212458370e8 0x00840471e0fc3e3a 0xf8021011c783f0f8

def z390 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0044447e00833ffc 0xe4011111f8020cff

def z391 : W := mkw 0x04144034010446a1 0x00105100d004111a 0x0004007000000e00 0x40001001c0000038

def z392 : W := mkw 0x000000009a228000 0x0000000002688a00 0x000000001f03c000 0x04000000007c0f00

def z393 : W := mkw 0x428106d040dc121c 0x090a041b41037048 0xc38007f1e0fc002b 0xbb0e001fc783f000

def z394 : W := mkw 0xb962310800000000 0x22e588c420000000 0x3000380000000000 0x00c000e000000000

def z395 : W := mkw 0x00080c0304813150 0x000020300c1204c5 0x30487c0f1c8331fd 0xb4c121f03c720cc7

def z396 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x30487f8e1c0331d4 0x24c121fe38700cc7

def z397 : W := mkw 0x040cc00121002ca0 0x00103300048400b2 0xcc0fc001e3003ff7 0xdf303f00078c00ff

def z398 : W := mkw 0x42898ed36cff3b5e 0x0d0a263b4db3fced 0xc38f87f1fcff3ffb 0xff0e3e1fc7f3fcff

def z399 : W := mkw 0xfbe106d0dafe921c 0x0bef841b436bfa48 0xfff007f1ffffc02f 0xbfffc01fc7ffff00

def z400 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xf3f00001fcffc009 0x13cfc00007f3ff00

def z401 : W := mkw 0x0010043600855251 0x00004010d8021549 0x0000047e00000000 0x20000011f8000000

def z402 : W := mkw 0xffff7b6d04002100 0x23fffdedb4100084 0xffffffff1c0031ff 0xf7fffffffc7000c7

def z403 : W := mkw 0x155455be09b756fb 0x04555156f826dd5b 0x0ff447fe03fffffe 0xec3fd11ff80fffff

def z404 : W := mkw 0x041f7fef0491315a 0x24107dffbc1244c5 0x000ffffe000031d0 0x60003ffff80000c7

def z405 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xffb00001ff7cc003 0x1bfec00007fdf300

def z406 : W := mkw 0xfff7776e00811050 0x23ffddddb8020441 0xfffffffe008331ff 0xe7fffffff8020cc7

def z407 : W := mkw 0x57f5536c00000000 0x215fd54db0000000 0x0ff447fe0000001e 0xe03fd11ff8000000

def z408 : W := mkw 0x00000000da6a8000 0x000000000369aa00 0x00000001fc700000 0x1000000007f1c000

def z409 : W := mkw 0x11481d9b0db777fb 0x044520766c36dddf 0x33487f8f1ffffffd 0xbccd21fe3c7fffff

def z410 : W := mkw 0x53f1136c486a8000 0x214fc44db121aa00 0x03f007fe00ffc008 0x200fc01ff803ff00

def z411 : W := mkw 0xbd5efdbfbfb77ffb 0x16f57bf6fefeddff 0xffffffffffffffff 0xffffffffffffffff

def z412 : W := mkw 0xa80aa801b6002900 0x12a02aa006d800a4 0xf00fb801fc003e33 0xdbc03ee007f000f8

def z413 : W := mkw 0x04144036010546e1 0x00105100d804151b 0x0cf4407e030fcfc6 0x4c33d101f80c3f3f

def z414 : W := mkw 0xeaa00000d2488000 0x03aa800003492200 0xfcb00001ff0cc027 0x9ff2c00007fc3300

def z415 : W := mkw 0xeaa0000000000000 0x03aa800000000000 0xccb0000000000002 0x0332c00000000000

def z416 : W := mkw 0x1148158900903018 0x00452056240240c0 0x33487f8f00f0303d 0xb0cd21fe3c03c0c0

def z417 : W := mkw 0x0406e00021000ca0 0x10101b8000840032 0x0007800000000e00 0x40001e0000000038

def z418 : W := mkw 0xffff7fff0db777fb 0x27fffdfffc36dddf 0xffffffff1fffffff 0xfffffffffc7fffff

def z419 : W := mkw 0x00088c91f7dc3fbc 0x1800223247df70fe 0x00000001fffc3fe0 0x1c00000007fff0ff

def z420 : W := mkw 0x11489d9b6cff3b5e 0x0c4522766db3fced 0x33487f8ffcff3ffd 0xbccd21fe3ff3fcff

def z421 : W := mkw 0xac0eec11b7843fb0 0x12b03bb046de10fe 0xfc8ffc71ff8c3fff 0xfff23ff1c7fe30ff

def z422 : W := mkw 0x00099fdb24953b5e 0x0c00267f6c9254ed 0x000ffffe00003fd0 0x60003ffff80000ff

def z423 : W := mkw 0x42898251604c2a04 0x090a2609458130a8 0xc08f8071e00c3e33 0xdb023e01c78030f8

def z424 : W := mkw 0x53e00000486a8000 0x014f80000121aa00 0xc3f00001e0ffc02b 0x9b0fc0000783ff00

def z425 : W := mkw 0x4695426400000000 0x011a550990000000 0xcfffc7fe0000001f 0xe33fff1ff8000000

def z426 : W := mkw 0x0008841120843a10 0x00002210448210e8 0xc08f8471e08c3e3b 0xfb023e11c78230f8

def z427 : W := mkw 0xfff7777e00855251 0x23ffddddf8021549 0xfffffffe008fc01f 0xe3fffffff8023f00

def z428 : W := mkw 0xeeb76274010446a1 0x23badd89d004111a 0xccb78070030cce02 0x4b32de01c00c3338

def z429 : W := mkw 0x0010002400000000 0x0000400090000000 0x00f0047e00000008 0x2003c011f8000000

def z430 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xcfff87f1e3fffe3f 0xff3ffe1fc78ffff8

def z431 : W := mkw 0x53c91fcb0cb3315a 0x054f247f2c32ccc5 0xf3cfffff1cf331ff 0xf7cf3ffffc73ccc7

def z432 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040440e0000001c 0xa001011038000000

def z433 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xf3800001fcfc002b 0x9bce000007f3f000

def z434 : W := mkw 0xeeb44436d3cdd6f1 0x03bad110db4f375b 0xccf4447ee38ffffe 0xef33d111fb8e3fff

def z435 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc0878071e0fc3e22 0x5b021e01c783f0f8

def z436 : W := mkw 0x0000041000841210 0x0000001040021048 0x0004047000003e10 0x60001011c00000f8

def z437 : W := mkw 0x114819890c32210a 0x044520662430c884 0x33487f8f1c70001d 0xb0cd21fe3c71c000

def z438 : W := mkw 0xac0e680104002100 0x02b039a004100084 0xfc0ff8011c0031f7 0xd7f03fe0047000c7

def z439 : W := mkw 0xfffc5dbfdffff7fb 0x07fff176ff7fffdf 0xfffc7fffffffffff 0xfffff1ffffffffff

def z440 : W := mkw 0xfff7777e018556f1 0x23ffddddf806155b 0xfffffffe00003fdf 0xe3fffffff80000ff

def z441 : W := mkw 0xfbe986d1fafeba1c 0x0befa61b47ebfae8 0xf38f87f1fcfc3e3b 0xfbce3e1fc7f3f0f8

def z442 : W := mkw 0xeaa00000d2488000 0x03aa800003492200 0xcfb00001e3fcc02b 0x9b3ec000078ff300

def z443 : W := mkw 0x0008849361dd7efd 0x080022124d8775fb 0x00000001e3ffffe0 0x1c000000078fffff

def z444 : W := mkw 0xffe7734800000000 0x23ff9dcd20000000 0xff0ffb8000000017 0xc3fc3fee00000000

def z445 : W := mkw 0xffeee801ff6aada0 0x13ffbba007fdaab6 0xff0ff801ff703ff7 0xdffc3fe007fdc0ff

def z446 : W := mkw 0xfbeb3fcb0cb3315a 0x27efacff2c32ccc5 0xf34bff8f1cf331fd 0xb7cd2ffe3c73ccc7

def z447 : W := mkw 0xeeb7626400000000 0x23badd8990000000 0xcfbf87f00000001b 0xe33efe1fc0000000

def z448 : W := mkw 0x1557736c00000000 0x20555dcdb0000000 0x334ffffe0000001d 0xe0cd3ffff8000000

def z449 : W := mkw 0x0417777e018556f1 0x20105dddf806155b 0x0cfffffe038ffffe 0xec33fffff80e3fff

def z450 : W := mkw 0xffff7bed0c32210a 0x27fffdefb430c884 0xffffffff1c70001f 0xf3fffffffc71c000

def z451 : W := mkw 0x428106d040dc121c 0x090a041b41037048 0x038407f000fc3e3a 0xe80e101fc003f0f8

def z452 : W := mkw 0xfff777ee08b3105a 0x27ffdddfb822cc41 0xfffffffe00f3001f 0xe3fffffff803cc00

def z453 : W := mkw 0x154efd8b2db33dfa 0x14553bf62cb6ccf7 0x334fff8f1cf33ffd 0xf4cd3ffe3c73ccff

def z454 : W := mkw 0x0414442600811050 0x0010511098020441 0x0cf4447e008331fe 0xe433d111f8020cc7

def z455 : W := mkw 0x0416712c00000000 0x201059c4b0000000 0x0000780e00000000 0x000001e038000000

def z456 : W := mkw 0x0000000200010040 0x0000000008000401 0x0040400e000301c4 0x0401010038000c07

def z457 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0004447e038ffff0 0x6c001111f80e3fff

def z458 : W := mkw 0xbd76712e010144e1 0x22f5d9c4b8040513 0x3c70780e0303c1c4 0x04f1c1e0380c0f07

def z459 : W := mkw 0xfbe0110800000000 0x03ef804420000000 0xfff87f8e0000001f 0xa3ffe1fe38000000

def z460 : W := mkw 0xeeb7e274604c0a04 0x2bbadf89d1813028 0xccb78070e00c0e02 0x4b32de01c3803038

def z461 : W := mkw 0x00088801ff6aada0 0x1000222007fdaab6 0x00000001ffffffe0 0x1c00000007ffffff

def z462 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c00000003000026 0x8c300000000c0000

def z463 : W := mkw 0xfbe0000000000000 0x03ef800000000000 0xfff00000038fc02f 0x8fffc000000e3f00

def z464 : W := mkw 0xfbebbb49b6002900 0x33efaeed26d800a4 0xf30bbb81fc000001 0x13cc2eee07f00000

def z465 : W := mkw 0xfbe00410daee9210 0x03ef8010436bba48 0xfff40471fffffe3f 0xffffd011c7fffff8

def z466 : W := mkw 0xfff7f37c604c0a04 0x2bffdfcdf1813028 0xfffffffee00c0e1f 0xebfffffffb803038

def z467 : W := mkw 0x11499fdb2cb73b5e 0x0c45267f6cb2dced 0x334fffff1cf33ffd 0xf4cd3ffffc73ccff

def z468 : W := mkw 0x00088491fafeba1c 0x0800221247ebfae8 0x00000001fffffe20 0x1c00000007fffff8

def z469 : W := mkw 0xbd7ef92db7002da0 0x32f5fbe4b6dc00b6 0xfc7ff80fff003ff7 0xdff1ffe03ffc00ff

def z470 : W := mkw 0xfbe00402daeb9050 0x03ef80100b6bae41 0xfff0440ffffff1ff 0xbfffc1103fffffc7

def z471 : W := mkw 0x1554592e0d2345e3 0x04555164b8348d17 0x3c70780e1f03c1c4 0x04f1c1e0387c0f07

def z472 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xf3400001fcf3002d 0x97cd000007f3cc00

def z473 : W := mkw 0x429106f640dd525d 0x090a441bd9037549 0x03f007fe00ffc008 0x200fc01ff803ff00

def z474 : W := mkw 0xa800000092000000 0x02a0000002480000 0x3c0000001f000004 0x04f00000007c0000

def z475 : W := mkw 0x0008000100002000 0x0000200004000080 0x0008000100003031 0x90002000040000c0

def z476 : W := mkw 0x04144426018154f1 0x0010511098060553 0x0c70440e0383f1fc 0xa431c110380e0fc7

def z477 : W := mkw 0xfbe00000486a8000 0x03ef80000121aa00 0xfff0000000ffc00f 0x83ffc0000003ff00

def z478 : W := mkw 0xfff7736cd2488000 0x23ffddcdb3492200 0xfffffffee30cc01f 0xebfffffffb8c3300

def z479 : W := mkw 0x00081d8b0491315a 0x040020762c1244c5 0x03087f8f00f031f9 0xb00c21fe3c03c0c7

def z480 : W := mkw 0x1140110808220000 0x0045004420208800 0x33487f8f1cf3003d 0xb4cd21fe3c73cc00

def z481 : W := mkw 0x11481d8b0491315a 0x044520762c1244c5 0x33487f8e000031dd 0xa0cd21fe380000c7

def z482 : W := mkw 0x00081d8b0491315a 0x040020762c1244c5 0x30087f8f1c0031f5 0xb4c021fe3c7000c7

def z483 : W := mkw 0x42898ed1f7dc3fbc 0x190a263b47df70fe 0xc38f87f1fffc3ffb 0xff0e3e1fc7fff0ff

def z484 : W := mkw 0xffff77ed00903018 0x23fffddfb40240c0 0xffffffff00f0303f 0xf3fffffffc03c0c0

def z485 : W := mkw 0xfbe0000040480000 0x03ef800001012000 0xfff00001e0fc002f 0x9bffc0000783f000

def z486 : W := mkw 0x428986d1fafeba1c 0x090a261b47ebfae8 0xc38f87f1fffffe3b 0xff0e3e1fc7fffff8

def z487 : W := mkw 0x42b1026400000000 0x210ac40990000000 0x00b0007000000000 0x0002c001c0000000

def z488 : W := mkw 0x1148190b0c232142 0x044520642c308c85 0x3048780f1c0331f5 0x94c121e03c700cc7

def z489 : W := mkw 0x00000412018556f1 0x000000104806155b 0x0000000000003fc0 0x00000000000000ff

def z490 : W := mkw 0x0008049100943218 0x00002012440250c8 0x038c07f100fc3e3b 0xf80e301fc403f0f8

def z491 : W := mkw 0x1148198b0c33214a 0x044520662c30cc85 0x33487b8f1c7301c5 0x14cd21ee3c71cc07

def z492 : W := mkw 0x1140190a0c230142 0x0445006428308c05 0x3340780f1cf301ed 0x94cd01e03c73cc07

def z493 : W := mkw 0x114819890c32210a 0x044520662430c884 0x33087b811c7031f5 0x94cc21ee0471c0c7

def z494 : W := mkw 0xb94ab989be32290a 0x16e52ae626f8c8a4 0xf30bbb81fc700001 0x13cc2eee07f1c000

def z495 : W := mkw 0xac144436938556f1 0x02b05110da4e155b 0xfcf4447fff8fffff 0xfff3d111fffe3fff

def z496 : W := mkw 0x1140110800000000 0x0045004420000000 0x33083b8000000001 0x00cc20ee00000000

def z497 : W := mkw 0xeebfea65b7002da0 0x33baffa996dc00b6 0xfcbff871ff003ff7 0xdff2ffe1c7fc00ff

def z498 : W := mkw 0x04044402018114f0 0x0010111008060453 0x0c44440e03833ffe 0xec311110380e0cff

def z499 : W := mkw 0x040efd8b25913dfa 0x14103bf62c9644f7 0x000fff8e00003fd0 0x60003ffe380000ff

def z500 : W := mkw 0x04044000010004a0 0x0010110000040012 0x0c04000003000e02 0x48301000000c0038

def z501 : W := mkw 0x114019080c220102 0x0445006420308804 0x300038001c000000 0x00c000e000700000

def z502 : W := mkw 0xfbe80c83defbb15a 0x07efa0320f7beec5 0xfff00001fffff1ef 0x9fffc00007ffffc7

def z503 : W := mkw 0xfbe00412dbefd6f1 0x03ef80104b6fbf5b 0xfff00001ffffffef 0x9fffc00007ffffff

def z504 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00f800000000013 0xc3003e0000000000

def z505 : W := mkw 0xbd4e7d8b9fb335fa 0x16f539f62e7eccd7 0x3f487f8f1ff331fd 0xb4fd21fe3c7fccc7

def z506 : W := mkw 0xac1ee827b7016de1 0x12b07ba09edc05b7 0xfc7ff80fff03fff7 0xdff1ffe03ffc0fff

def z507 : W := mkw 0xffffff7fb7857ff1 0x33fffffdfede15ff 0xffffffffff8fffff 0xfffffffffffe3fff

def z508 : W := mkw 0x4280041040cc1210 0x010a001041033048 0xc3840471e0fc3e3b 0xfb0e1011c783f0f8

def z509 : W := mkw 0x428906d140dc321c 0x090a241b450370c8 0x038807f100fc3039 0xb00e201fc403f0c0

def z510 : W := mkw 0xfff7626400000000 0x23ffdd8990000000 0xfff780700000000f 0xc3ffde01c0000000

def z511 : W := mkw 0x53e00000da6a8000 0x014f80000369aa00 0x03f00001ffffc028 0x1c0fc00007ffff00

def z512 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xcff787fe0000000a 0x633fde1ff8000000

def z513 : W := mkw 0xeeb44034d34cc6a1 0x03bad100d34d331a 0xccb40070e30cce02 0x4b32d001c38c3338

def z514 : W := mkw 0xfff76264da6a8000 0x23ffdd899369aa00 0xfff78071ffffc02f 0xdfffde01c7ffff00

def z515 : W := mkw 0xb9681d8b9eb3b15a 0x06e5a0762e7acec5 0x3f787f8f1ff3f1fd 0xb4fde1fe3c7fcfc7

def z516 : W := mkw 0x11489d8bbfb33dfa 0x144522762efeccf7 0x33487f8ffff33ffd 0xbccd21fe3fffccff

def z517 : W := mkw 0x000982c12010280c 0x0800260b048040a0 0x000b838000000000 0x00002e0e00000000

def z518 : W := mkw 0xffff7fef0491315a 0x27fffdffbc1244c5 0xfffffffe000031df 0xe3fffffff80000c7

def z519 : W := mkw 0x1148158b08b3305a 0x044520562c22ccc1 0x0348078f00f33039 0xb00d201e3c03ccc0

def z520 : W := mkw 0x0000000000000000 0x0000000000000000 0x0004000000003e32 0xc8001000000000f8

def z521 : W := mkw 0x0000000008220000 0x0000000000208800 0x000000011cf30020 0x140000000473cc00

def z522 : W := mkw 0x000986d120943a1c 0x0800261b448250e8 0x030f87f100f03e39 0xf00c3e1fc403c0f8

def z523 : W := mkw 0x04066800050005a0 0x101019a000140016 0x00007800000001c0 0x000001e000000007

def z524 : W := mkw 0x0003334800000000 0x20000ccd20000000 0x000bbb8000000000 0x00002eee00000000

def z525 : W := mkw 0x53e0000000000000 0x014f800000000000 0x03f0000000000008 0x000fc00000000000

def z526 : W := mkw 0xa802a000b2000800 0x12a00a8002c80020 0xc0038000e0000000 0x03000e0003800000

def z527 : W := mkw 0x11581dbf0cb7735b 0x04456076fc32ddcd 0x33f87fff1cfff1fd 0xb4cfe1fffc73ffc7

def z528 : W := mkw 0xffffffefbfb33dfa 0x37ffffffbefeccf7 0xfffffffffff33fff 0xffffffffffffccff

def z529 : W := mkw 0xfbe0000008220000 0x03ef800000208800 0xfff000011cf3002f 0x97ffc0000473cc00

def z530 : W := mkw 0xea800000d2480000 0x03aa000003492000 0xff800001fffc002f 0x9ffe000007fff000

def z531 : W := mkw 0xfbe33348da6a8000 0x23ef8ccd2369aa00 0xf30bbb81fc700001 0x13cc2eee07f1c000

def z532 : W := mkw 0x4695c274614c4ea5 0x091a5709d185313a 0xccb78070e30cce02 0x4b32de01c38c3338

def z533 : W := mkw 0xfffffb6db6002900 0x33ffffedb6d800a4 0xfffffffffc00001f 0xf3fffffffff00000

def z534 : W := mkw 0x53c117da48ff125e 0x0d4f045f6923fc49 0x03c007fe00ff0008 0x200f001ff803fc00

def z535 : W := mkw 0x428906c100903018 0x010a241b040240c0 0xc38f87f100f0303b 0xf30e3e1fc403c0c0

def z536 : W := mkw 0x1140190a0c230142 0x0445006428308c05 0x33487f8e1c0301dd 0xa4cd21fe38700c07

def z537 : W := mkw 0xac16602400000000 0x02b0598090000000 0xfcfffc7e0000001f 0xe3f3fff1f8000000

def z538 : W := mkw 0x0000000000000000 0x0000000000000000 0x00f00000008fc008 0x0003c00000023f00

def z539 : W := mkw 0xac0eec81b7903db8 0x12b03bb206de40f6 0xff0fff81fff03fff 0xfffc3ffe07ffc0ff

def z540 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0c74447e0303ffd4 0x6431d111f80c0fff

def z541 : W := mkw 0x041dc6f721957efd 0x0810771bdc8655fb 0x0cffc7fe038ffffe 0xec33ff1ff80e3fff

def z542 : W := mkw 0xac1ee835b7046fa1 0x12b07ba0d6dc11be 0xfcbff871ff0cfff7 0xdff2ffe1c7fc33ff

def z543 : W := mkw 0xac0eec83bfb33dfa 0x16b03bb20efeccf7 0xfc0ff801fff33ff7 0xdff03fe007ffccff

def z544 : W := mkw 0x11480c830cb3315a 0x044520320c32ccc5 0x334000011cf331ed 0x94cd00000473ccc7

def z545 : W := mkw 0x041c5dbf059577fb 0x04107176fc1655df 0x000c7ffe00003fd0 0x600031fff80000ff

def z546 : W := mkw 0xfff7736e010144e1 0x23ffddcdb8040513 0xfffffffe0303c1df 0xe7fffffff80c0f07

def z547 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0cf4447e00003fde 0xe033d111f80000ff

def z548 : W := mkw 0x0414402400000000 0x0010510090000000 0x0c70400e00000004 0x0031c10038000000

def z549 : W := mkw 0xa80aa801b6002900 0x12a02aa006d800a4 0xfc0bb801ff000027 0x9ff02ee007fc0000

def z550 : W := mkw 0x04144034010446a1 0x00105100d004111a 0x0cb44070030cfff6 0xcc32d101c00c33ff

def z551 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfc0bf801ff0001c5 0x17f02fe007fc0007

def z552 : W := mkw 0xfff777fc40dc121c 0x2bffdddff1037048 0xfffffffe00fc001f 0xe3fffffff803f000

def z553 : W := mkw 0xfbe1024000000000 0x03ef840900000000 0xffff87f00000001f 0xe3fffe1fc0000000

def z554 : W := mkw 0xac1eec37b7857ff1 0x12b07bb0dede15ff 0xfc0ffc7fff003ff7 0xfff03ff1fffc00ff

def z555 : W := mkw 0xffe6e000fb6a8ca0 0x13ff9b8003edaa32 0xfff78001ffffce2f 0xdfffde0007ffff38

def z556 : W := mkw 0x53f117ee08b3105a 0x254fc45fb822cc41 0x03f007fe00f30008 0x200fc01ff803cc00

def z557 : W := mkw 0xfff7736c9a228000 0x23ffddcdb2688a00 0xfffffffe1f03c01f 0xe7fffffff87c0f00

def z558 : W := mkw 0x0008080104002100 0x0000202004100084 0x300838011c000001 0x10c020e004700000

def z559 : W := mkw 0x00000000d2488000 0x0000000003492200 0x00000000e30cc000 0x08000000038c3300

def z560 : W := mkw 0x469dc6f561dc7ebd 0x091a771bd58771fa 0xcfbf87f1e3fcfe3b 0xfb3efe1fc78ff3f8

def z561 : W := mkw 0x4280000000000000 0x010a000000000000 0xc38000000000000b 0x830e000000000000

def z562 : W := mkw 0xac166436018556f1 0x02b05990d806155b 0xfcfffc7e038fffff 0xeff3fff1f80e3fff

def z563 : W := mkw 0x53e00000486a8000 0x014f80000121aa00 0x0300000000700000 0x000c00000001c000

def z564 : W := mkw 0xbd46710800000000 0x02f519c420000000 0xff4fff8e0000001f 0xe3fd3ffe38000000

def z565 : W := mkw 0xac06e000b3000ca0 0x12b01b8002cc0032 0xcc07c000e3003ff6 0xcf301f00038c00ff

def z566 : W := mkw 0x041eec3725857ff1 0x10107bb0dc9615ff 0x000ffc7e00003fd0 0x60003ff1f80000ff

def z567 : W := mkw 0x0008849160dc3a1c 0x08002212458370e8 0xc00f8001e0fc3e33 0xdb003e000783f0f8

def z568 : W := mkw 0x04044000010004a0 0x0010110000040012 0x0c004000030001c4 0x04300100000c0007

def z569 : W := mkw 0x04144034010446a1 0x00105100d004111a 0x0cf40070038fce2e 0xcc33d001c00e3f38

def z570 : W := mkw 0x0000048208b3105a 0x040000120822cc41 0x0000000000f30000 0x000000000003cc00

def z571 : W := mkw 0xa80aa801b6002900 0x12a02aa006d800a4 0xf00bf801fc0031f5 0x97c02fe007f000c7

def z572 : W := mkw 0x4281865060cc1a14 0x090a061941833068 0xc0878470e08c3e3a 0xeb021e11c38230f8

def z573 : W := mkw 0xfffdc6f7fbfffefd 0x0bfff71bdfeffffb 0xffffc7ffffffffff 0xffffff1fffffffff

def z574 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0x3ff07ffe0000000c 0x20ffc1fff8000000

def z575 : W := mkw 0x00080c930db777fb 0x040020324c36dddf 0x000000011fffffe0 0x1c000000047fffff

def z576 : W := mkw 0x11481d890cb2311a 0x044520762432c8c4 0x33083f811cf03039 0xb0cc20fe0473c0c0

def z577 : W := mkw 0xfbe18250fa6e8a04 0x0bef860943e9ba28 0xfff78071ffffce2f 0xdfffde01c7ffff38

def z578 : W := mkw 0xfbf1136c00000000 0x23efc44db0000000 0xfff007fe0000000f 0xa3ffc01ff8000000

def z579 : W := mkw 0x00008010604c0a04 0x0800020041813028 0x00000000e00c0e00 0x0800000003803038

def z580 : W := mkw 0xac16e436b3855ef1 0x12b05b90dace157b 0xccf7c47ee38ffffe 0xef33df11fb8e3fff

def z581 : W := mkw 0xbd4ee801bf222da0 0x12f53ba006fc88b6 0xff4ff801fff33fff 0xdffd3fe007ffccff

def z582 : W := mkw 0x0010043600855251 0x00004010d8021549 0x0cf0047e038fc02e 0xac33c011f80e3f00

def z583 : W := mkw 0xfbf1136cda6a8000 0x23efc44db369aa00 0xfff007ffffffc02f 0xbfffc01fffffff00

def z584 : W := mkw 0x1140000008220000 0x0045000000208800 0x3ff000011fffc02f 0x9cffc000047fff00

def z585 : W := mkw 0x0000000000000000 0x0000000000000000 0x00004000000031f4 0x84000100000000c7

def z586 : W := mkw 0xa802280096000100 0x12a008a002580004 0x300038001c000000 0x00c000e000700000

def z587 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xfcf00000ff0fc006 0x0ff3c00003fc3f00

def z588 : W := mkw 0x53c91fdb4cff335e 0x0d4f247f6d33fccd 0x33c87fff1cff31fd 0xb4cf21fffc73fcc7

def z589 : W := mkw 0x04144026010144e1 0x0010510098040513 0x0cf4447e0303c1de 0xe433d111f80c0f07

def z590 : W := mkw 0xfff44034db6ec6a1 0x03ffd100d36dbb1a 0xfff40071ffffce2f 0xdfffd001c7ffff38

def z591 : W := mkw 0x0000041000841210 0x0000001040021048 0x00800470008c0008 0x20020011c0023000

def z592 : W := mkw 0xfbe3334800000000 0x23ef8ccd20000000 0xf38fbff00000001b 0xe3ce3effc0000000

def z593 : W := mkw 0xa800000092000000 0x02a0000002480000 0xf0000001fc000001 0x13c0000007f00000

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000001e0000023 0x9b00000007800000

def z595 : W := mkw 0xffefeed1fffebfbc 0x1bffbfbb47fffafe 0xfffffff1ffffffff 0xffffffffc7ffffff

def z596 : W := mkw 0x428106d040dc121c 0x090a041b41037048 0xc38f87f000fc001b 0xe30e3e1fc003f000

def z597 : W := mkw 0xfff44026db6bc4e1 0x03ffd1009b6daf13 0xfff0400fffffc1ef 0x9fffc1003fffff07

def z598 : W := mkw 0x53c99fd96cfe3b1e 0x0d4f267f65b3f8ec 0xf38fbff1fcfc3e3b 0xfbce3effc7f3f0f8

def z599 : W := mkw 0xee87624000000000 0x03ba1d8900000000 0xff8ffff00000001f 0xe3fe3fffc0000000

def z600 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xff700001ff73c005 0x17fdc00007fdcf00

def z601 : W := mkw 0x00081d8b0cb3315a 0x040020762c32ccc5 0x00087f8f1cf331f0 0x340021fe3c73ccc7

def z602 : W := mkw 0x0414402400000000 0x0010510090000000 0x0cb4007000000002 0x4032d001c0000000

def z603 : W := mkw 0xfff7777edbefd6f1 0x23ffddddfb6fbf5b 0xffffffffffffffff 0xffffffffffffffff

def z604 : W := mkw 0xac0ee001b3002ca0 0x12b03b8006cc00b2 0xcc0f8001e3003e33 0xdb303e00078c00f8

def z605 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0cb4447e030cffd2 0x6832d111f80c33ff

def z606 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xcc0ff800e3003fd2 0x4b303fe0038c00ff

def z607 : W := mkw 0x0000041000841210 0x0000001040021048 0x0cf40470038ffe3e 0xec33d011c00e3ff8

def z608 : W := mkw 0x1140158a08b3105a 0x044500562822cc41 0x33487f8e00f3001d 0xa0cd21fe3803cc00

def z609 : W := mkw 0x53f91fef0cb3315a 0x254fe47fbc32ccc5 0x33f87fff1cf331fd 0xb4cfe1fffc73ccc7

def z610 : W := mkw 0x4280000040480000 0x010a000001012000 0xcff00001e3ffc02f 0x9f3fc000078fff00

def z611 : W := mkw 0x4280000040480000 0x010a000001012000 0xc3000001e0700001 0x130c00000781c000

def z612 : W := mkw 0x0404400000000000 0x0010110000000000 0x0c04400000000016 0xc030110000000000

def z613 : W := mkw 0x1160000008228000 0x0045800000208a00 0x007000000003c000 0x0001c00000000f00

def z614 : W := mkw 0x0000000000000000 0x0000000000000000 0x004000000083002c 0x8401000000020c00

def z615 : W := mkw 0xac06e000b3000ca0 0x12b01b8002cc0032 0xfc0ff800e3000e17 0xcbf03fe0038c0038

def z616 : W := mkw 0xfbe986d160dc3a1c 0x0befa61b458370e8 0xffff87f1e0fc3e3f 0xfbfffe1fc783f0f8

def z617 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33483f8f1cf30009 0x30cd20fe3c73cc00

def z618 : W := mkw 0x00088801b6002900 0x1000222006d800a4 0x00000001fc000000 0x1000000007f00000

def z619 : W := mkw 0x114819890c32210a 0x044520662430c884 0x33483b811cf3002d 0x94cd20ee0473cc00

def z620 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xcff00000e3ffc00a 0x0b3fc000038fff00

def z621 : W := mkw 0xeaa00000d2488000 0x03aa800003492200 0xccf00000e38fc02e 0x8f33c000038e3f00

def z622 : W := mkw 0x041cc43721857ef1 0x00107310dc8615fb 0xccffc47fe38fffff 0xff33ff11ff8e3fff

def z623 : W := mkw 0xac0eec13b7857ff1 0x12b03bb04ede15ff 0xfc0ff801ff8ffff7 0xdff03fe007fe3fff

def z624 : W := mkw 0xeeb7e264b3000ca0 0x33badf8992cc0032 0xccb78070e3000e02 0x4b32de01c38c0038

def z625 : W := mkw 0x00088801b7002da0 0x1000222006dc00b6 0x30087801ff003ff5 0x9cc021e007fc00ff

def z626 : W := mkw 0x4281024000000000 0x010a040900000000 0x038007f000000008 0x200e001fc0000000

def z627 : W := mkw 0xbd7e7daf0cb3315a 0x26f5f9f6bc32ccc5 0x3f787f8f1cf331fd 0xb4fde1fe3c73ccc7

def z628 : W := mkw 0x1140158a08b3105a 0x044500562822cc41 0x3340078f1cf3002d 0xb4cd001e3c73cc00

def z629 : W := mkw 0x53c997d960dc3a1c 0x094f265f658370e8 0xf3cfffffe0fc3e3f 0xfbcf3fffff83f0f8

def z630 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xff000001ff700027 0x9ffc000007fdc000

def z631 : W := mkw 0x53c00000486a0000 0x014f00000121a800 0xf3c00001fcff002f 0x9fcf000007f3fc00

def z632 : W := mkw 0x04144026010144e1 0x0010510098040513 0x0c74400e0303fff6 0xcc31d100380c0fff

def z633 : W := mkw 0x04144024010044a1 0x0010510090040112 0x0c3000000300c000 0x0030c000000c0300

def z634 : W := mkw 0xbd6ee801bf22ada0 0x12f5bba006fc8ab6 0xfc7ff801ff03fff7 0xdff1ffe007fc0fff

def z635 : W := mkw 0xfff7736cda6a8000 0x23ffddcdb369aa00 0xfffffffffc70001f 0xf3fffffffff1c000

def z636 : W := mkw 0x041c44b7019576f9 0x00107112dc0655db 0x0ffc47ff03ffffff 0xfc3ff11ffc0fffff

def z637 : W := mkw 0x0008048300913058 0x000020120c0244c1 0x0348478f00f331fd 0xb40d211e3c03ccc7

def z638 : W := mkw 0xac066800970005a0 0x12b019a0025c0016 0x3c0478001f003ff6 0xccf011e0007c00ff

def z639 : W := mkw 0x04044000010004a0 0x0010110000040012 0x0004400000003fd0 0x40001100000000ff

def z640 : W := mkw 0x041c4cb70db777fb 0x04107132dc36dddf 0x0cf4447f1ffffffe 0xfc33d111fc7fffff

def z641 : W := mkw 0xfffffffdf7dc3fbc 0x3bfffffff7df70fe 0xfffffffffffc3fff 0xfffffffffffff0ff

def z642 : W := mkw 0xea8baed1f6dc3b1c 0x1baa2ebb47db70ec 0xf38fbff1fcfc3e3b 0xfbce3effc7f3f0f8

def z643 : W := mkw 0x00000000010004a0 0x0000000000040012 0x0000000003003fe0 0x0c000000000c00ff

def z644 : W := mkw 0xac044000930004a0 0x02b01100024c0012 0xfc044001ff003ff7 0xdff0110007fc00ff

def z645 : W := mkw 0xac0ee00120002800 0x02b03b80048000a0 0xfc0ff801e0003e37 0xdbf03fe0078000f8

def z646 : W := mkw 0x1140000008220000 0x0045000000208800 0x0340000000f30008 0x000d00000003cc00

def z647 : W := mkw 0x1554512c00000000 0x00555144b0000000 0x3ffc7ffe0000001f 0xe0fff1fff8000000

def z648 : W := mkw 0x0010043600855251 0x00004010d8021549 0x00f4047e008ffe3a 0xe803d011f8023ff8

def z649 : W := mkw 0x53f0043648efd251 0x014fc010d923bf49 0x03f0047e00ffc008 0x200fc011f803ff00

def z650 : W := mkw 0x428986d361dd7efd 0x090a261b4d8775fb 0xc38f87f1e3fffffb 0xff0e3e1fc78fffff

def z651 : W := mkw 0xee8fe6d1f3dc3ebc 0x1bba3f9b47cf70fa 0xcf8f87f1e3fc3e3b 0xfb3e3e1fc78ff0f8

def z652 : W := mkw 0x040feed125943fbc 0x18103fbb449650fe 0x000ffff000003fd0 0x60003fffc00000ff

def z653 : W := mkw 0xfff44436018556f1 0x03ffd110d806155b 0xfff4447e038fffff 0xefffd111f80e3fff

def z654 : W := mkw 0xfbe0190ade6b8142 0x07ef80642b79ae05 0xfff0780fffffc1ef 0x9fffc1e03fffff07

def z655 : W := mkw 0x42899fdb64dd3b5e 0x0d0a267f6d9374ed 0xc38fffffe0fc3ffb 0xfb0e3fffff83f0ff

def z656 : W := mkw 0x0008800120002800 0x00002200048000a0 0x000f800000003e10 0x40003e00000000f8

def z657 : W := mkw 0x57dddfff6dff7fff 0x0d5f777ffdb7fdff 0xffffffffffffffff 0xffffffffffffffff

def z658 : W := mkw 0xee8fea51f74c2fa4 0x1bba3fa947dd30be 0xfc8ff871ff0c3ff7 0xdff23fe1c7fc30ff

def z659 : W := mkw 0x040ee801b7002da0 0x10103ba006dc00b6 0x000ff801ff003ff0 0x5c003fe007fc00ff

def z660 : W := mkw 0xfff7777c00841210 0x23ffddddf0021048 0xfffffffe008c3e3f 0xebfffffff80230f8

def z661 : W := mkw 0xac16e034b3044ea1 0x12b05b80d2cc113a 0xccb78070e30cce02 0x4b32de01c38c3338

def z662 : W := mkw 0xeaa986d1f2dcba1c 0x0baaa61b47cb72e8 0xcfbf87f1e3fcfe3b 0xfb3efe1fc78ff3f8

def z663 : W := mkw 0x00080c830cb3315a 0x040020320c32ccc5 0x030807811cf331f9 0xb40c201e0473ccc7

def z664 : W := mkw 0x00000412018556f1 0x000000104806155b 0x0cf00000038fffee 0x8c33c000000e3fff

def z665 : W := mkw 0xfbe3334800000000 0x23ef8ccd20000000 0xf34bff8e0000001d 0xa3cd2ffe38000000

def z666 : W := mkw 0x00000412018556f1 0x000000104806155b 0x00840470038ffffa 0xec021011c00e3fff

def z667 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000038fc020 0x0c000000000e3f00

def z668 : W := mkw 0x1170112c00000000 0x2045c044b0000000 0x0070000e00000000 0x0001c00038000000

def z669 : W := mkw 0x0000041200855251 0x0000001048021549 0x00000000008fc000 0x0000000000023f00

def z670 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33083b811cf331e1 0x14cc20ee0473ccc7

def z671 : W := mkw 0xffffffff6cff3b5e 0x2ffffffffdb3fced 0xfffffffffcff3fff 0xfffffffffff3fcff

def z672 : W := mkw 0x4281824060480804 0x090a060901812020 0xc0038000e0000000 0x03000e0003800000

def z673 : W := mkw 0x0000000000000000 0x0000000000000000 0x00800000008c002a 0x8802000000023000

def z674 : W := mkw 0x0000080004000100 0x0000002000100004 0x300078001c0001c4 0x04c001e000700007

def z675 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0c04447e03003ff6 0xec301111f80c00ff

def z676 : W := mkw 0x53e1134800000000 0x214f844d20000000 0x0300038000000000 0x000c000e00000000

def z677 : W := mkw 0x0000000040480000 0x0000000001012000 0x00000001e0fc0020 0x180000000783f000

def z678 : W := mkw 0x155c5dbf0db777fb 0x04557176fc36dddf 0x334c7fff1cf33ffd 0xf4cd31fffc73ccff

def z679 : W := mkw 0x53c99bc96c7a290e 0x0d4f266f25b1e8a4 0xf30bbb81fc700001 0x13cc2eee07f1c000

def z680 : W := mkw 0xfbe81d8bdefbb15a 0x07efa0762f7beec5 0xf3487f8ffcf331fd 0xb7cd21fe3ff3ccc7

def z681 : W := mkw 0x0000048000901018 0x0000001200024040 0x0300078000f00008 0x200c001e0003c000

def z682 : W := mkw 0xffff7fefdefbb15a 0x27fffdffbf7beec5 0xfffffffffffff1ff 0xffffffffffffffc7

def z683 : W := mkw 0xbd76712c00000000 0x22f5d9c4b0000000 0xfc7ff80e00000017 0xc3f1ffe038000000

def z684 : W := mkw 0xfbe982c1fa7aa80c 0x0befa60b07e9eaa0 0xf30b8381fc700001 0x13cc2e0e07f1c000

def z685 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0x038007f1e0fc3e28 0x380e001fc783f0f8

def z686 : W := mkw 0x57f4443649efd6f1 0x015fd110d927bf5b 0x0ff4447e03fffffe 0xec3fd111f80fffff

def z687 : W := mkw 0x00081d8b0491315a 0x040020762c1244c5 0x00487f8e008331fc 0xa40121fe38020cc7

def z688 : W := mkw 0x000880816058280c 0x08002202058160a0 0x00000001e0700000 0x100000000781c000

def z689 : W := mkw 0x0000000000000000 0x0000000000000000 0x0308078000000019 0xa00c201e00000000

def z690 : W := mkw 0x53e00000486a8000 0x014f80000121aa00 0x33f000011cffc02d 0x94cfc0000473ff00

def z691 : W := mkw 0x04144024010004a0 0x0010510090040012 0x0cf4447e03003ffe 0xec33d111f80c00ff

def z692 : W := mkw 0x428102c04058000c 0x090a040b01016000 0x0300038000700000 0x000c000e0001c000

def z693 : W := mkw 0x468dc6d161dc3ebc 0x091a371b458770fa 0xcf8fc7f1e3fc3fff 0xff3e3f1fc78ff0ff

def z694 : W := mkw 0xfff4402400000000 0x03ffd10090000000 0xfff4447e0000001f 0xe3ffd111f8000000

def z695 : W := mkw 0xfff44024da6a8000 0x03ffd1009369aa00 0xfff4447fffffc03f 0xffffd111ffffff00

def z696 : W := mkw 0xffeee801b7002da0 0x13ffbba006dc00b6 0xfffff801ff003fff 0xdfffffe007fc00ff

def z697 : W := mkw 0x0414402400000000 0x0010510090000000 0x0004447e00000010 0x60001111f8000000

def z698 : W := mkw 0x4289824120002800 0x010a2609048000a0 0xc38f87f1e0003e3b 0xfb0e3e1fc78000f8

def z699 : W := mkw 0x041ffb6d25002da0 0x30107fedb49400b6 0x000ffffe00003fd0 0x60003ffff80000ff

def z700 : W := mkw 0x0010043600855251 0x00004010d8021549 0x00f0447e008ff1fc 0xa403c111f8023fc7

def z701 : W := mkw 0x0010003400044201 0x00004000d0001108 0x00b00070000cc000 0x0002c001c0003300

def z702 : W := mkw 0x4280000040480000 0x010a000001012000 0x0380000000fc0008 0x000e00000003f000

def z703 : W := mkw 0xfbe00000d2488000 0x03ef800003492200 0xfff00000e30cc00f 0x8bffc000038c3300

def z704 : W := mkw 0x000986d120943a1c 0x0800261b448250e8 0xc00f87f1e0003e33 0xfb003e1fc78000f8

def z705 : W := mkw 0x0008800120002800 0x00002200048000a0 0xc00b8001e0000001 0x13002e0007800000

def z706 : W := mkw 0xfbeaa801fe6aa900 0x13efaaa007f9aaa4 0xf30bb801fc700001 0x13cc2ee007f1c000

def z707 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xfffffffe030cc01f 0xebfffffff80c3300

def z708 : W := mkw 0xfff44436dbefd6f1 0x03ffd110db6fbf5b 0xf304447ffc703fd1 0x73cc1111fff1c0ff

def z709 : W := mkw 0xfbf3336c00000000 0x23efcccdb0000000 0xf3fbfffe0000001d 0xa3cfeffff8000000

def z710 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xff700001ffffc025 0x1ffdc00007ffff00

def z711 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc30f87f1e0703e33 0xfb0c3e1fc781c0f8

def z712 : W := mkw 0x428186d060dc1a1c 0x090a061b41837068 0xc38f87f0e0fc0e1b 0xeb0e3e1fc383f038

def z713 : W := mkw 0xbd7ef5bd60dc3a1c 0x2af5fbd6f58370e8 0x3c70780fe0fc3e24 0x18f1c1e03f83f0f8

def z714 : W := mkw 0xfff7736c010004a0 0x23ffddcdb0040012 0xfffffffe038fffff 0xeffffffff80e3fff

def z715 : W := mkw 0x0417736cda6a8000 0x20105dcdb369aa00 0x000fffffffffc030 0x7c003fffffffff00

def z716 : W := mkw 0xac3ee825b7002da0 0x32b0fba096dc00b6 0xfc3ff801ff003ff7 0xdff0ffe007fc00ff

def z717 : W := mkw 0xbd56712c00000000 0x02f559c4b0000000 0xfffffffe0000001f 0xe3fffffff8000000

def z718 : W := mkw 0x469dc2e761596ced 0x091a770b9d8565b3 0xcf7bc38fe373c1c5 0x173def0e3f8dcf07

def z719 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc3ff87f1e0fffe3b 0xfb0ffe1fc783fff8

def z720 : W := mkw 0xeeb7736c00000000 0x23baddcdb0000000 0xcfbffffe0000001b 0xe33efffff8000000

def z721 : W := mkw 0x1148198b0c33214a 0x044520662c30cc85 0x33487f8f1c7301dd 0xb4cd21fe3c71cc07

def z722 : W := mkw 0xfff7736cda6a8000 0x23ffddcdb369aa00 0xfffffffee3ffc01f 0xebfffffffb8fff00

def z723 : W := mkw 0xfff7736cd2488000 0x23ffddcdb3492200 0xffffffffff0cc03f 0xfffffffffffc3300

def z724 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xfffffffe0083003f 0xe7fffffff8020c00

def z725 : W := mkw 0xfff7736cda6a8000 0x23ffddcdb369aa00 0xffffffffff73c01f 0xf7fffffffffdcf00

def z726 : W := mkw 0xfbf3336cda6a8000 0x23efcccdb369aa00 0xfffbbfffffffc02f 0xbfffeeffffffff00

def z727 : W := mkw 0x11401d8a0cb3115a 0x044500762832cc45 0x33407f8f1cf301ed 0xb4cd01fe3c73cc07

def z728 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33487f8f1cf301cd 0x34cd21fe3c73cc07

def z729 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfc0ff801fc003fd7 0xd3f03fe007f000ff

def z730 : W := mkw 0x53f117fe48ff125e 0x2d4fc45ff923fc49 0x03f007fe00ff0008 0x200fc01ff803fc00

def z731 : W := mkw 0xfff7736c40488000 0x23ffddcdb1012200 0xfffffffe000cc01f 0xe3fffffff8003300

def z732 : W := mkw 0x1557736c08220000 0x20555dcdb0208800 0x334fffff1cf3003d 0xf4cd3ffffc73cc00

def z733 : W := mkw 0xb9600000da6a8000 0x02e580000369aa00 0x3f700001ffffc02d 0x9cfdc00007ffff00

def z734 : W := mkw 0xeaa81d8bd6d9b15a 0x07aaa0762f5b66c5 0xccb87f8ee30cf1d2 0x2b32e1fe3b8c33c7

def z735 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc38f87f1e0fc0e0b 0x7b0e3e1fc783f038

def z736 : W := mkw 0x040ee80125002da0 0x10103ba0049400b6 0xf00ff801fc003ff7 0xdfc03fe007f000ff

def z737 : W := mkw 0xb9600000da6a8000 0x02e580000369aa00 0xfc700001ffffc027 0x9ff1c00007ffff00

def z738 : W := mkw 0xfff7736c9a228000 0x23ffddcdb2688a00 0xfffffffe1f8fc03f 0xeffffffff87e3f00

def z739 : W := mkw 0xbd46f58abbb31cfa 0x16f51bd62aeecc73 0xcf47878ee3f30e0a 0x6b3d1e1e3b8fcc38

def z740 : W := mkw 0x428986d360dd3a5c 0x090a261b4d8374e9 0xc3cf87ffe0ff3e3b 0xfb0f3e1fff83fcf8

def z741 : W := mkw 0xfbe11348da6a8000 0x03ef844d2369aa00 0xffffffffffffc03f 0xffffffffffffff00

def z742 : W := mkw 0x11681d8b0cb3b15a 0x0445a0762c32cec5 0x33787f8f1cf3f1fd 0xb4cde1fe3c73cfc7

def z743 : W := mkw 0xfbe10240da6a8000 0x03ef84090369aa00 0xfff007f1ffffc02f 0xbfffc01fc7ffff00

def z744 : W := mkw 0x1140150a08a31050 0x0045005428228c41 0x33487f8f1cf331fd 0xb4cd21fe3c73ccc7

def z745 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc30f87f1e0f03e39 0xf30c3e1fc783c0f8

def z746 : W := mkw 0xfff7736c486a0000 0x23ffddcdb121a800 0xfffffffffcff003f 0xfffffffffff3fc00

def z747 : W := mkw 0xac0ee80124002900 0x02b03ba0049000a4 0xfc0ff801fc003ff7 0xdff03fe007f000ff

def z748 : W := mkw 0xb94000009a220000 0x02e5000002688800 0xfff00001ffffc02f 0x9fffc00007ffff00

def z749 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc38f87f1e07c3e13 0x7b0e3e1fc781f0f8

def z750 : W := mkw 0x00088c93f7dd7ffd 0x180022324fdf75ff 0x00000001ffffffe0 0x1c00000007ffffff

def z751 : W := mkw 0xeeb7736cd2488000 0x23baddcdb3492200 0xccbffffee30cc012 0x6b32fffffb8c3300

def z752 : W := mkw 0xac06e800b7000da0 0x12b01ba002dc0036 0xfc07f800ff003ff6 0xcff01fe003fc00ff

def z753 : W := mkw 0xeaa00000da6a8000 0x03aa80000369aa00 0xccf00001ffffc02e 0x9f33c00007ffff00

def z754 : W := mkw 0xfff7736c92008000 0x23ffddcdb2480200 0xfffffffe0300c01f 0xe3fffffff80c0300

def z755 : W := mkw 0x11481d9b0cb7335a 0x044520766c32dccd 0x3ffc7fff1fffffff 0xfcfff1fffc7fffff

def z756 : W := mkw 0xfbebbb49fe6aa900 0x33efaeed27f9aaa4 0xf30bbb81fc700001 0x13cc2eee07f1c000

def z757 : W := mkw 0x0417736c00000000 0x20105dcdb0000000 0x0c7ffffe00000014 0x6031fffff8000000

def z758 : W := mkw 0xfff7736c40480000 0x23ffddcdb1012000 0xffffffffe070001f 0xf3ffffffff81c000

def z759 : W := mkw 0xeaa00000da6a8000 0x03aa80000369aa00 0xcfb00001ffffc02b 0x9f3ec00007ffff00

def z760 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xffb00001ffffc023 0x1ffec00007ffff00

def z761 : W := mkw 0xac17736c00000000 0x22b05dcdb0000000 0xf00ffffe00000011 0x63c03ffff8000000

def z762 : W := mkw 0x53f99b6db7002da0 0x314fe66db6dc00b6 0x03f007ffff003fe8 0x3c0fc01ffffc00ff

def z763 : W := mkw 0x041efdbf25957ffb 0x14107bf6fc9655ff 0x000ffffe00003fd0 0x60003ffff80000ff

def z764 : W := mkw 0xa80aa801b7002da0 0x12a02aa006dc00b6 0xfc0bb801ff003fe7 0x9ff02ee007fc00ff

def z765 : W := mkw 0xb96986d1bab6ba1c 0x0ae5a61b46eadae8 0x3c7f87f01f03fe14 0x64f1fe1fc07c0ff8

def z766 : W := mkw 0x428982d1605c2a0c 0x090a260b458170a8 0xc38f87f1e07c0e1b 0xfb0e3e1fc781f038

def z767 : W := mkw 0xfff7736c9a220000 0x23ffddcdb2688800 0xfffffffffff3003f 0xffffffffffffcc00

def z768 : W := mkw 0xfff7736cda6a8000 0x23ffddcdb369aa00 0xffffffffff7cc01f 0xfbfffffffffdf300

def z769 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xfffffffe008c003f 0xebfffffff8023000

def z770 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfc4ff801ff833fff 0xdff13fe007fe0cff

def z771 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xffffffff1c00003f 0xf7fffffffc700000

def z772 : W := mkw 0xfff7736c08220000 0x23ffddcdb0208800 0xfffffffe00f3001f 0xe3fffffff803cc00

def z773 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x3f787f8f1ff3f1fd 0xb4fde1fe3c7fcfc7

def z774 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xff0ffffe00000017 0xe3fc3ffff8000000

def z775 : W := mkw 0xac17736c00000000 0x22b05dcdb0000000 0xcc0ffffe00000012 0x63303ffff8000000

def z776 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xffbffffe00000013 0x63fefffff8000000

def z777 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33c87f8f1cff31ff 0xbccf21fe3c73fcc7

def z778 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfcbff801ff0cfff7 0xdff2ffe007fc33ff

def z779 : W := mkw 0x1140198a0c33014a 0x044500662830cc05 0x33407b8e1c7301c4 0x04cd01ee3871cc07

def z780 : W := mkw 0x53c11348486a0000 0x014f044d2121a800 0xf3cffffffcff003f 0xffcf3ffffff3fc00

def z781 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc38f87f1e3fffe3b 0xff0e3e1fc78ffff8

def z782 : W := mkw 0xee876ed0d7dc17bc 0x1bba1dbb435f705e 0x3f807ff01ffc01cc 0x24fe01ffc07ff007

def z783 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc38f87f1e0fc3e19 0x730e3e1fc783f0f8

def z784 : W := mkw 0xee97e274f34c4ea5 0x1bba5f89d3cd313a 0xccb78070e30cce02 0x4b32de01c38c3338

def z785 : W := mkw 0xb9600000da6a8000 0x02e580000369aa00 0x3cf00001ffffc02e 0x9cf3c00007ffff00

def z786 : W := mkw 0x53c19b5a6c6f0b46 0x0d4f066d69b1bc2d 0xf0c7f87efc0f0fc6 0x4fc31fe1fbf03c3f

def z787 : W := mkw 0xeebf6ee70cb3315a 0x27bafdbb9c32ccc5 0xccb780711cf331e2 0x5732de01c473ccc7

def z788 : W := mkw 0xfff7736cda6a8000 0x23ffddcdb369aa00 0xfffffffffcf3003f 0xf7fffffffff3cc00

def z789 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xf00ff801fc003ff3 0xdbc03fe007f000ff

def z790 : W := mkw 0x00100436018556f1 0x00004010d806155b 0x0cf0047e038fffee 0xac33c011f80e3fff

def z791 : W := mkw 0xfff7736c010044a1 0x23ffddcdb0040112 0xfffffffe0300c01f 0xe3fffffff80c0300

def z792 : W := mkw 0xfff7736cd2488000 0x23ffddcdb3492200 0xffffffffe3fcc03f 0xfbffffffff8ff300

def z793 : W := mkw 0xfbe3375a018556f1 0x23ef8cdd6806155b 0xf30bbb80038fffe1 0x0fcc2eee000e3fff

def z794 : W := mkw 0x0417736c010004a0 0x20105dcdb0040012 0x0c0ffffe03003ff6 0xec303ffff80c00ff

def z795 : W := mkw 0xfff7736c92000000 0x23ffddcdb2480000 0xfffffffe1f00001f 0xe7fffffff87c0000

def z796 : W := mkw 0x11489d9b2cb73b5e 0x0c4522766cb2dced 0x33487f8f1cf33ffd 0xb4cd21fe3c73ccff

def z797 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfc0ff800ff003fd6 0x4ff03fe003fc00ff

def z798 : W := mkw 0x57f7736c00000000 0x215fddcdb0000000 0x33fffffe0000001d 0xe0cffffff8000000

def z799 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc30f87f1e0fc3e31 0x7b0c3e1fc783f0f8

def z800 : W := mkw 0x04144436018556f1 0x00105110d806155b 0xccffc47e038fffff 0xef33ff11f80e3fff

def z801 : W := mkw 0xee97736c00000000 0x23ba5dcdb0000000 0xff8ffffe0000001f 0xe3fe3ffff8000000

def z802 : W := mkw 0xac0ee881b7102da8 0x12b03ba206dc40b6 0xff0ffb81ff703ff7 0xdffc3fee07fdc0ff

def z803 : W := mkw 0xbd77736c00000000 0x22f5ddcdb0000000 0x3f7ffffe0000001d 0xe0fdfffff8000000

def z804 : W := mkw 0xbd77736c00000000 0x22f5ddcdb0000000 0xfc7ffffe00000017 0xe3f1fffff8000000

def z805 : W := mkw 0xee97626400000000 0x03ba5d8990000000 0xfffffffe0000001f 0xe3fffffff8000000

def z806 : W := mkw 0xfff7736c40480000 0x23ffddcdb1012000 0xffffffffe3ffc03f 0xffffffffff8fff00

def z807 : W := mkw 0xfbe32240da6a8000 0x23ef8c890369aa00 0xfff38001ffffc02f 0x9fffce0007ffff00

def z808 : W := mkw 0xfff7736c08220000 0x23ffddcdb0208800 0xffffffff1c70001f 0xf3fffffffc71c000

def z809 : W := mkw 0x00081d8b0491315a 0x040020762c1244c5 0x33087f8f1cf031fd 0xb4cc21fe3c73c0c7

def z810 : W := mkw 0xfff7736cda6a8000 0x23ffddcdb369aa00 0xf30ffffffc700011 0x73cc3ffffff1c000

def z811 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc38787f1e0fc3e2a 0x7b0e1e1fc783f0f8

def z812 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc3cfc7ffe0fc3e3f 0xfb0f3f1fff83f0f8

def z813 : W := mkw 0x53e117da48ff925e 0x0d4f845f6923fe49 0x03f007fe00ffc008 0x200fc01ff803ff00

def z814 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc38f87f0e0fc3e1a 0x6b0e3e1fc383f0f8

def z815 : W := mkw 0xbd77736c9a228000 0x22f5ddcdb2688a00 0x3c7ffffe1f03c014 0x64f1fffff87c0f00

def z816 : W := mkw 0xa80aa801b7002da0 0x12a02aa006dc00b6 0xf00bb801fc003fc1 0x13c02ee007f000ff

def z817 : W := mkw 0x428986d360dd3a5c 0x090a261b4d8374e9 0xc38fc7ffe0fc3ffb 0xfb0e3f1fff83f0ff

def z818 : W := mkw 0xa80aa801b7002da0 0x12a02aa006dc00b6 0xf00bf801ff003ff5 0x9fc02fe007fc00ff

def z819 : W := mkw 0xeeb7736c00000000 0x23baddcdb0000000 0xccfffffe0000001e 0xe333fffff8000000

def z820 : W := mkw 0xa81aac37b6857b51 0x12a06ab0deda15ed 0xf0fbbc7ffc8fc009 0x33c3eef1fff23f00

def z821 : W := mkw 0x46b7736c00000000 0x211addcdb0000000 0x00bffffe00000010 0x6002fffff8000000

def z822 : W := mkw 0x57d5536c00000000 0x015f554db0000000 0xfffffffe0000001f 0xe3fffffff8000000

def z823 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xcfff87f1e0fc3e3f 0xfb3ffe1fc783f0f8

def z824 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x334c7f8f1cf33fff 0xfccd31fe3c73ccff

def z825 : W := mkw 0x11489d8b2cb3395a 0x044522762cb2cce5 0x334fff8f1cf33ffd 0xf4cd3ffe3c73ccff

def z826 : W := mkw 0xfbe22000da6a8000 0x03ef88800369aa00 0xfffbb801ffffc02f 0x9fffeee007ffff00

def z827 : W := mkw 0xa8200000da6a8000 0x02a080000369aa00 0x0c300001ffffc020 0x1c30c00007ffff00

def z828 : W := mkw 0xfff7736cda6a8000 0x23ffddcdb369aa00 0xfffffffffcfc003f 0xfbfffffffff3f000

def z829 : W := mkw 0x00000000da6a8000 0x000000000369aa00 0x0c700001ffffc024 0x1c31c00007ffff00

def z830 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x3cf4447f1f8fffff 0xfcf3d111fc7e3fff

def z831 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xf34ffffe0000001d 0xe3cd3ffff8000000

def z832 : W := mkw 0x00000000da6a8000 0x000000000369aa00 0x0cb00001ffffc022 0x1c32c00007ffff00

def z833 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xffff8001ffffc03f 0xdffffe0007ffff00

def z834 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xf3fffffe00000019 0x63cffffff8000000

def z835 : W := mkw 0x57f7736c00000000 0x215fddcdb0000000 0x030ffffe00000010 0x600c3ffff8000000

def z836 : W := mkw 0x11489d8b2cb3395a 0x044522762cb2cce5 0x33487f8ffcf33ffd 0xbccd21fe3ff3ccff

def z837 : W := mkw 0xfbf3336c00000000 0x23efcccdb0000000 0xf30bbffe00000001 0x23cc2efff8000000

def z838 : W := mkw 0x53d117fe48ff525f 0x0d4f445ff923fd49 0x03f007fe00ffc008 0x200fc01ff803ff00

def z839 : W := mkw 0x0417736c010004a0 0x20105dcdb0040012 0x000ffffe00003fd0 0x60003ffff80000ff

def z840 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xffffbffe0000000b 0x63fffefff8000000

def z841 : W := mkw 0xac1ee825b7002da0 0x12b07ba096dc00b6 0xfc0ffc7fff003ff7 0xfff03ff1fffc00ff

def z842 : W := mkw 0x57eee8016d6aada0 0x115fbba005b5aab6 0x03fff80000ffffd8 0x400fffe00003ffff

def z843 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x3cfc7c7e038fffff 0xecf3f1f1f80e3fff

def z844 : W := mkw 0x00088c9364dd3b5e 0x0c0022324d9374ed 0x00000001e0fc3fe0 0x180000000783f0ff

def z845 : W := mkw 0xbd77736c00000000 0x22f5ddcdb0000000 0x3cfffffe0000001e 0xe0f3fffff8000000

def z846 : W := mkw 0x04144024010004a0 0x0010510090040012 0x0cf4447e038ffffe 0xec33d111f80e3fff

def z847 : W := mkw 0x114819090c222100 0x0045206424308884 0x33487f8f1cf331fd 0xb4cd21fe3c73ccc7

def z848 : W := mkw 0x42898ed364dd3b5e 0x0d0a263b4d9374ed 0xc38f87f1e0fc3ffb 0xfb0e3e1fc783f0ff

def z849 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0cf0447e038fffec 0x2c33c111f80e3fff

def z850 : W := mkw 0x0417736c00000000 0x20105dcdb0000000 0xc00ffffe00000013 0xe3003ffff8000000

def z851 : W := mkw 0x57f7736c00000000 0x215fddcdb0000000 0x0ffffffe0000001e 0xe03ffffff8000000

def z852 : W := mkw 0x53c88c936cff3b5e 0x0d4f22324db3fced 0xf3c00001fcff3fef 0x9fcf000007f3fcff

def z853 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0x3ff00001ffffc02c 0x1cffc00007ffff00

def z854 : W := mkw 0xac1ee825b7002da0 0x12b07ba096dc00b6 0xfc7ff80fff003ff7 0xdff1ffe03ffc00ff

def z855 : W := mkw 0x0417736c00000000 0x20105dcdb0000000 0x0c0ffffe00000016 0xe0303ffff8000000

def z856 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xfcf00001ffffc026 0x1ff3c00007ffff00

def z857 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfc8ff801ff8c3fff 0xdff23fe007fe30ff

def z858 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfc0ff801ff003fd3 0x5bf03fe007fc00ff

def z859 : W := mkw 0xfff7736c08220000 0x23ffddcdb0208800 0xffffffff1fffc03f 0xfffffffffc7fff00

def z860 : W := mkw 0x4281065040cc1210 0x010a041941033048 0xc38f87f1e0fc3e3b 0xfb0e3e1fc783f0f8

def z861 : W := mkw 0x42a986d160dcba1c 0x090aa61b458372e8 0xc3bf87f1e0fcfe3b 0xfb0efe1fc783f3f8

def z862 : W := mkw 0x00088c9324953b5e 0x0c0022324c9254ed 0x0000000000003fc0 0x00000000000000ff

def z863 : W := mkw 0x42818250604c0a04 0x090a060941813028 0xc38f87f1e0fc0e3b 0xfb0e3e1fc783f038

def z864 : W := mkw 0x040cc80125002da0 0x00103320049400b6 0xfc0ff801ff003ff7 0xdff03fe007fc00ff

def z865 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0cf4447e030fffd6 0x6c33d111f80c3fff

def z866 : W := mkw 0xfbe01108da6a8000 0x03ef80442369aa00 0xfff0078fffffc02f 0xbfffc01e3fffff00

def z867 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0ff4447f03ffffff 0xfc3fd111fc0fffff

def z868 : W := mkw 0xa8088801b6002900 0x02a0222006d800a4 0xfc0ff801ff003ff7 0xdff03fe007fc00ff

def z869 : W := mkw 0x00088c93feffbb5e 0x0c0022324ffbfeed 0x00000001ffffffe0 0x1c00000007ffffff

def z870 : W := mkw 0xbd76792e9f2305e2 0x36f5d9e4ba7c8c17 0x3c70780e1f0301c4 0x04f1c1e0387c0c07

def z871 : W := mkw 0x428986d360dd3a5c 0x090a261b4d8374e9 0xc38f87f1e0ff3ffb 0xff0e3e1fc783fcff

def z872 : W := mkw 0x428986d360dd7a5d 0x090a261b4d8375e9 0xc38f87f1e0fffe3b 0xfb0e3e1fc783fff8

def z873 : W := mkw 0x0417736c00000000 0x20105dcdb0000000 0x030ffffe00000019 0xe00c3ffff8000000

def z874 : W := mkw 0x00088c93ffff3ffe 0x1c0022324ffffcff 0x00000001ffff3fe0 0x1c00000007fffcff

def z875 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xfff00001ffffc00b 0x1bffc00007ffff00

def z876 : W := mkw 0x00080c8304913158 0x000020320c1244c5 0x33487f8f1cf331fd 0xb4cd21fe3c73ccc7

def z877 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfc0ff801ff8ffff7 0xdff03fe007fe3fff

def z878 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xfffffffe0300003f 0xeffffffff80c0000

def z879 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xfff40001fffffe3f 0xdfffd00007fffff8

def z880 : W := mkw 0xfff7736c486a8000 0x23ffddcdb121aa00 0xffffffff1cffc03f 0xf7fffffffc73ff00

def z881 : W := mkw 0x11400000da6a8000 0x004500000369aa00 0x3ff00001ffffc02f 0x9cffc00007ffff00

def z882 : W := mkw 0xfff7736c92000000 0x23ffddcdb2480000 0xfffffffffc00001f 0xf3fffffffff00000

def z883 : W := mkw 0x0417736c00000000 0x20105dcdb0000000 0x008ffffe0000001a 0xe0023ffff8000000

def z884 : W := mkw 0x42898ed164dc3b1c 0x090a263b459370ec 0xc38f87f1fcfc3ffb 0xff0e3e1fc7f3f0ff

def z885 : W := mkw 0x11481d9b0cb7335a 0x044520766c32dccd 0x33487f8f1cff3ffd 0xbccd21fe3c73fcff

def z886 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc38f83f1e0fc3e23 0x5b0e3e0fc783f0f8

def z887 : W := mkw 0x0001134800000000 0x0000044d20000000 0x000ffffe00000010 0x60003ffff8000000

def z888 : W := mkw 0x00088801b7002da0 0x1000222006dc00b6 0xf00ff801ff003ff7 0xdfc03fe007fc00ff

def z889 : W := mkw 0x42898ed164dc3b1c 0x090a263b459370ec 0xf38fbff1fcfc3e3b 0xfbce3effc7f3f0f8

def z890 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33087f8f1cf331f1 0x34cc21fe3c73ccc7

def z891 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xf38f87f1fcfc3e3f 0xffce3e1fc7f3f0f8

def z892 : W := mkw 0xeaa00000da6a8000 0x03aa80000369aa00 0xfcb00001ffffc027 0x9ff2c00007ffff00

def z893 : W := mkw 0x428982c16058280c 0x090a260b058160a0 0xc38f87f1e0703e3b 0xfb0e3e1fc781c0f8

def z894 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33487f8f1ffff1fd 0xbccd21fe3c7fffc7

def z895 : W := mkw 0x4281134800000000 0x010a044d20000000 0xc38ffffe0000001b 0xe30e3ffff8000000

def z896 : W := mkw 0xac1ee825b7002da0 0x12b07ba096dc00b6 0xfcfffc7fff8fffff 0xfff3fff1fffe3fff

def z897 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x3f487f8f1ff331ff 0xbcfd21fe3c7fccc7

def z898 : W := mkw 0xfbe01108da6a8000 0x03ef80442369aa00 0xfff0780fffffc02f 0x9fffc1e03fffff00

def z899 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xf00ff801fc003ff5 0xd7c03fe007f000ff

def z900 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xfff04001fffff1ff 0x9fffc10007ffffc7

def z901 : W := mkw 0xa8000000da6a8000 0x02a000000369aa00 0xfcf00001ffffc02f 0x9ff3c00007ffff00

def z902 : W := mkw 0x53f1177e48efd251 0x214fc45df923bf49 0x03f007fe00ffc008 0x200fc01ff803ff00

def z903 : W := mkw 0xac2ee801b700ada0 0x12b0bba006dc02b6 0xfc3ff801ff00fff7 0xdff0ffe007fc03ff

def z904 : W := mkw 0xfff7736c9a228000 0x23ffddcdb2688a00 0xffffffff1ff3c03f 0xf7fffffffc7fcf00

def z905 : W := mkw 0x00088c936dff7fff 0x0c0022324db7fdff 0x00000001ffffffe0 0x1c00000007ffffff

def z906 : W := mkw 0xeeb7736c00000000 0x23baddcdb0000000 0xc00ffffe00000010 0x63003ffff8000000

def z907 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33087f8f1cf031f9 0xb0cc21fe3c73c0c7

def z908 : W := mkw 0x1140190a0c230142 0x0445006428308c05 0x33487f8f1cf301fd 0xb4cd21fe3c73cc07

def z909 : W := mkw 0x155c59bd0d3667ab 0x04557166f434d99e 0x3fbc3bf11f7cce03 0x58fef0efc47df338

def z910 : W := mkw 0x1148198b0c33214a 0x044520662c30cc85 0x33487b8f1c7331f5 0x94cd21ee3c71ccc7

def z911 : W := mkw 0xfbe88c93feffbb5e 0x0fefa2324ffbfeed 0xfff00001ffffffef 0x9fffc00007ffffff

def z912 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33487f8e1cf331dc 0x24cd21fe3873ccc7

def z913 : W := mkw 0x57f7736c486a8000 0x215fddcdb121aa00 0x03fffffe00ffc018 0x600ffffff803ff00

def z914 : W := mkw 0x428982d1605c2a0c 0x090a260b458170a8 0xc38f83f1e0fc0e2b 0xdb0e3e0fc783f038

def z915 : W := mkw 0xfff7736c010004a0 0x23ffddcdb0040012 0xfffffffe03000e1f 0xebfffffff80c0038

def z916 : W := mkw 0x57d7736c00000000 0x215f5dcdb0000000 0xf3cffffe0000001f 0xe3cf3ffff8000000

def z917 : W := mkw 0xfff7736cda6a8000 0x23ffddcdb369aa00 0xfffffffe1fffc01f 0xe7fffffff87fff00

def z918 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33487b8f1cf331e5 0x14cd21ee3c73ccc7

def z919 : W := mkw 0x1577736c00000000 0x2055ddcdb0000000 0x007ffffe00000010 0x6001fffff8000000

def z920 : W := mkw 0x57f7736c00000000 0x215fddcdb0000000 0xc3fffffe0000001b 0xe30ffffff8000000

def z921 : W := mkw 0x42898ed364dd3b5c 0x090a263b4d9374ed 0xf3cffffffcff3fff 0xffcf3ffffff3fcff

def z922 : W := mkw 0x1557736c00000000 0x20555dcdb0000000 0x034ffffe00000018 0x600d3ffff8000000

def z923 : W := mkw 0x428982d1605c2a0c 0x090a260b458170a8 0xc38f83f1e07c3e33 0xdb0e3e0fc781f0f8

def z924 : W := mkw 0x041ddfff25957fff 0x0c10777ffc9655ff 0x000ffffe00003fd0 0x60003ffff80000ff

def z925 : W := mkw 0x00088c93bfb77ffb 0x140022324efeddff 0x00000001ffffffe0 0x1c00000007ffffff

def z926 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xf38ffffe0000001b 0xe3ce3ffff8000000

def z927 : W := mkw 0x4697736c40480000 0x211a5dcdb1012000 0xc38fffffe0fc003b 0xfb0e3fffff83f000

def z928 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xff0fff81ff003fff 0xfffc3ffe07fc00ff

def z929 : W := mkw 0xac1ee825b7006da1 0x12b07ba096dc01b6 0xfc3ff801ff00fff7 0xdff0ffe007fc03ff

def z930 : W := mkw 0x00088c932cb73b5e 0x0c0022324cb2dced 0x000000011cf33fe0 0x140000000473ccff

def z931 : W := mkw 0xfbe99bc9fe7aa90e 0x0fefa66f27f9eaa4 0xf30bbb81fc700001 0x13cc2eee07f1c000

def z932 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfc4ffc0fff003fff 0xfff13ff03ffc00ff

def z933 : W := mkw 0xfbe3334800000000 0x23ef8ccd20000000 0xf3cffffe0000001f 0xe3cf3ffff8000000

def z934 : W := mkw 0xac37736c00000000 0x22b0ddcdb0000000 0x0c3ffffe00000010 0x6030fffff8000000

def z935 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33f87f8f1cfff1fd 0xb4cfe1fe3c73ffc7

def z936 : W := mkw 0x4697736c00000000 0x211a5dcdb0000000 0xc08ffffe00000012 0x63023ffff8000000

def z937 : W := mkw 0xfbe33348da6a8000 0x23ef8ccd2369aa00 0xfffbff8fffffc03f 0xbfffeffe3fffff00

def z938 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0cf4447e038fffdc 0x6433d111f80e3fff

def z939 : W := mkw 0xbd77736c00000000 0x22f5ddcdb0000000 0x300ffffe00000010 0x60c03ffff8000000

def z940 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xffffffff00f0003f 0xf3fffffffc03c000

def z941 : W := mkw 0xfff7736cd2480000 0x23ffddcdb3492000 0xfffffffffffc003f 0xfffffffffffff000

def z942 : W := mkw 0xfff7736c92000000 0x23ffddcdb2480000 0xffffffffff8fc03f 0xfffffffffffe3f00

def z943 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xfff0440fffffc03f 0xbfffc1103fffff00

def z944 : W := mkw 0xfbe33348da6a8000 0x23ef8ccd2369aa00 0xffffbff1ffffc03f 0xfffffeffc7ffff00

def z945 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33487f8f1cf331d9 0x30cd21fe3c73ccc7

def z946 : W := mkw 0x53f3336c00000000 0x214fcccdb0000000 0x03fbbffe00000008 0x200feefff8000000

def z947 : W := mkw 0xac066000930004a0 0x02b01980024c0012 0xfc0ff801ff003ff7 0xdff03fe007fc00ff

def z948 : W := mkw 0xfff7736c40480000 0x23ffddcdb1012000 0xfffffffe00fc001f 0xe3fffffff803f000

def z949 : W := mkw 0x0013336c00000000 0x20004ccdb0000000 0x000bbffe00000000 0x20002efff8000000

def z950 : W := mkw 0xfbe11348da6a8000 0x23ef844d2369aa00 0xfff00381ffffc02f 0x9fffc00e07ffff00

def z951 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xfffffffe008fc01f 0xe3fffffff8023f00

def z952 : W := mkw 0xfff7736cda6a8000 0x23ffddcdb369aa00 0xffffffffff70003f 0xfffffffffffdc000

def z953 : W := mkw 0x1557736c00000000 0x20555dcdb0000000 0x304ffffe00000014 0x60c13ffff8000000

def z954 : W := mkw 0xfff7736c9a228000 0x23ffddcdb2688a00 0xffffffffff03c03f 0xfffffffffffc0f00

def z955 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xfff40471ffffc03f 0xffffd011c7ffff00

def z956 : W := mkw 0x4697736c00000000 0x211a5dcdb0000000 0xc30ffffe00000011 0x630c3ffff8000000

def z957 : W := mkw 0xfff7736c486a8000 0x23ffddcdb121aa00 0xfffffffe0070001f 0xe3fffffff801c000

def z958 : W := mkw 0xfff7736c08228000 0x23ffddcdb0208a00 0xfffffffe0003c01f 0xe3fffffff8000f00

def z959 : W := mkw 0xfff7736c010004a0 0x23ffddcdb0040012 0xfffffffe00003fdf 0xe3fffffff80000ff

def z960 : W := mkw 0xfff7736cda6a8000 0x23ffddcdb369aa00 0xfffffffeff0fc01f 0xeffffffffbfc3f00

def z961 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfc07f801ff003fe6 0x5ff01fe007fc00ff

def z962 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc38fc7f1e0fc3fff 0xff0e3f1fc783f0ff

def z963 : W := mkw 0x42898ed164dc3b1c 0x090a263b459370ec 0xc38ffff1e0fc3ffb 0xfb0e3fffc783f0ff

def z964 : W := mkw 0xfbe01108da6a8000 0x03ef80442369aa00 0xfff83b81ffffc02f 0x9fffe0ee07ffff00

def z965 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfc0bf801ff003fe5 0x1ff02fe007fc00ff

def z966 : W := mkw 0xeeb76274d34cc6a1 0x23badd89d34d331a 0xccb78070e30cce02 0x4b32de01c38c3338

def z967 : W := mkw 0x114819890c32210a 0x044520662430c884 0x33487f8f1c7031fd 0xb4cd21fe3c71c0c7

def z968 : W := mkw 0xac1ee825b7002da0 0x12b07ba096dc00b6 0xfcbff871ff003ff7 0xdff2ffe1c7fc00ff

def z969 : W := mkw 0xeeb7e274f34c0ea4 0x3bbadf89d3cd303a 0xccb78070e30c0e02 0x4b32de01c38c3038

def z970 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xfffffffe00003e3f 0xebfffffff80000f8

def z971 : W := mkw 0xfbe10240da6a8000 0x03ef84090369aa00 0xfff78071ffffc02f 0xdfffde01c7ffff00

def z972 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xcffffffe0000001a 0x633ffffff8000000

def z973 : W := mkw 0xeeb7e264f3488ca0 0x33badf8993cd2232 0xccb78070e30cce02 0x4b32de01c38c3338

def z974 : W := mkw 0xeeb7736c00000000 0x23baddcdb0000000 0xfcbffffe00000017 0xe3f2fffff8000000

def z975 : W := mkw 0x4289824160482800 0x010a2609058120a0 0xc38f87f1e0fc3e3b 0xfb0e3e1fc783f0f8

def z976 : W := mkw 0x428182d0605c0a0c 0x090a060b41817028 0xc38783f0e07c0e02 0x4b0e1e0fc381f038

def z977 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0xf34fff8f1cf331ff 0xf7cd3ffe3c73ccc7

def z978 : W := mkw 0x4697736c00000000 0x211a5dcdb0000000 0xcffffffe0000001f 0xe33ffffff8000000

def z979 : W := mkw 0xfbf3336c00000000 0x23efcccdb0000000 0xf3ffbffe0000001b 0xe3cffefff8000000

def z980 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33cc7fff1cf331ff 0xf4cf31fffc73ccc7

def z981 : W := mkw 0x11401d8a0cb3115a 0x044500762832cc45 0x33487f8e1cf301dd 0xa4cd21fe3873cc07

def z982 : W := mkw 0x4697736c00000000 0x211a5dcdb0000000 0x038ffffe00000018 0x600e3ffff8000000

def z983 : W := mkw 0xa80aa801b6002900 0x12a02aa006d800a4 0xf00ff801fc003ff7 0xdfc03fe007f000ff

def z984 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xfffbfffe0000000d 0x23ffeffff8000000

def z985 : W := mkw 0xfff7736c010004a0 0x23ffddcdb0040012 0xfffffffe030001df 0xe7fffffff80c0007

def z986 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xffffffffe000003f 0xfbffffffff800000

def z987 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xfff00001ffffc00d 0x17ffc00007ffff00

def z988 : W := mkw 0x0000041200851250 0x0000001048021449 0x0cf4447e038ffffe 0xec33d111f80e3fff

def z989 : W := mkw 0x1557736c00000000 0x20555dcdb0000000 0x330ffffe00000011 0x60cc3ffff8000000

def z990 : W := mkw 0x11489d8b2cb3395a 0x044522762cb2cce5 0xf34bff8ffcf331fd 0xb7cd2ffe3ff3ccc7

def z991 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0xf3487f8ffcf331ff 0xbfcd21fe3ff3ccc7

def z992 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc3cf87f1e0ff3e3f 0xff0f3e1fc783fcf8

def z993 : W := mkw 0xbd76712e9b23c4e1 0x22f5d9c4ba6c8f13 0x3c70780e1f03c1c4 0x04f1c1e0387c0f07

def z994 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xff0ff801fff03fff 0xdffc3fe007ffc0ff

def z995 : W := mkw 0xfff7736c40480000 0x23ffddcdb1012000 0xfffffffee00c001f 0xebfffffffb803000

def z996 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xcf8f87f1e3fc3e3f 0xff3e3e1fc78ff0f8

def z997 : W := mkw 0x041feef725957ffd 0x18107fbbdc9655ff 0x000ffffe00003fd0 0x60003ffff80000ff

def z998 : W := mkw 0x0417736c00000000 0x20105dcdb0000000 0x004ffffe0000001c 0xe0013ffff8000000

def z999 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33087f8f1c7031f5 0xb4cc21fe3c71c0c7

def z1000 : W := mkw 0x428986c120903818 0x010a261b048240e0 0xc38f87f1e0f03e3b 0xfb0e3e1fc783c0f8

def z1001 : W := mkw 0x11481d8904903118 0x00452076241240c4 0x33487f8f1cf031fd 0xb4cd21fe3c73c0c7

def z1002 : W := mkw 0xfff7736c08220000 0x23ffddcdb0208800 0xfffffffe1c03001f 0xe7fffffff8700c00

def z1003 : W := mkw 0x041444b6019556f9 0x00105112d806555b 0x0ff447fe03fffffe 0xec3fd11ff80fffff

def z1004 : W := mkw 0x1557736c00000000 0x20555dcdb0000000 0x3ffffffe0000001f 0xe0fffffff8000000

def z1005 : W := mkw 0x000986d120943a1c 0x0800261b448250e8 0xc30f87f1e0f03e3b 0xfb0c3e1fc783c0f8

def z1006 : W := mkw 0xfff7736c486a8000 0x23ffddcdb121aa00 0xfffffffe03ffc03f 0xeffffffff80fff00

def z1007 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xfff80781ffffc03f 0xbfffe01e07ffff00

def z1008 : W := mkw 0x42800000da6a8000 0x010a00000369aa00 0xcff00001ffffc02f 0x9f3fc00007ffff00

def z1009 : W := mkw 0x428186d060dc1a1c 0x090a061b41837068 0xc38787f1e0fc0e2b 0xfb0e1e1fc783f038

def z1010 : W := mkw 0xfff7736c92000000 0x23ffddcdb2480000 0xfffffffee300001f 0xebfffffffb8c0000

def z1011 : W := mkw 0x1141134800000000 0x0045044d20000000 0x334ffffe0000001d 0xe0cd3ffff8000000

def z1012 : W := mkw 0xfff7736cda6a8000 0x23ffddcdb369aa00 0xfffffffffcffc01f 0xf3fffffffff3ff00

def z1013 : W := mkw 0xa80aa801b7002da0 0x12a02aa006dc00b6 0xf00fb801ff003ff3 0xdfc03ee007fc00ff

def z1014 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xcff00001ffffc02a 0x1f3fc00007ffff00

def z1015 : W := mkw 0x1148198b0c33214a 0x044520662c30cc85 0x33487b8f1cf301ed 0x94cd21ee3c73cc07

def z1016 : W := mkw 0xfbf3336c00000000 0x23efcccdb0000000 0xfffbbffe0000000f 0xa3ffeefff8000000

def z1017 : W := mkw 0xac17736c00000000 0x22b05dcdb0000000 0x3c0ffffe00000014 0x60f03ffff8000000

def z1018 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xcfbf87f1e3fcfe3b 0xfb3efe1fc78ff3f8

def z1019 : W := mkw 0x11401d8a0cb3115a 0x044500762832cc45 0x33407f8e1cf331fc 0xa4cd01fe3873ccc7

def z1020 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0x3ffffffe0000001c 0x60fffffff8000000

def z1021 : W := mkw 0x04144436018556f1 0x00105110d806155b 0xccf4447fe38fffff 0xff33d111ff8e3fff

def z1022 : W := mkw 0xfbe10240da6a8000 0x03ef84090369aa00 0xfffb8381ffffc02f 0x9fffee0e07ffff00

def z1023 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0cf4407e038fffe6 0x4c33d101f80e3fff

def z1024 : W := mkw 0x428982d1605c2a0c 0x090a260b458170a8 0xc30f83f1e0700e01 0x530c3e0fc781c038

def z1025 : W := mkw 0x53e00000da6a8000 0x014f80000369aa00 0x0ff00001ffffc02e 0x9c3fc00007ffff00

def z1026 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xfffffffe000031ff 0xe7fffffff80000c7

def z1027 : W := mkw 0xfff7736cd2488000 0x23ffddcdb3492200 0xfffffffee000001f 0xe3fffffffb800000

def z1028 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33487f8f1c7331d5 0x34cd21fe3c71ccc7

def z1029 : W := mkw 0xfbe00000da6a8000 0x03ef80000369aa00 0xfff87801ffffc03f 0x9fffe1e007ffff00

def z1030 : W := mkw 0xbd76792c9f2285a0 0x32f5d9e4b27c8a16 0x3c70780e1f03c1c4 0x04f1c1e0387c0f07

def z1031 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xf00ff801ff003ff1 0x5fc03fe007fc00ff

def z1032 : W := mkw 0xbd57736c00000000 0x22f55dcdb0000000 0xff4ffffe0000001f 0xe3fd3ffff8000000

def z1033 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfc8ffc71ff003fff 0xfff23ff1c7fc00ff

def z1034 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x3ff87f8f1cf331ff 0xb4ffe1fe3c73ccc7

def z1035 : W := mkw 0x428986d360dd3a5c 0x090a261b4d8374e9 0xcfffc7ffe3ffffff 0xff3fff1fff8fffff

def z1036 : W := mkw 0x11481d9b0cb7335a 0x044520766c32dccd 0x33c87fff1cff31fd 0xb4cf21fffc73fcc7

def z1037 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33487f8f1c7031dd 0xb0cd21fe3c71c0c7

def z1038 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfc0fb801ff003fe3 0x5ff03ee007fc00ff

def z1039 : W := mkw 0xfbe23108da6a8000 0x23ef88c42369aa00 0xfff03801ffffc02f 0x9fffc0e007ffff00

def z1040 : W := mkw 0x0417736c00000000 0x20105dcdb0000000 0x0cfffffe038fc03e 0xec33fffff80e3f00

def z1041 : W := mkw 0x04144036010546e1 0x00105100d804151b 0x0cf4407e030ffff6 0xcc33d101f80c3fff

def z1042 : W := mkw 0x0417736c00000000 0x20105dcdb0000000 0x0cbffffe00000012 0x6032fffff8000000

def z1043 : W := mkw 0xfff7736c930004a0 0x23ffddcdb24c0012 0xffffffffff003fff 0xfffffffffffc00ff

def z1044 : W := mkw 0x04166436018556f1 0x00105990d806155b 0x0cfffc7e038ffffe 0xec33fff1f80e3fff

def z1045 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0ffc47fe038fffff 0xec3ff11ff80e3fff

def z1046 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfcfff801ff003fff 0xdff3ffe007fc00ff

def z1047 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0cf4447e038fffda 0x6833d111f80e3fff

def z1048 : W := mkw 0xfff7736c930004a0 0x33ffddcdb24c0012 0xfffffffe0300001f 0xe3fffffff80c0000

def z1049 : W := mkw 0xfbe1134800000000 0x03ef844d20000000 0xfffffffe0000001f 0xe3fffffff8000000

def z1050 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xfffffffe0303c01f 0xe7fffffff80c0f00

def z1051 : W := mkw 0x0417736c00000000 0x20105dcdb0000000 0x300ffffe00000015 0xe0c03ffff8000000

def z1052 : W := mkw 0x53c00000486a0000 0x014f00000121a800 0xfff00001ffffc02f 0x9fffc00007ffff00

def z1053 : W := mkw 0x11481d8b0cb3315a 0x044520762c32ccc5 0x33407f8f1cf331ec 0x34cd01fe3c73ccc7

def z1054 : W := mkw 0xfff7736cdb6a84a0 0x23ffddcdb36daa12 0xffffffffffffffff 0xffffffffffffffff

def z1055 : W := mkw 0xac17736c00000000 0x22b05dcdb0000000 0xfcfffffe0000001f 0xe3f3fffff8000000

def z1056 : W := mkw 0x11489d9b2cb73b5a 0x044522766cb2dced 0xf3cffffffcff3fff 0xffcf3ffffff3fcff

def z1057 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xf38ffff1e0fc3e3f 0xfbce3fffc783f0f8

def z1058 : W := mkw 0x1148198b0c33214a 0x044520662c30cc85 0x33087b8f1c7001c1 0x10cc21ee3c71c007

def z1059 : W := mkw 0xac17736c92000000 0x22b05dcdb2480000 0xfc0fffffff000037 0xfff03ffffffc0000

def z1060 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xfcfffffe00000016 0x63f3fffff8000000

def z1061 : W := mkw 0xfbf3336cda6a8000 0x23efcccdb369aa00 0xf3fbbffffcffc009 0x33cfeefffff3ff00

def z1062 : W := mkw 0xffc7734800000000 0x03ff1dcd20000000 0xffcffffe0000001f 0xe3ff3ffff8000000

def z1063 : W := mkw 0x53f1136c00000000 0x214fc44db0000000 0xf3fffffe0000001f 0xe3cffffff8000000

def z1064 : W := mkw 0xfff7736c00000000 0x23ffddcdb0000000 0xff7ffffe00000015 0x63fdfffff8000000

def z1065 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfc7ff801ff03fff7 0xdff1ffe007fc0fff

def z1066 : W := mkw 0xfff7736cd2488000 0x23ffddcdb3492200 0xfffffffee38fc03f 0xeffffffffb8e3f00

def z1067 : W := mkw 0xac0ee801b7002da0 0x12b03ba006dc00b6 0xfc0ff801ff003fd5 0x57f03fe007fc00ff

def z1068 : W := mkw 0xfff7736c9a228000 0x23ffddcdb2688a00 0xfffffffe1c00001f 0xe3fffffff8700000

def z1069 : W := mkw 0x428986d160dc3a1c 0x090a261b458370e8 0xc38f87f1e0703e1b 0xf30e3e1fc781c0f8

def z1070 : W := mkw 0x04144436018556f1 0x00105110d806155b 0x0cf4047e038fffea 0x6c33d011f80e3fff

def z1071 : W := mkw 0x0417736c00000000 0x20105dcdb0000000 0x00fffffe00000018 0x6003fffff8000000

def z1072 : W := mkw 0x428186d060dc1a1c 0x090a061b41837068 0xc38787f0e0fc3e3a 0xeb0e1e1fc383f0f8

def z1073 : W := mkw 0x11481d9b0cb7735b 0x044520766c32ddcd 0x33487f8f1cfff1fd 0xb4cd21fe3c73ffc7

def z1074 : W := mkw 0xbd56792e9f2345e3 0x16f559e4ba7c8d17 0x3c70780e1f03c1c4 0x04f1c1e0387c0f07

def z1075 : W := mkw 0x0008849120943a18 0x00002212448250e8 0xc38f87f1e0fc3e3b 0xfb0e3e1fc783f0f8

def z1076 : W := mkw 0x11481d9b0cb7335a 0x044520766c32dccd 0x334c7fff1cf33ffd 0xf4cd31fffc73ccff

def z1077 : W := mkw 0xfff7736c486a8000 0x23ffddcdb121aa00 0xffffffffe0ffc03f 0xfbffffffff83ff00

def z1078 : W := mkw 0xea800000d2480000 0x03aa000003492000 0xfff00001ffffc02f 0x9fffc00007ffff00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z5,z8]),(0,[z0,z1,z9,z3,z4,z5,z6])],[(1,[z0,z1,z10,z4,z5,z6]),(0,[z0,z1,z3,z11,z5,z6,z12]),(0,[z0,z1,z13,z3,z4,z5,z6]),(0,[z0,z14,z3,z4,z5,z6,z15]),(0,[z0,z1,z3,z4,z16,z5,z17]),(0,[z0,z1,z18,z3,z4,z5,z6])],[(0,[z0,z19,z20,z3,z4,z5,z6]),(1,[z0,z21,z3,z4,z5,z6]),(0,[z22,z0,z1,z3,z4,z5,z6])],[(0,[z0,z23,z1,z3,z4,z5,z24]),(0,[z0,z1,z25,z3,z4,z5,z6]),(0,[z26,z0,z1,z3,z4,z5,z6])],[(0,[z0,z23,z1,z3,z27,z4,z5]),(0,[z0,z1,z28,z29,z4,z5,z6]),(0,[z0,z1,z3,z30,z4,z5,z6]),(0,[z0,z1,z3,z4,z31,z5,z6])],[(0,[z0,z32,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z33,z4,z5,z6]),(0,[z0,z1,z3,z34,z4,z5,z6]),(0,[z35,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z36,z4,z5,z6])],[(0,[z37,z0,z1,z3,z4,z5,z6]),(0,[z0,z38,z1,z3,z4,z5,z6]),(0,[z39,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z40,z0,z1,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z4,z5,z6]),(0,[z42,z0,z43,z3,z4,z5,z6]),(0,[z44,z0,z1,z3,z4,z5,z6]),(0,[z0,z45,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z46,z5,z6]),(0,[z47,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z48,z5,z6]),(0,[z0,z49,z1,z3,z4,z5,z6])],[(0,[z0,z1,z50,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z51]),(0,[z1,z3,z4,z5,z8,z6,z24]),(0,[z0,z1,z3,z4,z5,z6,z15]),(0,[z0,z1,z3,z4,z5,z6,z52])],[(0,[z0,z1,z3,z4,z53,z5,z6]),(0,[z0,z1,z3,z4,z54,z5,z6]),(0,[z0,z23,z55,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z56,z5,z6]),(1,[z57,z1,z3,z4,z58,z6]),(0,[z0,z1,z59,z3,z4,z5,z6]),(0,[z60,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z61,z5,z62,z6]),(0,[z0,z1,z3,z63,z4,z5,z6]),(0,[z0,z23,z1,z3,z4,z6,z17])],[(0,[z64,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z5,z65,z6]),(0,[z66,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z58,z5,z6]),(1,[z0,z1,z67,z4,z5,z6]),(0,[z68,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z69,z5,z6]),(0,[z0,z1,z70,z3,z4,z71,z6])],[(0,[z72,z64,z1,z3,z4,z5,z6]),(0,[z73,z0,z1,z3,z4,z5,z6]),(0,[z74,z0,z1,z3,z4,z5,z17]),(0,[z75,z0,z1,z3,z4,z5,z6]),(0,[z44,z0,z23,z1,z3,z4,z5])]],
   [[(0,[z0,z23,z76,z1,z3,z4,z5]),(0,[z77,z0,z1,z3,z4,z5,z6]),(0,[z78,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z79,z5,z17]),(0,[z80,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z81,z5,z6]),(0,[z0,z1,z3,z82,z4,z5,z6]),(0,[z0,z83,z1,z3,z4,z5,z6])],[(0,[z84,z0,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z8,z6]),(0,[z0,z1,z3,z4,z85,z5,z17]),(0,[z0,z1,z3,z4,z86,z5,z6]),(0,[z0,z23,z1,z70,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z87,z6]),(0,[z0,z88,z1,z3,z4,z5,z6])],[(0,[z0,z1,z89,z3,z4,z5,z6]),(0,[z0,z1,z3,z27,z4,z5,z17]),(0,[z0,z1,z90,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z91,z5,z6]),(0,[z0,z1,z3,z92,z4,z5,z6]),(0,[z0,z1,z3,z4,z93,z5,z6]),(0,[z0,z1,z94,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z95,z5,z6]),(0,[z0,z1,z96,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z97]),(0,[z98,z1,z3,z4,z5,z6,z24]),(0,[z0,z1,z3,z4,z5,z99,z6]),(0,[z100,z0,z55,z3,z4,z5,z6]),(0,[z101,z0,z1,z3,z4,z5,z6])],[(0,[z0,z3,z4,z54,z5,z102,z6]),(0,[z0,z1,z70,z3,z4,z5,z103]),(0,[z0,z1,z3,z4,z5,z6,z12])],[(0,[z104,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z67,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z105,z5,z6])],[(0,[z0,z1,z106,z3,z4,z5,z6]),(1,[z0,z107,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z108,z5,z6]),(0,[z0,z23,z1,z109,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z110]),(0,[z111,z0,z1,z3,z4,z5,z6]),(0,[z0,z112,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z17,z12]),(0,[z0,z1,z3,z4,z113,z5,z6])],[(0,[z114,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z115,z4,z5,z6]),(0,[z116,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z117,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z118,z6]),(0,[z0,z1,z3,z4,z119,z5,z6]),(1,[z120,z0,z1,z4,z85,z6]),(0,[z0,z1,z3,z121,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z122])]],
   [[(0,[z123,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z124]),(0,[z0,z23,z1,z3,z4,z79,z5]),(0,[z0,z1,z3,z125,z4,z5,z6]),(1,[z0,z14,z3,z4,z5,z15]),(0,[z126,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z127,z6]),(0,[z0,z128,z1,z3,z4,z58,z5]),(0,[z0,z43,z19,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z129,z5,z6])],[(1,[z130,z0,z1,z3,z4,z5]),(0,[z130,z0,z1,z3,z29,z4,z5]),(0,[z131,z0,z1,z3,z4,z5,z6])],[(0,[z132,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z133]),(0,[z0,z1,z134,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z135,z5,z6]),(0,[z136,z0,z19,z3,z4,z5,z6]),(0,[z137,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z138,z4,z85,z5])],[(0,[z0,z1,z139,z3,z4,z5,z6]),(0,[z140,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z141,z4,z142,z5,z6])],[(0,[z72,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z143,z5,z6]),(0,[z144,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z145])],[(0,[z0,z1,z3,z4,z5,z6,z146]),(0,[z0,z1,z3,z4,z147,z5,z6]),(0,[z0,z23,z1,z3,z4,z5,z102]),(0,[z123,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z148,z4,z5,z6])],[(0,[z149,z0,z1,z3,z4,z5,z6]),(0,[z150,z0,z1,z3,z4,z6,z17]),(0,[z151,z0,z1,z3,z142,z5,z6]),(0,[z0,z23,z1,z152,z3,z4,z5]),(0,[z123,z0,z23,z1,z3,z4,z5])]],
   [[(0,[z150,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z153,z5,z6])],[(0,[z154,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z155,z5,z6]),(0,[z0,z156,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z157,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z158,z6]),(0,[z0,z3,z159,z4,z79,z5,z6]),(0,[z74,z0,z1,z3,z4,z5,z15]),(0,[z160,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z63,z5,z6,z12]),(0,[z0,z1,z3,z161,z4,z5,z6])],[(0,[z0,z1,z3,z4,z162,z5,z6]),(0,[z163,z0,z1,z3,z4,z5,z6]),(0,[z164,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z20,z3,z4,z5,z6]),(0,[z140,z0,z23,z1,z3,z4,z5])],[(1,[z0,z1,z165,z4,z5,z6]),(0,[z0,z1,z3,z4,z166,z5,z6]),(0,[z0,z1,z3,z4,z167,z5,z6]),(0,[z168,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z169,z4,z5,z6])],[(0,[z0,z1,z28,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z5,z170,z6])],[(0,[z171,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z109,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z172,z6,z17]),(0,[z0,z23,z1,z173,z3,z4,z5])]],
   [[(0,[z174,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z175,z4,z5,z6]),(0,[z98,z0,z1,z3,z4,z5,z24]),(0,[z0,z1,z3,z4,z176,z5,z6]),(0,[z0,z1,z3,z4,z5,z177,z6])],[(0,[z0,z1,z109,z3,z4,z85,z6]),(0,[z0,z1,z3,z178,z4,z5,z6])],[(1,[z0,z179,z3,z4,z5,z6]),(0,[z180,z0,z1,z3,z143,z5,z6]),(0,[z0,z1,z3,z4,z5,z181,z6]),(1,[z0,z1,z3,z175,z5,z6]),(0,[z0,z1,z173,z3,z4,z5,z6])],[(0,[z182,z0,z1,z3,z4,z5,z6])],[(0,[z183,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z184,z5,z6]),(0,[z42,z0,z1,z3,z79,z5,z6]),(0,[z0,z1,z3,z4,z185,z5,z6])],[(0,[z1,z3,z4,z58,z5,z186,z6]),(0,[z0,z187,z1,z3,z4,z5,z6]),(0,[z188,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z189,z4,z5,z6]),(0,[z0,z190,z1,z3,z4,z5,z6]),(0,[z0,z43,z1,z3,z79,z5,z6]),(0,[z0,z14,z1,z70,z3,z4,z5]),(0,[z0,z1,z3,z191,z4,z5,z6])],[(0,[z192,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z11,z4,z5,z6]),(0,[z0,z1,z3,z4,z193,z5,z6]),(0,[z0,z1,z3,z194,z4,z5,z6]),(0,[z0,z195,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z103]),(0,[z0,z1,z3,z63,z4,z5,z12]),(0,[z0,z1,z3,z4,z196,z5,z17])]],
   [[(0,[z0,z1,z197,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z198,z6]),(0,[z0,z1,z3,z4,z199,z5,z6])],[(0,[z0,z200,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z201,z6]),(0,[z0,z1,z3,z159,z4,z5,z17]),(0,[z202,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z203,z4,z5,z6]),(1,[z204,z0,z23,z1,z3,z4])],[(0,[z205,z206,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z207,z5,z6]),(0,[z120,z0,z1,z28,z4,z5,z6]),(0,[z98,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z208,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z209,z6])],[(0,[z0,z1,z3,z4,z5,z6,z210]),(0,[z0,z23,z1,z3,z159,z4,z5]),(0,[z0,z1,z3,z4,z5,z211,z6])],[(0,[z0,z1,z3,z11,z4,z5,z17]),(0,[z57,z0,z1,z3,z4,z6,z17]),(0,[z0,z20,z3,z29,z4,z5,z6]),(0,[z212,z0,z1,z3,z4,z5,z6]),(0,[z151,z0,z213,z3,z4,z5,z6]),(0,[z214,z0,z1,z3,z4,z5,z6]),(1,[z214,z0,z1,z4,z86,z5]),(0,[z215,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z216,z3,z4,z5,z6]),(0,[z217,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z218,z5,z6]),(0,[z0,z1,z3,z4,z5,z219,z6]),(0,[z220,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z221,z6]),(0,[z0,z1,z3,z222,z4,z5,z17])],[(0,[z0,z1,z3,z223,z4,z5,z6]),(1,[z0,z1,z96,z4,z5,z6]),(0,[z0,z1,z3,z4,z224,z5,z6]),(1,[z0,z1,z3,z4,z225,z6])],[(0,[z0,z1,z3,z4,z5,z226,z6]),(0,[z0,z1,z3,z143,z5,z6,z12]),(0,[z0,z1,z3,z4,z5,z227,z6]),(0,[z0,z1,z3,z228,z4,z5,z6])]],
   [[(0,[z0,z1,z229,z3,z4,z5,z6]),(0,[z0,z23,z1,z3,z4,z58,z5]),(0,[z0,z1,z3,z230,z4,z5,z6]),(0,[z0,z1,z231,z20,z4,z5,z6]),(1,[z0,z1,z3,z4,z172,z17])],[(0,[z0,z1,z3,z4,z232,z5,z6]),(0,[z98,z0,z23,z1,z3,z4,z5]),(0,[z233,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z234,z5,z6]),(0,[z0,z1,z3,z4,z5,z235,z6]),(0,[z236,z0,z1,z3,z4,z5,z6]),(0,[z214,z0,z1,z3,z4,z5,z17]),(1,[z0,z1,z3,z237,z4,z5]),(1,[z0,z1,z3,z4,z5,z17])],[(0,[z0,z1,z3,z4,z5,z238,z6]),(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z214,z0,z23,z1,z3,z4,z5]),(0,[z215,z0,z23,z1,z3,z4,z5]),(0,[z0,z1,z3,z239,z4,z5,z6])],[(0,[z0,z1,z3,z240,z4,z5,z6]),(0,[z0,z1,z3,z4,z241,z5,z6]),(0,[z100,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z85,z17]),(0,[z0,z1,z3,z4,z5,z17,z17])],[(0,[z0,z1,z3,z4,z5,z6,z242]),(1,[z0,z1,z3,z4,z5,z243])],[(1,[z0,z1,z3,z244,z5,z6]),(0,[z0,z1,z245,z3,z4,z5,z6]),(0,[z246,z0,z1,z3,z4,z5,z17])],[(0,[z0,z1,z3,z4,z247,z5,z6])]],
   [[(0,[z150,z0,z1,z3,z4,z186,z6]),(0,[z0,z1,z3,z4,z8,z227,z6])],[(1,[z150,z0,z1,z3,z4,z17]),(0,[z0,z248,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z249,z5,z6]),(0,[z0,z1,z3,z4,z250,z5,z6])],[(1,[z0,z1,z3,z4,z251,z6]),(0,[z0,z1,z3,z252,z4,z5,z6]),(0,[z0,z23,z1,z3,z4,z153,z5])],[(0,[z0,z1,z3,z253,z4,z5,z6]),(0,[z254,z0,z1,z3,z4,z5,z6]),(0,[z255,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z256,z4,z5,z6]),(0,[z100,z0,z23,z1,z3,z4,z5]),(0,[z0,z1,z3,z257,z4,z5,z6]),(0,[z0,z1,z258,z3,z4,z5,z6]),(0,[z204,z0,z1,z3,z4,z172,z6]),(0,[z259,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z260,z5,z6]),(0,[z261,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z262,z6]),(0,[z263,z0,z1,z3,z4,z5,z6])],[(0,[z206,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z264,z4,z5,z6]),(0,[z150,z0,z107,z3,z4,z5,z6]),(1,[z57,z0,z1,z3,z4,z17]),(1,[z265,z0,z1,z3,z4,z6]),(0,[z0,z266,z1,z3,z4,z5,z6]),(0,[z0,z1,z20,z4,z142,z5,z6]),(0,[z0,z1,z3,z267,z4,z5,z6]),(0,[z0,z1,z109,z4,z5,z268,z6])],[(0,[z0,z269,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z270,z5,z6]),(0,[z271,z0,z1,z3,z4,z5,z6])],[(0,[z0,z55,z1,z3,z4,z5,z6]),(0,[z0,z1,z231,z3,z4,z5,z6]),(0,[z0,z1,z70,z3,z4,z86,z5]),(0,[z0,z23,z1,z3,z4,z86,z5])]],
   [[(0,[z0,z1,z20,z28,z4,z5,z6]),(0,[z272,z0,z1,z3,z4,z5,z6]),(0,[z0,z273,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z262,z5,z6]),(0,[z0,z1,z3,z274,z4,z5,z275])],[(0,[z0,z1,z3,z276,z4,z5,z6]),(0,[z277,z0,z1,z3,z4,z5,z6]),(0,[z259,z0,z1,z3,z4,z5,z17])],[(0,[z0,z1,z278,z3,z4,z5,z6]),(0,[z0,z1,z3,z141,z4,z5,z6]),(0,[z279,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z280,z5,z6]),(0,[z0,z1,z18,z3,z4,z5,z17])],[(1,[z64,z76,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z281,z6]),(0,[z0,z1,z3,z4,z244,z5,z6]),(0,[z0,z1,z3,z4,z5,z282,z6]),(0,[z0,z1,z3,z4,z283,z5,z6]),(0,[z151,z0,z1,z3,z141,z5,z6]),(0,[z284,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z274,z4,z5,z6])],[(0,[z206,z0,z23,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z285]),(0,[z0,z1,z3,z4,z5,z286,z6])],[(0,[z287,z0,z1,z3,z4,z5,z6]),(0,[z180,z0,z1,z3,z11,z5,z6]),(1,[z0,z1,z3,z4,z5,z52]),(0,[z0,z1,z3,z288,z4,z5,z6])],[(0,[z180,z0,z1,z3,z4,z5,z6]),(0,[z0,z289,z1,z3,z4,z5,z6]),(0,[z74,z0,z14,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z17,z15]),(0,[z0,z1,z3,z4,z290,z5,z6]),(0,[z0,z273,z23,z1,z3,z4,z5])]],
   [[(0,[z204,z57,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z291,z6]),(0,[z120,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z292,z5,z6]),(0,[z0,z23,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z293,z4,z5,z6]),(0,[z0,z294,z1,z3,z4,z5,z6])],[(0,[z295,z0,z1,z3,z4,z5,z6]),(1,[z98,z1,z3,z4,z5,z24]),(0,[z0,z1,z3,z296,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z297,z6]),(0,[z298,z0,z1,z3,z4,z5,z6]),(1,[z42,z0,z3,z79,z5,z6]),(1,[z0,z1,z3,z4,z54,z17]),(0,[z120,z0,z1,z3,z4,z85,z6])],[(0,[z205,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z299,z3,z4,z5,z6]),(0,[z0,z1,z300,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z301,z5,z6]),(0,[z0,z1,z3,z4,z5,z302,z6])],[(0,[z303,z0,z1,z3,z4,z5,z6]),(0,[z180,z0,z1,z3,z4,z5,z17]),(1,[z0,z128,z1,z3,z4,z5]),(0,[z0,z1,z3,z304,z4,z5,z24]),(0,[z0,z19,z1,z3,z4,z5,z6]),(0,[z100,z0,z1,z3,z4,z54,z6]),(0,[z0,z1,z3,z4,z54,z5,z17]),(0,[z0,z1,z70,z4,z5,z6,z103])],[(0,[z180,z0,z23,z1,z3,z4,z5]),(0,[z57,z0,z1,z3,z4,z186,z6]),(0,[z0,z1,z305,z3,z4,z5,z6]),(0,[z0,z1,z3,z63,z4,z5,z17])],[(0,[z0,z1,z3,z4,z5,z306,z6]),(1,[z0,z1,z3,z4,z5,z97]),(1,[z0,z1,z3,z4,z5,z307]),(0,[z0,z1,z3,z4,z5,z6,z307]),(0,[z0,z1,z3,z4,z5,z6,z308]),(0,[z120,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z309,z5,z6]),(0,[z0,z23,z1,z3,z4,z5,z17])],[(0,[z0,z1,z3,z4,z58,z5,z17]),(0,[z136,z0,z1,z20,z4,z5,z6]),(0,[z0,z310,z1,z3,z4,z5,z6]),(0,[z0,z1,z311,z3,z4,z5,z6]),(0,[z0,z23,z1,z3,z4,z5,z268]),(0,[z120,z0,z23,z1,z3,z4,z5]),(1,[z0,z1,z3,z4,z312,z5]),(0,[z0,z23,z23,z1,z3,z4,z5])]],
   [[(0,[z0,z313,z1,z3,z4,z5,z6]),(0,[z314,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z315,z5,z6]),(0,[z214,z0,z1,z70,z4,z5,z6])],[(0,[z0,z1,z3,z4,z316,z5,z6]),(0,[z0,z1,z3,z4,z5,z317,z6]),(0,[z205,z1,z3,z27,z4,z5,z6]),(1,[z0,z318,z3,z4,z5,z6]),(1,[z0,z1,z3,z319,z5,z6]),(0,[z0,z1,z3,z320,z4,z5,z6])],[(0,[z205,z0,z23,z1,z3,z4,z5]),(0,[z321,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z322,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z86,z5,z17])],[(0,[z0,z1,z89,z3,z4,z5,z17]),(0,[z100,z0,z76,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z124]),(0,[z150,z0,z1,z3,z184,z5,z6]),(0,[z0,z1,z3,z4,z5,z186,z6]),(0,[z0,z1,z3,z4,z323,z5,z6]),(0,[z0,z1,z3,z4,z5,z324,z6])],[(0,[z98,z0,z1,z3,z4,z5,z8]),(0,[z7,z0,z1,z3,z4,z5,z24]),(0,[z0,z1,z3,z4,z102,z6,z17]),(0,[z325,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z326,z4,z5,z6]),(0,[z0,z1,z3,z327,z4,z5,z6])],[(0,[z328,z0,z1,z3,z29,z5,z6]),(0,[z204,z0,z1,z3,z4,z54,z6]),(0,[z0,z1,z3,z4,z329,z5,z6]),(0,[z330,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z331,z4,z5,z6])],[(0,[z332,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z333,z5,z6]),(0,[z0,z1,z3,z4,z334,z5,z6]),(0,[z0,z1,z3,z335,z4,z5,z6]),(0,[z0,z1,z3,z336,z4,z5,z6]),(0,[z337,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z304,z4,z5,z6]),(0,[z338,z0,z1,z3,z304,z5,z6])],[(0,[z0,z1,z3,z4,z339,z5,z6]),(0,[z206,z1,z28,z3,z4,z5,z6]),(0,[z340,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z341,z29,z4,z5]),(0,[z0,z55,z1,z3,z4,z54,z6]),(0,[z0,z1,z3,z4,z5,z342,z6]),(0,[z0,z1,z3,z343,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z344]),(0,[z0,z1,z3,z138,z4,z5,z6])]],
   [[(0,[z328,z0,z1,z3,z4,z5,z6]),(0,[z0,z345,z1,z3,z4,z5,z6])],[(0,[z64,z0,z89,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z186,z17]),(0,[z0,z346,z1,z3,z4,z5,z6]),(0,[z0,z1,z347,z3,z4,z5,z6]),(0,[z74,z0,z3,z4,z301,z5,z6]),(0,[z0,z23,z1,z3,z63,z4,z5]),(0,[z0,z1,z3,z4,z5,z17,z344])],[(1,[z180,z1,z3,z11,z5,z6]),(0,[z0,z1,z348,z3,z4,z5,z6]),(0,[z0,z1,z3,z349,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z17,z145])],[(0,[z350,z0,z1,z3,z4,z5,z6]),(0,[z0,z351,z1,z3,z4,z5,z6]),(0,[z42,z0,z1,z3,z4,z5,z6]),(0,[z352,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z69,z5]),(0,[z131,z0,z1,z3,z4,z5,z17])],[(0,[z0,z43,z1,z3,z4,z5,z6]),(0,[z0,z353,z1,z3,z4,z5,z6]),(0,[z0,z354,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z355,z4,z5,z6])],[(0,[z0,z1,z356,z3,z4,z5,z6]),(0,[z150,z0,z1,z96,z4,z5,z6]),(0,[z0,z1,z3,z4,z357,z5,z6]),(0,[z358,z0,z1,z3,z4,z5,z6])],[(0,[z72,z1,z89,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z143,z5,z17]),(0,[z0,z1,z3,z4,z319,z5,z6]),(0,[z136,z0,z1,z3,z4,z5,z6]),(1,[z328,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z359,z5,z6]),(0,[z0,z360,z1,z3,z4,z5,z6]),(0,[z0,z1,z361,z3,z4,z5,z6]),(0,[z144,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z362,z5,z6])],[(0,[z363,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z364]),(0,[z151,z0,z43,z1,z3,z5,z6]),(0,[z0,z1,z3,z365,z4,z5,z6])]],
   [[(0,[z120,z0,z1,z27,z4,z5,z6]),(0,[z0,z1,z3,z4,z366,z5,z6])],[(0,[z367,z0,z1,z3,z143,z5,z6]),(0,[z150,z0,z1,z3,z4,z5,z17]),(0,[z0,z368,z1,z3,z4,z5,z6])],[(0,[z206,z0,z1,z28,z4,z5,z6]),(0,[z150,z0,z23,z1,z3,z4,z5]),(0,[z42,z0,z23,z1,z3,z4,z5]),(0,[z0,z1,z3,z369,z4,z5,z6]),(0,[z0,z1,z3,z4,z370,z5,z6]),(0,[z0,z1,z3,z4,z371,z5,z6])],[(0,[z372,z0,z1,z3,z4,z5,z6]),(0,[z338,z0,z1,z3,z143,z5,z6]),(0,[z373,z0,z1,z3,z4,z5,z6]),(0,[z98,z0,z1,z3,z175,z5,z6]),(0,[z0,z1,z3,z374,z4,z5,z6]),(0,[z0,z1,z3,z375,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z376,z6]),(0,[z377,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z172,z5,z6])],[(0,[z0,z1,z3,z4,z378,z5,z6]),(0,[z0,z379,z1,z3,z4,z5,z6]),(0,[z380,z0,z1,z3,z11,z5,z6]),(0,[z0,z1,z20,z3,z4,z5,z17]),(0,[z0,z14,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z381]),(1,[z0,z1,z3,z4,z71,z6])],[(0,[z382,z0,z1,z3,z4,z5,z6]),(0,[z136,z0,z23,z1,z3,z4,z5]),(0,[z0,z1,z3,z383,z4,z5,z6]),(0,[z380,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z384,z6])],[(0,[z0,z1,z3,z385,z4,z5,z6]),(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z8,z6]),(0,[z386,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z231,z29,z4,z5,z6]),(0,[z130,z0,z1,z3,z4,z5,z6]),(1,[z380,z0,z1,z3,z61,z6])],[(0,[z0,z1,z387,z3,z4,z5,z6]),(0,[z388,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z304,z63,z4,z5])]],
   [[(0,[z389,z0,z1,z3,z4,z5,z6]),(0,[z390,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z109,z3,z4,z5,z17])],[(0,[z72,z0,z89,z3,z4,z5,z6]),(0,[z391,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z357,z5]),(0,[z392,z0,z1,z3,z4,z5,z6])],[(0,[z0,z14,z1,z3,z4,z5,z17]),(0,[z0,z1,z4,z85,z5,z268,z6]),(0,[z0,z1,z393,z3,z4,z5,z6]),(0,[z377,z0,z23,z1,z3,z4,z5])],[(0,[z0,z19,z76,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z394,z5,z6]),(0,[z395,z0,z1,z3,z4,z5,z6]),(0,[z0,z396,z1,z3,z4,z5,z6]),(0,[z0,z23,z1,z3,z4,z5,z12])],[(0,[z397,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z8,z17]),(0,[z0,z1,z3,z398,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z399,z6]),(0,[z0,z1,z3,z4,z5,z17,z103]),(0,[z380,z0,z23,z1,z3,z4,z5]),(0,[z0,z1,z3,z304,z5,z6,z12])],[],[(0,[z0,z1,z3,z4,z400,z5,z6]),(0,[z401,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z402]),(0,[z0,z1,z403,z3,z4,z5,z6]),(0,[z0,z404,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z405,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z406]),(0,[z0,z1,z3,z407,z4,z5,z6]),(0,[z408,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z409,z3,z4,z5,z6]),(0,[z0,z213,z1,z3,z4,z5,z6]),(0,[z380,z0,z1,z3,z61,z4,z6]),(0,[z0,z1,z3,z410,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z411,z5,z6]),(0,[z205,z0,z1,z28,z4,z5,z6]),(0,[z0,z1,z3,z412,z4,z5,z6]),(0,[z57,z0,z1,z3,z4,z5,z6]),(0,[z413,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z414,z5,z6]),(0,[z0,z1,z3,z4,z415,z5,z6]),(0,[z0,z1,z109,z3,z4,z268,z6]),(0,[z0,z416,z1,z3,z4,z5,z6])],[(0,[z0,z1,z27,z4,z5,z268,z6]),(0,[z0,z1,z3,z184,z4,z5,z6]),(0,[z417,z0,z1,z3,z4,z5,z6]),(0,[z120,z0,z1,z109,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z418]),(0,[z0,z1,z3,z11,z5,z62,z6]),(0,[z0,z23,z1,z3,z4,z5,z8]),(0,[z419,z0,z1,z3,z4,z5,z6]),(0,[z0,z23,z1,z3,z141,z4,z5]),(0,[z0,z1,z420,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z421,z5,z6]),(0,[z98,z0,z1,z3,z4,z5,z17]),(1,[z100,z0,z3,z4,z54,z6])],[(0,[z422,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z423,z3,z4,z5,z6]),(1,[z0,z55,z3,z4,z102,z6]),(0,[z0,z1,z3,z424,z4,z5,z6])],[(0,[z0,z1,z3,z425,z4,z5,z6]),(0,[z426,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z427]),(0,[z0,z1,z3,z4,z428,z5,z6]),(0,[z0,z1,z3,z61,z4,z5,z6])],[(0,[z0,z1,z3,z10,z4,z5,z6]),(0,[z0,z1,z20,z27,z4,z5,z6]),(0,[z429,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z430,z4,z5,z6]),(0,[z0,z55,z3,z4,z5,z102,z6]),(0,[z0,z1,z3,z431,z4,z5,z6])],[(0,[z432,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z433,z5,z6]),(0,[z57,z0,z23,z1,z3,z4,z5]),(0,[z98,z0,z1,z3,z244,z5,z6]),(0,[z0,z1,z3,z4,z434,z5,z6]),(0,[z0,z1,z435,z3,z4,z5,z6]),(0,[z0,z23,z1,z3,z4,z301,z5])]],
   [[(0,[z0,z89,z3,z29,z4,z5,z6]),(0,[z436,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z181]),(0,[z0,z437,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z438,z4,z5,z6])],[(0,[z1,z28,z3,z27,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z439]),(0,[z0,z1,z27,z29,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z440]),(0,[z0,z1,z3,z4,z5,z441,z6]),(0,[z0,z1,z3,z4,z442,z5,z6]),(0,[z380,z0,z1,z3,z61,z5,z6]),(0,[z0,z1,z3,z4,z312,z5,z6])],[(0,[z443,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z444,z6]),(0,[z0,z1,z3,z4,z5,z445,z6]),(0,[z0,z1,z3,z4,z5,z446,z6]),(0,[z0,z3,z29,z4,z79,z5,z6]),(0,[z0,z1,z3,z4,z447,z5,z6]),(1,[z0,z1,z448,z3,z4,z5]),(0,[z0,z1,z109,z3,z4,z5,z52]),(0,[z0,z449,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z450]),(0,[z0,z43,z3,z29,z4,z5,z6]),(0,[z0,z1,z448,z3,z4,z54,z5]),(0,[z0,z1,z3,z4,z5,z5,z17])],[(0,[z0,z1,z451,z3,z4,z5,z6]),(0,[z150,z0,z1,z3,z4,z5,z97]),(0,[z0,z1,z3,z4,z5,z6,z452]),(0,[z100,z0,z1,z3,z4,z5,z17]),(1,[z0,z1,z3,z274,z62,z6])],[(0,[z136,z0,z3,z29,z4,z5,z6]),(0,[z0,z1,z21,z3,z4,z5,z6]),(0,[z0,z1,z453,z3,z4,z5,z6])],[(0,[z454,z0,z1,z3,z4,z5,z6]),(0,[z74,z0,z1,z70,z3,z4,z5])]],
   [[(0,[z72,z0,z1,z106,z4,z5,z6]),(0,[z150,z0,z318,z3,z4,z5,z6]),(0,[z150,z0,z1,z3,z319,z5,z6]),(0,[z0,z19,z1,z20,z4,z5,z6]),(0,[z0,z455,z1,z3,z4,z5,z6]),(0,[z204,z0,z1,z3,z4,z5,z6])],[(0,[z456,z0,z1,z3,z4,z5,z6]),(0,[z457,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z458,z5,z6]),(0,[z0,z1,z3,z4,z5,z459,z6]),(0,[z204,z0,z1,z3,z4,z85,z6]),(0,[z0,z1,z3,z4,z460,z5,z6]),(0,[z461,z0,z1,z3,z4,z5,z6])],[(0,[z462,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z463,z5,z6]),(1,[z0,z1,z3,z4,z268,z17]),(0,[z0,z1,z3,z4,z5,z464,z6]),(0,[z0,z23,z1,z3,z304,z4,z5])],[(0,[z205,z0,z179,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z465,z6]),(0,[z367,z0,z1,z3,z11,z5,z6]),(0,[z380,z0,z1,z3,z143,z5,z6]),(0,[z0,z1,z29,z4,z142,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z466]),(0,[z0,z1,z3,z4,z5,z251,z6]),(0,[z0,z23,z1,z3,z4,z142,z5]),(0,[z0,z1,z3,z4,z5,z268,z6]),(0,[z0,z1,z467,z3,z4,z5,z6])],[(0,[z367,z0,z1,z3,z4,z5,z6]),(0,[z136,z0,z1,z29,z4,z5,z6]),(0,[z151,z0,z1,z3,z4,z5,z6]),(0,[z468,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z469,z5,z6]),(0,[z0,z1,z3,z4,z5,z62,z6])],[(0,[z0,z1,z3,z4,z5,z470,z6]),(0,[z0,z1,z471,z3,z4,z5,z6]),(0,[z206,z0,z1,z3,z4,z5,z17]),(0,[z338,z0,z1,z3,z11,z5,z6]),(0,[z204,z0,z1,z3,z4,z5,z17])],[(0,[z0,z1,z3,z4,z472,z5,z6]),(0,[z0,z1,z3,z473,z4,z5,z6]),(0,[z100,z0,z3,z4,z54,z5,z6]),(0,[z0,z1,z3,z474,z4,z5,z6]),(0,[z338,z0,z1,z3,z4,z5,z6]),(0,[z204,z0,z23,z1,z3,z4,z5])]],
   [[(0,[z475,z0,z1,z3,z4,z5,z6]),(0,[z476,z0,z1,z3,z4,z5,z6]),(0,[z0,z55,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z142,z5,z6]),(0,[z0,z1,z231,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z477,z5,z6])],[(0,[z0,z1,z3,z4,z5,z8,z12]),(0,[z0,z23,z1,z3,z4,z5,z62])],[(0,[z0,z1,z3,z4,z5,z6,z478]),(0,[z479,z0,z1,z3,z4,z5,z6]),(0,[z0,z480,z1,z3,z4,z5,z6]),(0,[z0,z481,z1,z3,z4,z5,z6])],[(0,[z367,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z141,z4,z5,z17]),(0,[z0,z1,z70,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z62,z17]),(0,[z482,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z483,z4,z5,z6])],[(0,[z367,z0,z23,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z484]),(0,[z151,z0,z23,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z485,z5,z6]),(0,[z214,z0,z1,z4,z86,z5,z6]),(0,[z0,z1,z3,z274,z4,z5,z17]),(0,[z0,z1,z3,z486,z4,z5,z6])],[(0,[z0,z1,z3,z29,z4,z5,z6]),(0,[z0,z1,z3,z487,z4,z5,z6]),(0,[z0,z488,z1,z3,z4,z5,z6]),(0,[z338,z0,z1,z3,z4,z5,z17])],[(0,[z42,z0,z1,z165,z4,z5,z6]),(0,[z0,z23,z43,z1,z3,z4,z5]),(0,[z0,z1,z231,z3,z142,z5,z6]),(1,[z0,z1,z70,z4,z5,z103]),(0,[z338,z0,z23,z1,z3,z4,z5])],[(1,[z0,z19,z20,z4,z5,z6]),(0,[z42,z0,z1,z3,z159,z5,z6]),(0,[z0,z1,z3,z274,z5,z62,z6])]],
   [[(0,[z489,z0,z1,z3,z4,z5,z6]),(0,[z0,z43,z1,z3,z159,z5,z6]),(1,[z0,z213,z3,z4,z5,z6]),(0,[z0,z480,z1,z3,z4,z5,z17])],[(0,[z490,z0,z1,z3,z4,z5,z6]),(1,[z0,z491,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z133,z6]),(0,[z0,z1,z109,z3,z4,z69,z5]),(0,[z0,z492,z1,z3,z4,z5,z6]),(0,[z0,z1,z70,z3,z4,z5,z17])],[(0,[z0,z493,z1,z3,z4,z5,z6]),(0,[z0,z318,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z494,z5,z6]),(0,[z0,z14,z1,z3,z4,z301,z5]),(0,[z0,z1,z3,z4,z268,z6,z17]),(0,[z0,z1,z3,z4,z495,z5,z6])],[(0,[z0,z496,z1,z3,z4,z5,z6]),(0,[z205,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z497,z5,z6]),(0,[z0,z1,z3,z4,z301,z5,z17])],[(0,[z0,z19,z1,z3,z4,z5,z17]),(0,[z42,z0,z1,z231,z3,z5,z6]),(0,[z498,z0,z1,z3,z4,z5,z6]),(0,[z499,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z274,z4,z62,z6])],[(0,[z500,z0,z1,z3,z4,z5,z6]),(0,[z0,z501,z1,z3,z4,z5,z6]),(0,[z0,z43,z1,z231,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z502,z6]),(0,[z151,z0,z21,z3,z4,z5,z6]),(0,[z489,z0,z1,z3,z4,z5,z17])],[(0,[z0,z1,z3,z4,z5,z503,z6]),(0,[z504,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z505,z5,z6])]],
   [[(0,[z206,z0,z1,z27,z4,z5,z6]),(0,[z0,z1,z3,z4,z506,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z507]),(0,[z0,z1,z508,z3,z4,z5,z6]),(0,[z0,z1,z509,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z510,z6]),(0,[z214,z0,z14,z1,z3,z4,z5]),(0,[z0,z1,z3,z511,z4,z5,z6])],[(0,[z0,z1,z3,z165,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z512,z6]),(0,[z120,z0,z1,z3,z4,z268,z6])],[(0,[z0,z1,z3,z4,z513,z5,z6]),(0,[z0,z1,z3,z4,z5,z514,z6])],[(1,[z72,z89,z3,z4,z5,z6])],[(0,[z0,z23,z1,z3,z4,z143,z5]),(0,[z0,z1,z3,z4,z5,z6,z24]),(0,[z0,z1,z3,z4,z515,z5,z6]),(0,[z0,z1,z516,z3,z4,z5,z6])],[(1,[z0,z1,z106,z4,z5,z6]),(0,[z517,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z518]),(0,[z0,z519,z1,z3,z4,z5,z6])],[(0,[z520,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z17,z24]),(0,[z0,z19,z3,z4,z79,z5,z6]),(0,[z0,z23,z19,z1,z3,z4,z5]),(0,[z521,z0,z1,z3,z4,z5,z6]),(0,[z522,z0,z1,z3,z4,z5,z6]),(0,[z523,z0,z1,z3,z4,z5,z6])],[(0,[z524,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z525,z4,z5,z6]),(0,[z0,z1,z3,z304,z4,z5,z17])]],
   [[(0,[z0,z1,z3,z526,z4,z5,z6]),(0,[z0,z1,z527,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z528]),(0,[z0,z1,z3,z4,z529,z5,z6]),(0,[z0,z1,z3,z4,z530,z5,z6]),(0,[z0,z1,z3,z4,z5,z531,z6])],[(0,[z0,z491,z1,z3,z4,z5,z6]),(0,[z7,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z532,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z533]),(0,[z120,z0,z1,z4,z85,z5,z6])],[(1,[z367,z1,z3,z143,z5,z6]),(0,[z0,z1,z3,z534,z29,z5,z6]),(1,[z0,z1,z3,z4,z102,z17])],[(0,[z42,z0,z1,z3,z4,z5,z17]),(0,[z0,z55,z1,z3,z4,z5,z307]),(0,[z0,z1,z535,z3,z4,z5,z6]),(0,[z0,z23,z1,z3,z4,z5,z15]),(0,[z0,z536,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z537,z5,z6]),(0,[z538,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z539,z5,z6]),(0,[z0,z43,z1,z3,z4,z5,z17]),(0,[z540,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z179,z3,z4,z5,z6]),(0,[z205,z0,z1,z27,z4,z5,z6]),(0,[z0,z1,z3,z534,z4,z5,z6]),(1,[z0,z1,z109,z4,z268,z6]),(0,[z0,z541,z1,z3,z4,z5,z6]),(0,[z524,z0,z23,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z542,z5,z6]),(0,[z150,z0,z1,z3,z4,z5,z181]),(0,[z7,z0,z1,z3,z4,z5,z17]),(0,[z136,z0,z1,z3,z4,z5,z17]),(0,[z74,z214,z0,z1,z3,z4,z5]),(0,[z151,z0,z1,z4,z142,z5,z6]),(0,[z380,z0,z1,z3,z274,z5,z6])]],
   [[(0,[z0,z76,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z143,z5,z62,z6]),(0,[z7,z0,z23,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z543,z5,z6]),(1,[z74,z0,z3,z4,z301,z5]),(0,[z0,z544,z1,z3,z4,z5,z6])],[(0,[z0,z545,z1,z3,z4,z5,z6])],[(0,[z76,z1,z89,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z546]),(1,[z206,z1,z28,z4,z5,z6]),(0,[z265,z0,z1,z3,z4,z8,z6]),(0,[z338,z0,z1,z3,z4,z5,z12]),(0,[z547,z0,z1,z3,z4,z5,z6])],[(0,[z548,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z549,z4,z5,z6]),(0,[z550,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z551,z4,z5,z6]),(0,[z367,z0,z1,z3,z4,z5,z124]),(1,[z151,z0,z1,z142,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z552]),(0,[z0,z1,z3,z4,z5,z553,z6]),(0,[z0,z1,z3,z4,z172,z5,z17])],[(0,[z0,z1,z3,z4,z554,z5,z6]),(0,[z42,z0,z3,z4,z79,z5,z6]),(0,[z0,z1,z3,z4,z5,z555,z6]),(0,[z0,z1,z3,z556,z4,z5,z6]),(0,[z0,z1,z3,z4,z85,z5,z557]),(0,[z214,z0,z1,z3,z4,z5,z103])],[(0,[z0,z1,z3,z4,z5,z71,z6]),(0,[z380,z0,z1,z3,z4,z5,z17])],[(0,[z558,z0,z1,z3,z4,z5,z6]),(0,[z367,z0,z1,z3,z4,z5,z133]),(1,[z150,z1,z3,z4,z186,z6]),(0,[z559,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z150,z1,z3,z4,z5,z186,z6]),(1,[z0,z1,z231,z141,z5,z6]),(0,[z0,z1,z3,z4,z16,z5,z6])],[(0,[z0,z1,z3,z560,z4,z5,z6]),(0,[z180,z1,z3,z11,z4,z5,z6]),(0,[z0,z23,z1,z3,z29,z4,z5]),(0,[z0,z1,z561,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z562,z5,z6]),(1,[z0,z1,z3,z63,z5,z12])],[(0,[z0,z1,z3,z563,z4,z5,z6]),(0,[z0,z1,z3,z4,z564,z5,z6])],[(0,[z0,z1,z3,z565,z4,z5,z6]),(0,[z0,z566,z1,z3,z4,z5,z6]),(0,[z0,z23,z1,z3,z11,z4,z5]),(0,[z567,z0,z1,z3,z4,z5,z6])],[(0,[z568,z0,z1,z3,z4,z5,z6]),(0,[z569,z0,z1,z3,z4,z5,z6]),(0,[z0,z23,z14,z1,z3,z4,z5])],[(1,[z205,z1,z27,z4,z5,z6]),(0,[z0,z23,z1,z3,z4,z5,z186]),(0,[z570,z0,z1,z3,z4,z5,z6]),(0,[z0,z14,z1,z3,z4,z251,z6])],[(0,[z0,z1,z3,z571,z4,z5,z6]),(0,[z0,z1,z572,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z573]),(0,[z0,z19,z1,z29,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z574,z6])],[(0,[z575,z0,z1,z3,z4,z5,z6]),(0,[z0,z576,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z577,z6]),(0,[z0,z14,z1,z3,z4,z262,z6]),(0,[z380,z0,z1,z3,z4,z62,z6]),(0,[z0,z1,z3,z4,z5,z578,z6])]],
   [[(1,[z136,z0,z29,z4,z5,z6]),(0,[z579,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z580,z5,z6]),(0,[z0,z1,z3,z410,z4,z5,z17])],[(0,[z57,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z581,z5,z6]),(0,[z582,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z583,z6])],[(0,[z0,z584,z1,z3,z4,z5,z6]),(0,[z265,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z231,z3,z141,z5,z6])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z11,z4,z143,z5,z6]),(0,[z57,z1,z3,z4,z58,z5,z6]),(0,[z42,z0,z1,z67,z4,z5,z6])],[(0,[z64,z0,z1,z3,z4,z5,z6]),(0,[z585,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z586,z4,z5,z6]),(0,[z0,z1,z3,z4,z587,z5,z6]),(0,[z0,z1,z3,z588,z4,z5,z6]),(0,[z589,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z590,z6]),(0,[z591,z0,z1,z3,z4,z5,z6]),(0,[z42,z151,z0,z1,z3,z5,z6]),(0,[z0,z23,z1,z3,z4,z172,z5])],[(0,[z0,z1,z3,z4,z5,z592,z6]),(0,[z0,z1,z3,z593,z4,z5,z6]),(0,[z74,z0,z1,z3,z4,z5,z6]),(0,[z594,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z595,z6]),(0,[z0,z1,z3,z61,z4,z5,z17]),(0,[z0,z1,z596,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z597,z6]),(0,[z0,z1,z3,z4,z79,z5,z6]),(0,[z0,z55,z1,z3,z4,z357,z5]),(0,[z0,z1,z3,z4,z54,z6,z17]),(0,[z0,z1,z3,z4,z85,z6,z17]),(0,[z0,z23,z1,z3,z4,z5,z5])]],
   [[(0,[z0,z1,z3,z598,z4,z5,z6]),(0,[z0,z14,z1,z3,z4,z5,z15]),(0,[z0,z1,z3,z4,z85,z5,z6])],[(0,[z0,z1,z3,z27,z4,z5,z6]),(0,[z0,z1,z3,z4,z599,z5,z6]),(0,[z0,z23,z1,z3,z4,z85,z5]),(0,[z0,z1,z3,z61,z4,z5,z243])],[(0,[z0,z1,z3,z4,z600,z5,z6]),(0,[z150,z57,z1,z3,z4,z5,z6]),(1,[z0,z43,z3,z159,z5,z6]),(0,[z338,z0,z1,z3,z304,z4,z5]),(0,[z601,z0,z1,z3,z4,z5,z6]),(1,[z0,z23,z1,z3,z4,z17])],[(0,[z0,z23,z1,z89,z3,z4,z5]),(0,[z602,z0,z1,z3,z4,z5,z6]),(0,[z64,z0,z23,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z603]),(0,[z0,z1,z3,z304,z4,z5,z8]),(0,[z0,z1,z3,z604,z4,z5,z6]),(0,[z605,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z606,z4,z5,z6]),(0,[z607,z0,z1,z3,z4,z5,z6]),(0,[z0,z608,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z609,z4,z5,z6])],[(0,[z0,z1,z610,z3,z4,z5,z6]),(0,[z0,z1,z611,z3,z4,z5,z6]),(0,[z612,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z613,z3,z4,z5,z6])],[(0,[z614,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z615,z4,z5,z6]),(0,[z74,z0,z23,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z616,z6]),(0,[z0,z1,z3,z4,z5,z17,z603])],[(0,[z0,z617,z1,z3,z4,z5,z6]),(0,[z618,z0,z1,z3,z4,z5,z6]),(0,[z0,z619,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z620,z5,z6])],[(0,[z0,z1,z3,z4,z621,z5,z6]),(0,[z0,z23,z1,z28,z3,z4,z5]),(0,[z0,z622,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z76,z3,z29,z4,z5,z6]),(0,[z0,z1,z3,z4,z623,z5,z6]),(0,[z0,z1,z3,z4,z624,z5,z6])],[(0,[z7,z98,z1,z3,z4,z5,z6]),(0,[z625,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z626,z3,z4,z5,z6]),(0,[z0,z23,z1,z3,z4,z5,z103]),(0,[z0,z1,z3,z4,z627,z5,z6]),(0,[z0,z628,z1,z3,z4,z5,z6]),(0,[z0,z23,z1,z3,z61,z4,z5])],[(0,[z0,z1,z3,z629,z4,z5,z6]),(0,[z0,z455,z23,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z630,z5,z6]),(0,[z7,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z631,z4,z5,z6]),(0,[z632,z0,z1,z3,z4,z5,z6])],[(0,[z72,z0,z1,z3,z4,z5,z6]),(0,[z633,z0,z1,z3,z4,z5,z6]),(0,[z150,z0,z1,z3,z4,z58,z6]),(0,[z0,z1,z3,z4,z634,z5,z6])],[(1,[z0,z1,z3,z4,z5,z635]),(0,[z0,z1,z3,z4,z5,z6,z635]),(0,[z0,z636,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z478]),(0,[z0,z1,z3,z4,z5,z268,z17]),(0,[z204,z0,z23,z1,z3,z4,z6])],[(0,[z150,z204,z0,z1,z3,z4,z6]),(1,[z0,z1,z3,z341,z4,z5]),(0,[z151,z0,z1,z3,z4,z5,z17])],[(0,[z637,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z638,z4,z5,z6]),(0,[z639,z0,z1,z3,z4,z5,z6]),(0,[z0,z43,z3,z159,z4,z5,z6]),(0,[z0,z640,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z641]),(0,[z0,z1,z152,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z642,z5,z6]),(0,[z0,z1,z70,z3,z4,z225,z6])],[(0,[z100,z0,z89,z3,z4,z5,z6]),(0,[z643,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z644,z4,z5,z6]),(0,[z151,z0,z1,z231,z4,z5,z6]),(0,[z0,z1,z3,z4,z142,z5,z17]),(0,[z204,z0,z1,z3,z4,z268,z6]),(0,[z0,z1,z3,z645,z4,z5,z6])],[(0,[z0,z89,z3,z4,z5,z102,z6]),(0,[z0,z646,z1,z3,z4,z5,z6])],[(0,[z72,z0,z23,z1,z3,z4,z5]),(0,[z0,z1,z647,z3,z4,z5,z6]),(0,[z0,z23,z449,z1,z3,z4,z5])],[(0,[z648,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z28,z3,z4,z5,z6]),(0,[z0,z1,z107,z3,z4,z5,z6]),(0,[z0,z1,z3,z649,z4,z5,z6]),(0,[z0,z23,z1,z3,z239,z4,z5])],[(0,[z0,z1,z3,z650,z4,z5,z6]),(0,[z0,z1,z3,z29,z4,z5,z17]),(0,[z0,z23,z1,z20,z3,z4,z5]),(0,[z0,z1,z3,z4,z651,z5,z6]),(0,[z652,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z557]),(0,[z0,z1,z3,z4,z5,z6,z557]),(0,[z0,z1,z3,z4,z5,z653,z6])],[(0,[z0,z1,z3,z4,z5,z654,z6]),(0,[z0,z1,z3,z655,z4,z5,z6]),(0,[z0,z23,z1,z3,z4,z54,z5]),(0,[z656,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z657,z4,z5,z6]),(0,[z0,z1,z231,z141,z4,z5,z6])],[(0,[z0,z1,z3,z4,z658,z5,z6])],[(0,[z659,z0,z1,z3,z4,z5,z6])],[(0,[z64,z0,z76,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z660]),(0,[z0,z1,z3,z4,z661,z5,z6]),(0,[z0,z1,z3,z4,z662,z5,z6]),(0,[z663,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z61,z4,z312,z5]),(0,[z664,z0,z1,z3,z4,z5,z6])],[(0,[z72,z0,z1,z10,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z665,z6]),(0,[z666,z0,z1,z3,z4,z5,z6])],[(0,[z667,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z196,z5,z6])],[(0,[z0,z76,z3,z4,z5,z102,z6]),(0,[z367,z1,z3,z4,z143,z5,z6]),(0,[z0,z1,z668,z3,z4,z5,z6])]],
   [[(0,[z669,z0,z1,z3,z4,z5,z6]),(0,[z0,z670,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z671]),(0,[z0,z1,z3,z159,z4,z5,z6]),(0,[z214,z0,z1,z3,z4,z86,z5])],[(0,[z180,z367,z1,z3,z4,z5,z6]),(0,[z57,z0,z1,z3,z4,z58,z6])],[(0,[z0,z1,z672,z3,z4,z5,z6]),(0,[z664,z0,z23,z1,z3,z4,z5])],[(0,[z673,z0,z1,z3,z4,z5,z6]),(0,[z674,z0,z1,z3,z4,z5,z6]),(0,[z675,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z676,z4,z5,z6]),(0,[z677,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z222,z4,z5,z6])],[(0,[z0,z1,z678,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z227,z6]),(0,[z0,z1,z3,z679,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z680,z6]),(0,[z0,z128,z1,z3,z4,z5,z6]),(0,[z681,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z682]),(1,[z0,z1,z3,z4,z5,z275]),(0,[z0,z1,z3,z4,z5,z6,z275])],[(0,[z0,z1,z3,z4,z5,z102,z6]),(0,[z0,z1,z3,z4,z54,z5,z478]),(0,[z0,z1,z3,z4,z683,z5,z6]),(0,[z0,z1,z3,z4,z5,z684,z6]),(0,[z0,z1,z685,z3,z4,z5,z6])]],
   [[(0,[z150,z0,z1,z430,z4,z5,z6]),(0,[z100,z0,z1,z3,z4,z102,z6]),(0,[z0,z1,z3,z237,z274,z4,z5]),(0,[z0,z1,z3,z686,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z17,z682])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z0,z19,z89,z3,z4,z5,z6]),(0,[z687,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z6]),(1,[z0,z1,z3,z138,z4,z5]),(0,[z0,z1,z3,z4,z225,z5,z6]),(0,[z338,z0,z1,z3,z63,z5,z6]),(0,[z0,z1,z3,z4,z5,z531,z17]),(0,[z0,z23,z1,z3,z331,z4,z5])],[(0,[z688,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z58,z5,z635]),(0,[z689,z0,z1,z3,z4,z5,z6])],[(0,[z72,z0,z76,z3,z4,z5,z6]),(0,[z0,z1,z3,z690,z4,z5,z6]),(0,[z691,z0,z1,z3,z4,z5,z6])],[(0,[z64,z76,z1,z3,z4,z5,z6]),(0,[z0,z1,z692,z3,z4,z5,z6]),(0,[z0,z1,z3,z693,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z694,z6]),(0,[z0,z1,z3,z4,z5,z102,z17]),(0,[z246,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z448,z3,z4,z5,z6]),(0,[z74,z0,z1,z3,z4,z301,z5])],[(0,[z0,z1,z3,z341,z4,z5,z6]),(0,[z0,z23,z1,z231,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z695,z6]),(0,[z0,z1,z3,z61,z274,z4,z6]),(0,[z0,z1,z3,z4,z5,z696,z6]),(0,[z0,z1,z3,z4,z5,z6,z17])]],
   [[(0,[z697,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z698,z3,z4,z5,z6]),(1,[z0,z23,z1,z3,z4,z5])],[(0,[z0,z76,z1,z3,z4,z5,z17]),(0,[z204,z0,z1,z3,z4,z102,z6]),(0,[z0,z699,z1,z3,z4,z5,z6]),(0,[z0,z23,z544,z1,z3,z4,z5])],[(1,[z0,z1,z3,z534,z5,z6]),(0,[z700,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z243])],[(0,[z701,z0,z1,z3,z4,z5,z6]),(0,[z205,z0,z491,z3,z4,z5,z6]),(0,[z0,z1,z28,z4,z5,z268,z6]),(0,[z0,z1,z3,z430,z4,z5,z6]),(0,[z0,z55,z1,z3,z4,z102,z6])],[(0,[z0,z1,z702,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z24,z12])],[(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z0,z1,z3,z4,z703,z5,z6]),(0,[z0,z23,z1,z3,z274,z4,z5]),(0,[z704,z0,z1,z3,z4,z5,z6])],[(0,[z705,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z301,z5,z6,z15]),(0,[z0,z1,z4,z86,z5,z6,z103]),(0,[z0,z1,z3,z237,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z706,z6]),(0,[z697,z0,z23,z1,z3,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z3,z293,z4,z17]),(0,[z0,z1,z3,z430,z4,z17]),(0,[z150,z1,z3,z4,z186,z97]),(0,[z0,z3,z4,z196,z102,z17])],[(0,[z0,z1,z3,z4,z5,z707]),(1,[z1,z3,z4,z708,z6])],[(0,[z171,z89,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z709]),(0,[z0,z1,z3,z4,z710,z6]),(0,[z0,z1,z70,z4,z225,z103]),(0,[z664,z0,z1,z3,z4,z17])],[(0,[z0,z1,z711,z4,z5,z6]),(0,[z150,z318,z3,z4,z186,z6]),(0,[z150,z1,z3,z319,z186,z6]),(0,[z150,z0,z1,z3,z4,z635])],[(0,[z0,z76,z10,z4,z5,z6]),(0,[z0,z1,z9,z4,z85,z6])],[(0,[z0,z23,z1,z67,z4,z5]),(0,[z0,z1,z712,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z557]),(0,[z0,z1,z4,z713,z5,z6]),(0,[z0,z1,z3,z4,z5,z714])],[(0,[z0,z715,z1,z3,z4,z6])],[(0,[z57,z0,z1,z3,z4,z635]),(0,[z0,z1,z3,z716,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z717,z5]),(0,[z328,z0,z1,z231,z5,z6]),(0,[z0,z21,z4,z142,z5,z6])],[(0,[z205,z1,z718,z4,z5,z6]),(0,[z0,z1,z719,z4,z5,z6])],[(0,[z0,z19,z572,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z531]),(0,[z0,z43,z3,z604,z5,z6]),(0,[z0,z1,z3,z4,z720,z5]),(0,[z0,z1,z3,z4,z177,z17])],[(0,[z0,z544,z3,z4,z301,z5]),(0,[z0,z1,z4,z85,z268,z17])],[(0,[z0,z721,z3,z4,z5,z6]),(0,[z0,z1,z430,z319,z5,z6]),(0,[z0,z1,z3,z4,z181,z17]),(0,[z0,z1,z3,z4,z5,z722]),(0,[z0,z1,z3,z4,z5,z723])],[(0,[z0,z1,z3,z4,z5,z724]),(0,[z72,z23,z89,z3,z4,z5]),(0,[z0,z179,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z725]),(0,[z0,z1,z3,z4,z5,z726]),(0,[z0,z727,z3,z4,z5,z6])],[(0,[z0,z728,z3,z4,z5,z6]),(0,[z171,z0,z1,z3,z4,z17])]],
   [[(0,[z0,z1,z3,z184,z5,z6]),(0,[z0,z1,z3,z729,z5,z6]),(0,[z57,z1,z3,z4,z708,z6]),(0,[z0,z1,z3,z730,z5,z6]),(0,[z0,z1,z3,z4,z5,z731]),(0,[z0,z1,z732,z3,z4,z54])],[],[(0,[z42,z0,z23,z3,z79,z5])],[(0,[z0,z1,z3,z4,z198,z17]),(0,[z0,z1,z3,z4,z733,z6]),(0,[z100,z0,z3,z4,z734,z6]),(0,[z0,z699,z1,z3,z4,z17])],[(0,[z0,z1,z735,z4,z5,z6]),(0,[z736,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z737,z6]),(0,[z0,z1,z3,z4,z71,z103])],[(0,[z0,z1,z3,z4,z5,z738]),(0,[z0,z1,z3,z739,z5,z6]),(0,[z0,z14,z3,z431,z4,z5]),(0,[z0,z1,z3,z4,z5,z275]),(0,[z259,z1,z3,z4,z5,z603])],[(0,[z0,z1,z740,z4,z5,z6]),(0,[z0,z351,z20,z4,z5,z6])],[(0,[z57,z1,z3,z4,z58,z635]),(0,[z0,z1,z3,z341,z4,z741]),(0,[z0,z742,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z743,z6]),(0,[z0,z744,z3,z4,z5,z17])]],
   [[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z745,z4,z5,z6]),(0,[z150,z0,z107,z3,z4,z17]),(0,[z0,z1,z3,z4,z219,z17]),(0,[z0,z1,z3,z244,z5,z24]),(0,[z0,z1,z3,z4,z5,z746]),(0,[z0,z1,z3,z747,z5,z6])],[(0,[z0,z1,z3,z4,z748,z6])],[(0,[z0,z1,z749,z4,z5,z6]),(0,[z0,z1,z96,z4,z5,z6]),(0,[z750,z0,z1,z3,z4,z5]),(0,[z380,z0,z1,z3,z264,z6]),(0,[z204,z0,z1,z3,z4,z181]),(0,[z0,z1,z3,z4,z227,z17]),(0,[z214,z0,z1,z4,z16,z5])],[(0,[z367,z1,z3,z143,z5,z17]),(0,[z0,z23,z1,z231,z141,z5]),(0,[z0,z156,z1,z3,z4,z17])],[(0,[z150,z83,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z751,z5]),(0,[z0,z1,z3,z4,z172,z17])],[(0,[z0,z1,z3,z138,z4,z225])],[(0,[z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z752,z5,z6]),(0,[z0,z1,z3,z4,z753,z6]),(0,[z0,z1,z3,z4,z238,z17]),(0,[z0,z1,z3,z4,z5,z754])],[(0,[z0,z23,z1,z3,z4,z5])]],
   [[(0,[z0,z755,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z756,z17])],[(0,[z0,z757,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z758]),(0,[z1,z3,z4,z5,z708,z6]),(0,[z0,z1,z3,z4,z759,z6]),(0,[z0,z1,z3,z4,z5,z243])],[(0,[z0,z1,z3,z4,z760,z6]),(0,[z206,z1,z28,z4,z5,z17]),(0,[z0,z1,z3,z244,z5,z6]),(0,[z0,z1,z3,z4,z761,z5]),(0,[z0,z1,z3,z762,z63,z5])],[(0,[z0,z763,z1,z3,z4,z6]),(0,[z0,z23,z1,z3,z764,z5])],[(0,[z150,z0,z1,z430,z4,z17]),(0,[z0,z1,z3,z230,z4,z17]),(0,[z0,z1,z3,z4,z247,z17]),(0,[z0,z1,z4,z765,z268,z6]),(0,[z0,z23,z1,z3,z4,z225])],[(0,[z150,z0,z1,z3,z4,z17]),(0,[z0,z3,z4,z54,z102,z17])],[(0,[z0,z1,z766,z4,z5,z6]),(0,[z22,z1,z3,z11,z5,z6]),(0,[z0,z636,z29,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z767])],[(0,[z7,z1,z3,z4,z5,z8]),(0,[z691,z1,z3,z4,z5,z24]),(0,[z0,z1,z3,z534,z5,z17])]],
   [[(0,[z0,z1,z3,z4,z5,z768]),(0,[z0,z1,z3,z4,z5,z769]),(0,[z150,z1,z430,z4,z186,z6]),(0,[z0,z1,z3,z4,z713,z5])],[(0,[z0,z1,z3,z770,z5,z6]),(0,[z57,z0,z1,z3,z4,z17]),(0,[z0,z1,z3,z4,z5,z771]),(0,[z0,z1,z3,z4,z5,z772])],[(0,[z0,z773,z3,z4,z5,z6]),(0,[z0,z566,z1,z3,z4,z17]),(0,[z0,z1,z3,z4,z5,z774]),(0,[z150,z1,z3,z4,z186,z181]),(0,[z697,z0,z1,z3,z4,z227]),(0,[z0,z1,z3,z4,z775,z5]),(0,[z144,z0,z1,z4,z16,z5])],[(0,[z0,z1,z3,z4,z5,z776]),(0,[z0,z777,z3,z4,z5,z6]),(0,[z120,z0,z1,z4,z85,z557]),(0,[z0,z23,z715,z1,z3,z4])],[(0,[z0,z1,z3,z778,z5,z6])],[(0,[z0,z779,z3,z4,z5,z6]),(0,[z0,z1,z3,z780,z4,z5]),(0,[z697,z449,z1,z3,z4,z5]),(0,[z377,z0,z1,z3,z153,z5])],[(0,[z0,z1,z10,z4,z5,z17]),(0,[z0,z1,z781,z4,z5,z6]),(0,[z0,z1,z3,z4,z282,z17]),(0,[z0,z1,z231,z782,z5,z6])],[(0,[z64,z76,z3,z4,z5,z6]),(0,[z0,z1,z783,z4,z5,z6]),(0,[z150,z0,z1,z3,z319,z17]),(0,[z0,z21,z3,z4,z5,z17])]],
   [[(0,[z100,z0,z3,z4,z621,z6]),(0,[z0,z3,z4,z784,z5,z6]),(0,[z0,z1,z3,z4,z785,z6]),(0,[z0,z1,z3,z264,z4,z17]),(0,[z0,z1,z786,z4,z5,z6]),(1,[z0,z3,z4,z734,z6])],[(1,[z0,z3,z4,z787,z5]),(0,[z0,z1,z3,z4,z5,z52])],[(0,[z0,z187,z1,z3,z4,z17]),(0,[z100,z0,z448,z3,z4,z54]),(0,[z0,z21,z231,z4,z5,z6])],[(0,[z0,z179,z28,z4,z5,z6]),(0,[z57,z1,z3,z4,z58,z6]),(0,[z0,z1,z3,z4,z85,z52])],[(0,[z206,z1,z718,z4,z5,z6]),(0,[z0,z1,z430,z4,z5,z181]),(0,[z0,z1,z3,z239,z4,z17])],[(0,[z0,z1,z3,z4,z5,z788]),(0,[z0,z1,z3,z789,z5,z6]),(0,[z0,z107,z3,z184,z5,z6]),(0,[z57,z1,z3,z4,z531,z17]),(0,[z0,z1,z67,z4,z5,z6])],[(0,[z98,z1,z3,z4,z5,z24]),(0,[z0,z1,z3,z4,z54,z17]),(0,[z790,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z791]),(0,[z1,z718,z27,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z792])]],
   [[(0,[z338,z0,z1,z3,z407,z5]),(0,[z0,z1,z3,z4,z5,z793]),(0,[z0,z1,z70,z4,z71,z103])],[(0,[z57,z1,z3,z4,z58,z17]),(0,[z0,z1,z448,z3,z4,z17])],[(0,[z0,z794,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z97]),(0,[z0,z43,z3,z159,z5,z17])],[(0,[z72,z89,z106,z4,z5,z6]),(0,[z0,z1,z107,z3,z4,z17]),(0,[z214,z0,z1,z398,z4,z5]),(0,[z0,z1,z3,z4,z5,z795]),(0,[z0,z796,z3,z4,z5,z17])],[(0,[z367,z1,z3,z143,z5,z124]),(0,[z0,z1,z96,z4,z5,z97]),(0,[z0,z1,z3,z797,z5,z6]),(0,[z0,z23,z1,z3,z534,z5]),(0,[z0,z23,z1,z3,z4,z251]),(0,[z0,z23,z213,z3,z4,z5])],[(0,[z0,z318,z3,z4,z5,z6]),(0,[z0,z107,z3,z4,z5,z6]),(0,[z0,z1,z610,z3,z4,z17]),(0,[z0,z1,z3,z319,z5,z6]),(0,[z790,z23,z1,z3,z4,z5])],[(0,[z73,z76,z3,z4,z5,z6]),(0,[z0,z1,z3,z11,z5,z124]),(0,[z0,z1,z3,z798,z4,z5]),(0,[z204,z0,z1,z448,z3,z4]),(0,[z120,z0,z1,z4,z85,z6]),(0,[z0,z1,z3,z4,z324,z17])],[(0,[z391,z0,z1,z3,z4,z17]),(0,[z0,z1,z3,z4,z5,z124]),(0,[z0,z107,z96,z4,z5,z6]),(0,[z0,z318,z96,z4,z5,z6]),(0,[z0,z1,z799,z4,z5,z6]),(0,[z800,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z801,z5])]],
   [[(0,[z0,z1,z3,z802,z5,z6]),(0,[z265,z7,z1,z3,z4,z8]),(0,[z0,z1,z3,z4,z803,z5])],[(0,[z0,z23,z1,z3,z4,z695]),(0,[z130,z0,z1,z3,z4,z5]),(0,[z0,z3,z4,z734,z102,z6]),(0,[z0,z1,z3,z4,z804,z5]),(1,[z0,z1,z4,z765,z6]),(0,[z0,z1,z152,z4,z86,z5])],[(0,[z0,z1,z3,z4,z805,z5]),(0,[z0,z1,z3,z4,z5,z133]),(0,[z7,z0,z1,z3,z4,z227]),(0,[z0,z1,z3,z762,z5,z6])],[(0,[z1,z3,z718,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z806]),(0,[z0,z107,z3,z4,z5,z17]),(0,[z0,z3,z4,z787,z5,z6]),(0,[z0,z480,z3,z4,z5,z15]),(0,[z0,z23,z1,z3,z4,z221])],[(0,[z0,z1,z3,z4,z807,z6]),(0,[z0,z1,z3,z4,z5,z808]),(0,[z0,z23,z318,z3,z4,z5]),(0,[z0,z273,z1,z3,z4,z251]),(0,[z809,z0,z3,z4,z5,z6])],[],[],[(0,[z0,z1,z3,z4,z810,z17]),(0,[z0,z23,z19,z20,z4,z5]),(0,[z390,z0,z1,z3,z4,z17])]],
   [[(0,[z0,z1,z811,z4,z5,z6]),(0,[z0,z1,z3,z222,z5,z12]),(0,[z0,z455,z1,z152,z4,z5])],[(0,[z0,z1,z812,z4,z5,z6]),(0,[z205,z491,z27,z4,z5,z6]),(0,[z0,z1,z3,z813,z5,z6]),(0,[z0,z1,z814,z4,z5,z6]),(0,[z0,z1,z3,z4,z815,z5]),(0,[z0,z1,z3,z816,z5,z6])],[(0,[z372,z0,z1,z3,z4,z17]),(0,[z0,z23,z1,z3,z244,z5]),(0,[z328,z0,z1,z3,z5,z6])],[(0,[z0,z1,z817,z4,z5,z6]),(0,[z0,z1,z3,z818,z5,z6]),(0,[z0,z1,z3,z4,z819,z5]),(1,[z1,z3,z820,z5,z6]),(0,[z0,z1,z165,z4,z5,z6]),(0,[z0,z1,z3,z821,z4,z5])],[(0,[z0,z1,z3,z822,z4,z5]),(0,[z0,z1,z823,z4,z5,z6]),(0,[z697,z0,z1,z3,z4,z17]),(0,[z352,z0,z29,z4,z5,z6]),(0,[z0,z1,z70,z4,z713,z5])],[(0,[z569,z76,z3,z4,z5,z6]),(0,[z0,z824,z3,z4,z5,z6]),(0,[z0,z14,z3,z4,z251,z15]),(0,[z0,z825,z3,z4,z5,z6]),(0,[z0,z23,z1,z3,z4,z583])],[(0,[z0,z1,z3,z4,z826,z6]),(0,[z0,z1,z3,z827,z4,z6]),(0,[z0,z23,z1,z3,z4,z514]),(0,[z0,z23,z1,z109,z4,z268])],[(0,[z0,z1,z3,z4,z5,z828]),(0,[z829,z0,z1,z3,z4,z6]),(0,[z150,z1,z3,z4,z708,z6]),(0,[z57,z128,z1,z3,z4,z58]),(0,[z830,z1,z3,z4,z5,z6]),(0,[z0,z43,z3,z588,z5,z6]),(0,[z0,z14,z3,z4,z262,z15]),(0,[z0,z715,z1,z3,z4,z17])]],
   [[(0,[z691,z1,z3,z143,z5,z6])],[(0,[z0,z1,z3,z4,z5,z831]),(0,[z832,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z175,z5,z6]),(0,[z0,z1,z3,z764,z5,z6]),(0,[z0,z1,z3,z4,z833,z6]),(0,[z204,z0,z715,z1,z3,z4])],[(0,[z0,z1,z3,z4,z5,z834]),(0,[z0,z1,z3,z4,z54,z307]),(0,[z0,z23,z1,z322,z3,z4])],[(0,[z489,z1,z3,z4,z5,z531])],[(0,[z0,z1,z3,z835,z4,z5]),(0,[z0,z836,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z837]),(1,[z0,z715,z1,z3,z4])],[(0,[z0,z23,z1,z10,z4,z5]),(0,[z0,z1,z718,z4,z5,z6]),(0,[z0,z1,z96,z184,z5,z6]),(0,[z0,z1,z3,z4,z357,z5])],[(0,[z0,z1,z3,z838,z5,z6]),(0,[z0,z839,z1,z3,z4,z5]),(0,[z151,z0,z1,z782,z5,z6]),(0,[z204,z0,z1,z3,z138,z4])],[(0,[z0,z179,z3,z4,z5,z17]),(0,[z0,z23,z1,z3,z184,z5]),(0,[z0,z1,z3,z175,z5,z17]),(0,[z0,z23,z1,z3,z4,z262]),(0,[z0,z1,z3,z4,z529,z17]),(0,[z0,z1,z3,z4,z399,z17])]],
   [[(0,[z0,z1,z3,z4,z5,z840]),(0,[z0,z1,z3,z841,z5,z6]),(0,[z0,z480,z3,z4,z102,z6]),(0,[z204,z0,z23,z1,z3,z4])],[(0,[z0,z1,z3,z184,z5,z17]),(1,[z0,z1,z3,z842,z6])],[(0,[z843,z1,z3,z4,z5,z6]),(0,[z844,z0,z1,z3,z4,z5])],[(0,[z214,z0,z1,z4,z86,z5])],[],[(0,[z0,z1,z3,z4,z845,z5]),(0,[z0,z1,z3,z4,z587,z17]),(0,[z0,z1,z3,z4,z225,z6])],[(0,[z0,z1,z3,z143,z5,z124]),(0,[z1,z3,z11,z820,z5,z6]),(0,[z328,z0,z21,z3,z5,z6]),(0,[z130,z0,z1,z3,z534,z5]),(0,[z0,z19,z423,z4,z5,z6]),(0,[z846,z1,z3,z4,z5,z6]),(0,[z0,z847,z3,z4,z5,z6])],[(0,[z0,z107,z3,z4,z5,z97]),(0,[z0,z318,z3,z4,z5,z97]),(0,[z1,z3,z4,z5,z793,z24]),(0,[z0,z1,z848,z4,z5,z6]),(0,[z849,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z485,z17])]],
   [[(0,[z0,z55,z3,z4,z102,z6]),(0,[z0,z850,z1,z3,z4,z5]),(0,[z0,z1,z18,z4,z268,z6])],[(0,[z0,z1,z3,z851,z4,z5]),(0,[z0,z1,z430,z4,z6,z17]),(0,[z0,z1,z3,z852,z4,z5]),(0,[z214,z0,z1,z3,z4,z251]),(0,[z0,z1,z3,z4,z853,z6]),(0,[z0,z1,z3,z4,z155,z17]),(0,[z0,z1,z3,z237,z4,z5])],[(0,[z0,z1,z610,z4,z268,z6]),(0,[z0,z1,z3,z854,z5,z6]),(0,[z0,z855,z1,z3,z4,z5]),(0,[z0,z107,z3,z319,z5,z6]),(0,[z0,z1,z3,z4,z856,z6])],[(0,[z0,z1,z96,z4,z5,z17]),(0,[z0,z1,z3,z4,z85,z17])],[(0,[z0,z1,z3,z857,z5,z6]),(0,[z0,z1,z3,z4,z5,z181]),(0,[z0,z1,z3,z4,z301,z251])],[(0,[z0,z1,z3,z858,z5,z6]),(0,[z180,z1,z3,z820,z5,z6]),(0,[z0,z1,z3,z762,z5,z12])],[(0,[z0,z1,z3,z4,z5,z859]),(0,[z0,z1,z3,z4,z708,z6]),(0,[z0,z1,z3,z274,z62,z275])],[(0,[z0,z1,z448,z3,z4,z5])]],
   [[(0,[z150,z57,z1,z3,z4,z17]),(0,[z0,z1,z860,z4,z5,z6]),(0,[z0,z1,z861,z4,z5,z6])],[(0,[z0,z179,z27,z4,z5,z6]),(0,[z0,z1,z3,z4,z251,z6]),(0,[z0,z1,z3,z274,z62,z6])],[(0,[z862,z0,z1,z3,z4,z5]),(0,[z0,z1,z863,z4,z5,z6])],[(0,[z864,z0,z1,z3,z5,z6]),(0,[z0,z23,z179,z3,z4,z5]),(0,[z0,z23,z1,z96,z4,z5]),(0,[z0,z1,z3,z244,z5,z17]),(0,[z0,z23,z1,z3,z4,z193]),(0,[z0,z1,z3,z4,z262,z6]),(0,[z0,z1,z70,z629,z4,z5]),(0,[z0,z1,z3,z4,z765,z6])],[(0,[z265,z0,z1,z3,z4,z6]),(0,[z865,z1,z3,z4,z5,z6]),(0,[z0,z165,z4,z79,z5,z6]),(0,[z0,z1,z231,z349,z5,z6]),(0,[z0,z1,z3,z63,z153,z5])],[(0,[z295,z0,z1,z3,z4,z17]),(0,[z0,z1,z3,z4,z866,z6]),(0,[z0,z1,z3,z4,z459,z17]),(0,[z0,z14,z3,z4,z787,z5])],[(0,[z867,z1,z3,z4,z5,z6]),(0,[z136,z0,z341,z29,z4,z5])],[(0,[z0,z89,z3,z4,z102,z17]),(0,[z0,z1,z3,z4,z465,z17]),(0,[z287,z0,z1,z3,z4,z17]),(0,[z1,z28,z718,z4,z5,z6]),(0,[z98,z1,z3,z175,z5,z24]),(0,[z0,z1,z3,z868,z5,z6]),(0,[z869,z0,z1,z3,z4,z5]),(0,[z0,z1,z4,z870,z5,z6]),(0,[z0,z1,z3,z4,z251,z17]),(0,[z0,z1,z3,z4,z415,z17]),(0,[z0,z1,z3,z4,z477,z17])]],
   [[],[(0,[z0,z1,z3,z4,z470,z17]),(0,[z0,z1,z871,z4,z5,z6]),(0,[z0,z1,z872,z4,z5,z6]),(0,[z0,z1,z3,z4,z281,z17]),(0,[z0,z873,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z262,z17])],[(0,[z0,z1,z678,z3,z4,z17]),(0,[z874,z0,z1,z3,z4,z5]),(0,[z0,z1,z4,z782,z5,z6])],[(0,[z0,z1,z3,z4,z875,z6]),(0,[z876,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z877,z5,z6])],[(0,[z0,z1,z3,z4,z5,z878]),(0,[z0,z3,z739,z79,z5,z6]),(0,[z214,z0,z1,z4,z713,z5])],[(0,[z0,z1,z3,z4,z879,z6]),(0,[z0,z1,z3,z184,z5,z97]),(0,[z0,z1,z3,z4,z5,z880]),(0,[z74,z0,z3,z4,z787,z5])],[(0,[z0,z881,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z882])],[(0,[z136,z0,z534,z29,z5,z6]),(0,[z328,z0,z43,z3,z5,z6]),(0,[z0,z715,z1,z3,z4,z172])]],
   [[(0,[z0,z23,z1,z106,z4,z5]),(0,[z64,z76,z3,z4,z5,z17]),(0,[z0,z318,z3,z184,z5,z6]),(0,[z150,z23,z1,z3,z4,z186]),(0,[z0,z55,z3,z4,z734,z6]),(0,[z246,z0,z3,z4,z196,z5])],[(0,[z0,z883,z1,z3,z4,z5]),(0,[z42,z0,z3,z79,z5,z6]),(0,[z0,z1,z884,z4,z5,z6]),(0,[z0,z1,z3,z4,z302,z17])],[(0,[z0,z885,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z86,z71])],[(0,[z0,z1,z886,z4,z5,z6]),(0,[z0,z128,z1,z3,z4,z5]),(0,[z887,z0,z1,z3,z4,z5]),(0,[z888,z0,z1,z3,z5,z6])],[(0,[z0,z1,z889,z4,z5,z6]),(0,[z0,z890,z3,z4,z5,z6]),(1,[z0,z786,z4,z5,z6]),(0,[z0,z1,z891,z4,z5,z6]),(0,[z0,z1,z3,z4,z892,z6])],[(0,[z0,z491,z3,z4,z5,z6]),(0,[z0,z1,z893,z4,z5,z6]),(0,[z0,z894,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z307]),(0,[z0,z1,z895,z3,z4,z5]),(0,[z0,z1,z18,z4,z5,z344]),(0,[z0,z1,z3,z896,z5,z6])],[(0,[z0,z897,z3,z4,z5,z6]),(0,[z204,z0,z107,z3,z4,z6]),(0,[z0,z1,z3,z4,z898,z6]),(0,[z0,z1,z67,z4,z5,z17]),(0,[z0,z1,z782,z142,z5,z6]),(0,[z0,z1,z3,z4,z312,z5]),(0,[z140,z0,z173,z3,z4,z5])],[(0,[z0,z1,z3,z4,z317,z17])]],
   [[(0,[z0,z1,z3,z899,z5,z6]),(0,[z120,z0,z1,z4,z232,z6]),(0,[z0,z3,z4,z301,z787,z5]),(0,[z0,z23,z1,z3,z4,z384])],[(0,[z0,z1,z3,z4,z900,z6]),(0,[z0,z1,z3,z901,z4,z6]),(0,[z0,z1,z3,z4,z502,z17])],[(0,[z0,z89,z10,z4,z5,z6]),(0,[z1,z3,z820,z143,z5,z6]),(0,[z0,z1,z96,z319,z5,z6]),(0,[z0,z1,z3,z4,z503,z17]),(0,[z0,z1,z3,z4,z268,z52])],[(0,[z0,z1,z3,z902,z5,z6]),(0,[z98,z1,z3,z244,z5,z24]),(0,[z0,z1,z3,z903,z5,z6]),(0,[z0,z1,z3,z4,z5,z904]),(0,[z0,z55,z3,z4,z357,z102])],[(0,[z905,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z906,z5]),(0,[z607,z1,z27,z4,z5,z6])],[(0,[z0,z584,z3,z4,z102,z6]),(0,[z0,z907,z3,z4,z5,z6]),(0,[z0,z908,z3,z4,z5,z6])],[(0,[z1,z909,z3,z4,z5,z6]),(0,[z0,z910,z3,z4,z5,z6]),(0,[z0,z318,z3,z4,z5,z17]),(0,[z0,z1,z3,z319,z5,z17]),(0,[z0,z1,z3,z4,z5,z911]),(0,[z100,z0,z3,z4,z54,z478]),(0,[z0,z912,z3,z4,z5,z6]),(0,[z0,z1,z109,z4,z69,z268]),(0,[z0,z1,z4,z713,z5,z103]),(0,[z0,z1,z3,z913,z4,z5]),(0,[z0,z23,z1,z3,z511,z4])],[(0,[z72,z89,z3,z4,z5,z6]),(0,[z0,z1,z914,z4,z5,z6]),(0,[z0,z584,z1,z3,z4,z17]),(0,[z0,z1,z3,z4,z5,z915]),(0,[z0,z1,z3,z916,z4,z5]),(0,[z0,z1,z3,z4,z5,z917]),(0,[z120,z0,z1,z4,z85,z17])]],
   [[(0,[z0,z918,z3,z4,z5,z6]),(0,[z0,z3,z159,z739,z5,z6]),(0,[z0,z1,z4,z86,z713,z5])],[(0,[z0,z1,z106,z4,z5,z6]),(0,[z180,z1,z3,z11,z5,z6]),(0,[z0,z107,z3,z4,z5,z181]),(0,[z0,z1,z732,z3,z4,z17])],[(0,[z204,z0,z1,z430,z4,z6]),(0,[z328,z0,z23,z1,z3,z5]),(0,[z0,z1,z919,z3,z4,z5]),(0,[z0,z1,z3,z920,z4,z5]),(0,[z0,z1,z3,z4,z69,z5]),(0,[z0,z23,z1,z3,z4,z71])],[(0,[z0,z1,z3,z4,z5,z810]),(0,[z0,z1,z3,z4,z662,z17]),(0,[z0,z908,z3,z4,z5,z17])],[(0,[z0,z1,z921,z4,z5,z6]),(0,[z0,z23,z1,z3,z4,z227]),(0,[z0,z1,z922,z3,z4,z5])],[(0,[z0,z1,z923,z4,z5,z6]),(0,[z909,z89,z3,z4,z5,z6]),(0,[z0,z924,z1,z3,z4,z6]),(0,[z925,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z926]),(0,[z150,z0,z318,z3,z4,z17]),(0,[z0,z3,z4,z734,z5,z6]),(0,[z0,z1,z3,z927,z4,z17])],[(0,[z0,z23,z1,z165,z4,z5]),(0,[z0,z1,z3,z842,z274,z6])],[(0,[z126,z1,z28,z4,z5,z6]),(0,[z180,z1,z3,z11,z5,z17]),(0,[z0,z1,z3,z244,z5,z8]),(0,[z0,z1,z3,z928,z5,z6]),(0,[z120,z0,z1,z4,z765,z6])]],
   [[(0,[z0,z1,z3,z4,z405,z17]),(0,[z0,z1,z3,z929,z5,z6]),(0,[z0,z23,z491,z3,z4,z5]),(1,[z1,z3,z4,z5,z793]),(0,[z930,z0,z1,z3,z4,z5]),(0,[z0,z1,z18,z4,z5,z103])],[(0,[z0,z909,z3,z4,z5,z6])],[(0,[z150,z0,z1,z3,z4,z810]),(0,[z136,z0,z23,z29,z4,z5]),(0,[z1,z3,z4,z5,z931,z6]),(0,[z0,z1,z109,z4,z268,z6]),(0,[z0,z1,z3,z816,z5,z17])],[(0,[z0,z1,z3,z932,z5,z6]),(0,[z0,z1,z3,z4,z5,z933]),(0,[z328,z0,z1,z3,z5,z17]),(0,[z0,z1,z3,z4,z934,z5]),(0,[z0,z1,z3,z4,z71,z6])],[(0,[z0,z1,z28,z4,z268,z17]),(0,[z0,z935,z3,z4,z5,z6]),(0,[z0,z1,z3,z936,z4,z5]),(0,[z0,z1,z165,z4,z5,z17]),(0,[z0,z1,z3,z222,z5,z145])],[(0,[z0,z1,z3,z4,z937,z6]),(0,[z132,z0,z29,z4,z5,z6]),(0,[z136,z0,z786,z4,z5,z6]),(0,[z0,z1,z3,z341,z827,z4]),(0,[z938,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z515,z17]),(0,[z380,z0,z1,z3,z61,z6])],[(0,[z0,z1,z3,z4,z939,z5]),(0,[z0,z1,z3,z4,z5,z940]),(0,[z42,z0,z67,z79,z5,z6])],[(0,[z72,z89,z10,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z941]),(0,[z0,z1,z3,z4,z553,z17]),(0,[z0,z23,z1,z3,z274,z62])]],
   [[(0,[z0,z1,z3,z4,z5,z942]),(0,[z380,z0,z23,z1,z3,z61])],[(0,[z0,z1,z3,z4,z943,z6]),(0,[z0,z1,z3,z4,z944,z6]),(0,[z0,z1,z3,z4,z135,z17]),(0,[z151,z0,z23,z1,z142,z5]),(0,[z380,z0,z1,z3,z61,z312])],[(0,[z37,z1,z27,z4,z5,z6]),(0,[z0,z945,z3,z4,z5,z6]),(0,[z0,z1,z3,z946,z4,z5]),(0,[z0,z1,z3,z947,z5,z6]),(0,[z0,z1,z3,z4,z5,z948])],[(0,[z949,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z950,z6]),(0,[z0,z1,z3,z4,z5,z951]),(0,[z0,z1,z3,z4,z5,z952]),(0,[z150,z1,z3,z4,z186,z6]),(0,[z0,z1,z953,z3,z4,z5]),(0,[z0,z20,z786,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z954])],[(0,[z0,z1,z3,z4,z955,z6]),(0,[z637,z0,z29,z4,z5,z6]),(0,[z0,z1,z430,z184,z5,z6]),(0,[z0,z1,z3,z63,z5,z12])],[(0,[z0,z1,z3,z956,z4,z5]),(0,[z0,z1,z3,z4,z5,z957]),(0,[z0,z3,z4,z739,z5,z6]),(0,[z0,z1,z3,z4,z414,z17]),(0,[z74,z0,z3,z4,z196,z5])],[(0,[z0,z1,z3,z184,z5,z181]),(0,[z0,z1,z3,z240,z4,z17]),(0,[z0,z3,z4,z787,z5,z15]),(0,[z0,z1,z3,z4,z5,z958])]],
   [[(0,[z0,z1,z3,z4,z5,z959]),(0,[z150,z0,z1,z3,z184,z17]),(0,[z1,z3,z4,z5,z8,z793]),(0,[z0,z1,z3,z4,z5,z960]),(0,[z0,z1,z3,z947,z5,z17])],[(0,[z0,z1,z3,z4,z734,z6]),(0,[z0,z480,z3,z4,z102,z17])],[(0,[z0,z545,z1,z3,z4,z17]),(0,[z367,z23,z1,z3,z143,z5]),(0,[z0,z1,z3,z319,z5,z97]),(0,[z0,z1,z3,z961,z5,z6]),(0,[z0,z1,z3,z4,z577,z17]),(0,[z100,z0,z3,z4,z54,z6]),(0,[z0,z1,z3,z4,z787,z5]),(0,[z0,z23,z1,z3,z355,z4])],[(0,[z98,z1,z3,z4,z5,z793]),(0,[z74,z0,z420,z3,z4,z5])],[(0,[z0,z1,z962,z4,z5,z6]),(0,[z136,z0,z29,z4,z5,z6]),(0,[z0,z1,z963,z4,z5,z6]),(1,[z0,z3,z739,z5,z6]),(0,[z380,z0,z1,z3,z842,z6])],[(0,[z0,z1,z3,z4,z964,z6]),(0,[z0,z1,z3,z965,z5,z6]),(0,[z0,z1,z430,z4,z5,z6]),(0,[z0,z1,z3,z4,z232,z17]),(0,[z0,z318,z3,z319,z5,z6]),(0,[z0,z3,z4,z966,z5,z6]),(1,[z0,z1,z3,z4,z741])],[(0,[z72,z909,z3,z4,z5,z6]),(0,[z1,z3,z820,z4,z5,z6]),(0,[z0,z967,z3,z4,z5,z6]),(0,[z681,z0,z29,z4,z5,z6]),(0,[z0,z786,z29,z4,z5,z6]),(0,[z100,z0,z23,z3,z4,z54]),(0,[z0,z1,z3,z4,z225,z17])],[(0,[z0,z1,z3,z968,z5,z6]),(0,[z205,z23,z1,z27,z4,z5]),(0,[z0,z3,z4,z969,z5,z6]),(0,[z0,z1,z3,z138,z4,z17]),(0,[z846,z1,z3,z4,z5,z17]),(0,[z0,z847,z3,z4,z5,z17])]],
   [[(0,[z0,z1,z3,z4,z5,z970]),(0,[z0,z1,z3,z4,z971,z6]),(0,[z0,z1,z3,z4,z5,z972]),(0,[z120,z0,z23,z1,z4,z85]),(0,[z0,z1,z3,z842,z5,z6]),(0,[z0,z3,z4,z973,z5,z6]),(0,[z0,z1,z848,z4,z5,z17]),(0,[z664,z524,z1,z3,z4,z5])],[(0,[z0,z1,z96,z4,z5,z181]),(0,[z0,z1,z3,z4,z974,z5]),(0,[z0,z55,z3,z4,z102,z17]),(0,[z0,z1,z18,z4,z268,z17]),(0,[z0,z1,z975,z4,z5,z6])],[(0,[z0,z1,z976,z4,z5,z6]),(0,[z0,z977,z3,z4,z5,z6]),(0,[z0,z1,z3,z61,z842,z6])],[(0,[z0,z1,z3,z978,z4,z5]),(0,[z0,z1,z3,z4,z5,z979]),(0,[z0,z3,z4,z966,z5,z17])],[(0,[z0,z980,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z793,z6]),(0,[z42,z0,z165,z79,z5,z6]),(0,[z151,z0,z21,z142,z5,z6]),(0,[z0,z981,z3,z4,z5,z6]),(0,[z0,z1,z3,z982,z4,z5])],[(1,[z1,z718,z4,z5,z6]),(0,[z42,z0,z3,z739,z5,z6])],[(0,[z0,z23,z1,z3,z4,z17])],[(0,[z0,z1,z3,z983,z5,z6]),(0,[z0,z1,z3,z4,z5,z984]),(0,[z0,z1,z3,z4,z5,z985]),(0,[z136,z328,z0,z29,z5,z6]),(0,[z0,z1,z3,z4,z5,z986])]],
   [[(0,[z0,z1,z3,z4,z987,z6]),(0,[z988,z1,z3,z4,z5,z6]),(0,[z0,z455,z1,z3,z4,z71]),(0,[z0,z1,z3,z4,z616,z17])],[(0,[z0,z1,z989,z3,z4,z5]),(0,[z0,z990,z3,z4,z5,z6]),(0,[z1,z3,z4,z58,z708,z6]),(0,[z0,z991,z3,z4,z5,z6]),(0,[z0,z1,z860,z4,z5,z17])],[(0,[z0,z1,z992,z4,z5,z6]),(0,[z0,z1,z4,z993,z5,z6]),(0,[z0,z1,z3,z4,z268,z17]),(0,[z0,z1,z3,z274,z62,z17])],[(0,[z0,z1,z3,z994,z5,z6]),(0,[z0,z1,z3,z4,z5,z995]),(0,[z0,z1,z863,z4,z5,z17])],[(0,[z0,z1,z996,z4,z5,z6]),(0,[z150,z0,z1,z96,z4,z17])],[(0,[z265,z0,z1,z3,z4,z17]),(0,[z44,z0,z1,z239,z4,z5])],[(0,[z0,z1,z3,z4,z620,z17]),(0,[z42,z0,z21,z3,z5,z6]),(0,[z0,z273,z1,z3,z4,z17])],[(0,[z233,z0,z29,z4,z5,z6]),(0,[z0,z1,z3,z4,z199,z17])]],
   [[(1,[z0,z1,z782,z5,z6])],[(0,[z0,z1,z3,z4,z5,z478])],[(0,[z0,z997,z1,z3,z4,z6]),(0,[z0,z1,z3,z341,z4,z5]),(0,[z0,z43,z3,z739,z5,z6]),(0,[z0,z14,z173,z3,z4,z5]),(0,[z0,z1,z3,z4,z329,z17])],[(0,[z0,z998,z1,z3,z4,z5]),(0,[z64,z23,z76,z3,z4,z5]),(0,[z0,z999,z3,z4,z5,z6]),(0,[z0,z1,z1000,z4,z5,z6]),(0,[z0,z1001,z3,z4,z5,z6]),(1,[z0,z1,z4,z713,z5])],[(0,[z0,z1,z3,z4,z5,z1002])],[(0,[z1003,z1,z3,z4,z5,z6]),(0,[z0,z1,z70,z4,z5,z103])],[(0,[z0,z1,z1004,z3,z4,z5]),(0,[z77,z0,z1,z3,z4,z17]),(0,[z0,z19,z20,z4,z5,z6]),(0,[z1005,z0,z1,z4,z5,z6]),(0,[z0,z1,z141,z782,z5,z6])],[(0,[z0,z213,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z1006]),(0,[z150,z107,z3,z4,z186,z6]),(0,[z254,z0,z1,z3,z304,z5]),(0,[z0,z1,z3,z304,z4,z227]),(0,[z0,z1,z3,z4,z1007,z6]),(0,[z0,z715,z1,z3,z4,z5])],[(0,[z76,z909,z3,z4,z5,z6]),(0,[z0,z1,z1008,z3,z4,z6]),(0,[z0,z1,z231,z165,z5,z6]),(0,[z0,z1,z1009,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1010]),(0,[z0,z1011,z1,z3,z4,z5]),(0,[z0,z1,z173,z3,z4,z17])],[(0,[z0,z1,z3,z4,z5,z1012]),(0,[z0,z1,z3,z4,z654,z17]),(0,[z42,z0,z3,z79,z5,z17]),(0,[z0,z273,z544,z3,z4,z5])],[(0,[z0,z43,z231,z29,z5,z6]),(0,[z0,z43,z21,z3,z5,z6])],[(0,[z0,z1,z3,z4,z621,z17]),(0,[z0,z1,z3,z1013,z5,z6]),(0,[z330,z1,z3,z4,z5,z8]),(0,[z0,z19,z20,z4,z5,z17]),(0,[z0,z1,z3,z4,z1014,z6]),(0,[z0,z1,z3,z4,z147,z17])],[(0,[z0,z1015,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1016]),(0,[z664,z1,z3,z4,z5,z8]),(0,[z0,z55,z3,z4,z102,z307]),(0,[z0,z1,z3,z4,z251,z15]),(0,[z0,z213,z3,z4,z5,z17]),(0,[z0,z1,z4,z85,z765,z6])],[(0,[z0,z491,z3,z4,z5,z17]),(0,[z0,z29,z4,z539,z5,z6]),(0,[z0,z1,z3,z896,z5,z17])],[(0,[z0,z1,z430,z4,z5,z97]),(0,[z0,z23,z1,z3,z175,z5]),(0,[z0,z1,z3,z4,z1017,z5])]],
   [[(0,[z0,z1,z1018,z4,z5,z6]),(0,[z0,z1019,z3,z4,z5,z6]),(0,[z98,z0,z1,z3,z4,z227]),(0,[z0,z1,z3,z4,z5,z1020])],[(0,[z0,z23,z43,z3,z159,z5]),(0,[z0,z1,z70,z239,z4,z5])],[(0,[z0,z1,z27,z4,z268,z17]),(0,[z180,z23,z1,z3,z11,z5]),(1,[z0,z107,z3,z4,z17]),(0,[z0,z107,z430,z4,z5,z6]),(0,[z0,z318,z430,z4,z5,z6]),(0,[z1021,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z108,z17])],[(0,[z0,z1,z3,z4,z1022,z6]),(0,[z98,z449,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z113,z17])],[(0,[z64,z909,z3,z4,z5,z6]),(0,[z0,z318,z3,z4,z5,z181]),(0,[z0,z1,z3,z319,z5,z181]),(0,[z1023,z1,z3,z4,z5,z6]),(0,[z0,z1,z1024,z4,z5,z6]),(0,[z0,z1,z3,z902,z5,z17])],[(0,[z0,z1,z3,z1025,z4,z6])],[(0,[z0,z744,z3,z4,z5,z6])],[(0,[z582,z1,z3,z11,z5,z6]),(0,[z0,z23,z107,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z4,z5,z1026]),(0,[z72,z89,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z5,z1027]),(0,[z0,z1028,z3,z4,z5,z6])],[(0,[z367,z1,z3,z820,z5,z6]),(0,[z0,z1,z3,z293,z62,z6]),(0,[z0,z1,z3,z4,z227,z6]),(0,[z7,z1,z3,z4,z8,z227]),(0,[z0,z1,z3,z4,z1029,z6])],[(0,[z0,z1,z106,z4,z5,z17]),(0,[z367,z1,z3,z143,z5,z6]),(0,[z0,z1,z3,z4,z102,z17])],[(0,[z0,z313,z1,z3,z4,z17]),(0,[z0,z1,z4,z765,z5,z6]),(0,[z607,z0,z1,z3,z4,z17]),(0,[z0,z1,z4,z1030,z5,z6])],[(0,[z0,z488,z20,z4,z5,z6]),(0,[z0,z455,z1,z3,z4,z17])],[(0,[z0,z1,z3,z1031,z5,z6]),(0,[z0,z1,z3,z138,z4,z5])],[(0,[z0,z1,z3,z223,z5,z12]),(1,[z0,z1,z430,z4,z17]),(0,[z150,z1,z3,z184,z186,z6])],[(0,[z0,z1,z3,z33,z5,z12]),(0,[z0,z1,z3,z341,z534,z5]),(0,[z0,z1,z3,z4,z1032,z5]),(0,[z74,z0,z3,z4,z301,z5]),(0,[z0,z1,z109,z4,z765,z6]),(0,[z1,z3,z4,z5,z756,z6])]],
   [[(0,[z0,z1,z3,z1033,z5,z6]),(0,[z0,z1034,z3,z4,z5,z6]),(0,[z0,z1,z1035,z4,z5,z6])],[(0,[z206,z1,z28,z4,z5,z6]),(0,[z0,z1036,z3,z4,z5,z6]),(0,[z0,z1037,z3,z4,z5,z6]),(0,[z0,z23,z55,z3,z4,z102]),(0,[z0,z23,z368,z1,z3,z4]),(0,[z0,z1,z3,z237,z274,z62]),(0,[z0,z1,z4,z1030,z5,z17])],[(0,[z205,z179,z27,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z793])],[(0,[z0,z1,z3,z1038,z5,z6]),(0,[z0,z1,z3,z4,z1039,z6]),(0,[z0,z23,z1,z430,z4,z5]),(0,[z151,z0,z1,z142,z5,z6]),(0,[z0,z1,z109,z4,z268,z17]),(0,[z0,z1,z3,z4,z93,z17])],[(0,[z37,z89,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z600,z17]),(0,[z0,z1040,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z71,z17])],[(0,[z1041,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z534,z5,z6]),(0,[z328,z0,z3,z79,z5,z6]),(0,[z0,z1,z3,z29,z4,z741]),(0,[z380,z0,z1,z3,z61,z17])],[(0,[z0,z1042,z1,z3,z4,z5]),(0,[z0,z404,z1,z3,z4,z17]),(0,[z0,z1,z231,z141,z5,z6]),(0,[z284,z0,z1,z3,z4,z17]),(0,[z0,z23,z1,z3,z841,z5])]],
   [[(0,[z150,z1,z96,z4,z186,z6]),(0,[z0,z1,z3,z4,z5,z1043]),(0,[z0,z1,z3,z842,z4,z6]),(0,[z1044,z1,z3,z4,z5,z6])],[(0,[z1045,z1,z3,z4,z5,z6]),(0,[z328,z130,z0,z1,z3,z5]),(0,[z151,z0,z1,z142,z5,z17]),(0,[z380,z0,z1,z3,z61,z243]),(0,[z457,z0,z1,z3,z4,z17])],[(0,[z160,z1,z3,z143,z5,z6]),(0,[z0,z1,z3,z1046,z5,z6]),(0,[z1047,z1,z3,z4,z5,z6]),(0,[z0,z1,z448,z3,z4,z262]),(0,[z0,z1,z3,z782,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1048]),(0,[z0,z1,z3,z4,z703,z17])],[(0,[z205,z1,z27,z4,z5,z6]),(0,[z150,z1,z3,z4,z186,z17]),(0,[z0,z1,z3,z4,z463,z17]),(0,[z0,z480,z3,z4,z5,z682])],[(0,[z0,z1,z10,z4,z5,z6]),(0,[z259,z57,z1,z3,z4,z17]),(0,[z0,z19,z786,z4,z5,z6]),(0,[z0,z1,z231,z141,z5,z17]),(0,[z120,z0,z1,z138,z4,z85])],[(0,[z0,z23,z1,z3,z319,z5]),(0,[z0,z3,z786,z4,z5,z6]),(0,[z0,z21,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1049])],[(0,[z0,z1,z3,z4,z5,z1050]),(0,[z0,z1051,z1,z3,z4,z5]),(0,[z1044,z23,z1,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z1052,z4,z6]),(0,[z476,z1,z28,z4,z5,z6]),(0,[z0,z1053,z3,z4,z5,z6])],[(1,[z909,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1054]),(0,[z0,z1,z3,z4,z1055,z5]),(0,[z136,z130,z0,z29,z4,z5]),(0,[z151,z0,z1,z165,z5,z6]),(0,[z0,z481,z3,z4,z54,z6])],[(0,[z205,z1,z27,z4,z5,z17]),(0,[z0,z1056,z3,z4,z5,z6]),(0,[z0,z1,z3,z537,z5,z12]),(0,[z0,z1,z1057,z4,z5,z6]),(0,[z0,z1058,z3,z4,z5,z6]),(0,[z0,z1,z3,z927,z4,z85]),(0,[z0,z1,z3,z4,z1059,z5])],[(0,[z0,z1,z3,z4,z5,z1060]),(0,[z328,z0,z1,z3,z341,z5]),(0,[z100,z0,z3,z4,z54,z17])],[(0,[z0,z1,z3,z4,z5,z1061]),(0,[z57,z1,z3,z4,z531,z6]),(0,[z0,z1,z3,z4,z5,z1062]),(0,[z0,z1,z3,z1063,z4,z5]),(0,[z0,z1,z3,z4,z5,z741])],[(0,[z136,z0,z29,z4,z5,z17])],[(0,[z0,z1,z430,z4,z5,z17]),(0,[z259,z1,z3,z4,z5,z24]),(0,[z328,z0,z1,z142,z5,z6]),(0,[z0,z1,z3,z4,z102,z307]),(0,[z0,z1,z109,z4,z268,z52])],[(0,[z0,z1,z3,z4,z5,z1064]),(0,[z0,z14,z1,z3,z4,z71])]],
   [[(0,[z1,z3,z4,z708,z186,z6]),(0,[z0,z43,z165,z4,z5,z6]),(0,[z0,z23,z21,z3,z4,z5])],[(0,[z0,z76,z3,z4,z102,z17]),(0,[z0,z1,z3,z1065,z5,z6]),(0,[z0,z43,z3,z159,z5,z6]),(0,[z0,z1,z3,z762,z4,z5]),(0,[z0,z3,z4,z973,z5,z17])],[(0,[z0,z1,z3,z4,z5,z1066]),(0,[z0,z796,z3,z4,z5,z6]),(0,[z0,z1,z975,z4,z5,z17])],[(0,[z0,z1,z3,z1067,z5,z6]),(0,[z0,z1,z3,z4,z5,z1068]),(0,[z0,z1,z3,z820,z5,z6]),(0,[z0,z1,z1069,z4,z5,z6]),(0,[z1070,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z227,z12]),(0,[z0,z3,z4,z54,z734,z6]),(0,[z0,z1,z3,z4,z87,z17])],[(0,[z206,z23,z1,z28,z4,z5]),(0,[z0,z1071,z1,z3,z4,z5])],[(0,[z0,z1,z1072,z4,z5,z6]),(0,[z0,z1073,z3,z4,z5,z6]),(0,[z265,z0,z23,z1,z3,z4]),(0,[z0,z1,z3,z4,z99,z17]),(0,[z0,z1,z70,z3,z4,z251]),(0,[z0,z1,z3,z562,z5,z12])],[(0,[z0,z1,z3,z4,z442,z17]),(0,[z74,z0,z1,z3,z4,z71])]],
   [[(0,[z0,z1,z4,z1074,z5,z6]),(0,[z151,z0,z213,z142,z5,z6])],[(0,[z490,z0,z29,z4,z5,z6]),(0,[z0,z107,z3,z4,z6,z17]),(0,[z0,z1,z3,z4,z741,z6]),(0,[z0,z1,z231,z189,z5,z6])],[(0,[z0,z1,z3,z4,z118,z17]),(0,[z0,z1,z732,z3,z4,z5]),(0,[z0,z1,z3,z842,z62,z6])],[(0,[z1075,z0,z1,z4,z5,z6]),(0,[z0,z1076,z3,z4,z5,z6]),(0,[z265,z0,z1,z3,z4,z181]),(0,[z0,z1,z3,z4,z5,z1077]),(0,[z0,z1,z4,z993,z5,z17])],[(0,[z0,z1,z3,z4,z1078,z6]),(0,[z367,z1,z3,z143,z5,z133]),(0,[z0,z1,z3,z4,z5,z635]),(0,[z328,z0,z1,z165,z5,z6]),(0,[z0,z14,z3,z4,z5,z15]),(0,[z0,z1,z4,z16,z268,z17])],[],[(0,[z0,z1,z3,z927,z4,z5])],[]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 535) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 535).take 533) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1068).take 93) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1161)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [535, 533, 93] = true :=
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

end PEqualNP.Outside.L_meta_41488

theorem PEqualNP.Outside.L_meta_41488 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4276791296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4276791296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41488.solve