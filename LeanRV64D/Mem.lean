import LeanRV64D.Flow
import LeanRV64D.Prelude
import LeanRV64D.Errors
import LeanRV64D.MemAddrtype
import LeanRV64D.MemMetadata
import LeanRV64D.PhysMemInterface
import LeanRV64D.PlatformConfig
import LeanRV64D.Types
import LeanRV64D.VmemTypes
import LeanRV64D.MemTypeUtils
import LeanRV64D.Callbacks
import LeanRV64D.PmpControl
import LeanRV64D.SysControl
import LeanRV64D.Platform
import LeanRV64D.Pma

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

noncomputable section

namespace LeanRV64D.Functions

open zvk_vsm4r_funct6
open zvk_vsha2_funct6
open zvk_vaesem_funct6
open zvk_vaesef_funct6
open zvk_vaesdm_funct6
open zvk_vaesdf_funct6
open zicondop
open xRET_type
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open wrsop
open write_kind
open wmvxfunct6
open wmvvfunct6
open vxsgfunct6
open vxmsfunct6
open vxmfunct6
open vxmcfunct6
open vxfunct6
open vxcmpfunct6
open vvmsfunct6
open vvmfunct6
open vvmcfunct6
open vvfunct6
open vvcmpfunct6
open vregno
open vregidx
open vmlsop
open vlewidth
open visgfunct6
open virtaddr
open vimsfunct6
open vimfunct6
open vimcfunct6
open vifunct6
open vicmpfunct6
open vfwunary0
open vfunary1
open vfunary0
open vfnunary0
open vextfunct6
open vector_support
open uop
open stateen_bit
open sopw
open sop
open seed_opst
open rounding_mode
open ropw
open rop
open rmvvfunct6
open rivvfunct6
open rfwvvfunct6
open rfvvfunct6
open regno
open regidx
open read_kind
open pte_check_failure
open pmpAddrMatch
open physaddr
open option
open nxsfunct6
open nxfunct6
open nvsfunct6
open nvfunct6
open ntl_type
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open misaligned_fault
open mem_payload
open maskfunct3
open landing_pad_expectation
open iop
open instruction
open indexed_mop
open fwvvmafunct6
open fwvvfunct6
open fwvfunct6
open fwvfmafunct6
open fwvffunct6
open fwffunct6
open fvvmfunct6
open fvvmafunct6
open fvvfunct6
open fvfmfunct6
open fvfmafunct6
open fvffunct6
open fregno
open fregidx
open float_class
open f_un_x_op_H
open f_un_x_op_D
open f_un_rm_xf_op_S
open f_un_rm_xf_op_H
open f_un_rm_xf_op_D
open f_un_rm_fx_op_S
open f_un_rm_fx_op_H
open f_un_rm_fx_op_D
open f_un_rm_ff_op_S
open f_un_rm_ff_op_H
open f_un_rm_ff_op_D
open f_un_op_x_S
open f_un_op_f_S
open f_un_f_op_H
open f_un_f_op_D
open f_madd_op_S
open f_madd_op_H
open f_madd_op_D
open f_bin_x_op_H
open f_bin_x_op_D
open f_bin_rm_op_S
open f_bin_rm_op_H
open f_bin_rm_op_D
open f_bin_op_x_S
open f_bin_op_f_S
open f_bin_f_op_H
open f_bin_f_op_D
open extop_zbb
open extension
open exception
open ctl_result
open csrop
open cregidx
open checked_cbop
open cfregidx
open cbop_zicbop
open cbop_zicbom
open cbie
open cacheop
open bropw_zbb
open brop_zbs
open brop_zbkb
open brop_zbb
open breakpoint_cause
open bop
open biop_zbs
open barrier_kind
open amoop
open agtype
open XenvcfgCbieReservedBehavior
open WaitReason
open VectorHalf
open TrapVectorMode
open TrapCause
open Step
open Software_Check_Code
open Signedness
open SWCheckCodes
open SATPMode
open Reservability
open Register
open Privilege
open PmpWriteOnlyReservedBehavior
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open MemoryAccessType
open InterruptType
open ISA_Format
open HartState
open FetchResult
open Ext_DataAddr_Check
open ExtStatus
open ExecutionResult
open ExceptionType
open CSRAccessType
open AtomicSupport
open Architecture
open AmocasOddRegisterReservedBehavior

/-- Type quantifiers: width : Nat, width > 0 -/
def is_aligned_paddr (typ_0 : physaddr) (width : Nat) : Bool :=
  let .Physaddr addr : physaddr := typ_0
  ((Int.tmod (BitVec.toNatInt addr) width) == 0)

/-- Type quantifiers: width : Nat, width > 0 -/
def is_aligned_vaddr (typ_0 : virtaddr) (width : Nat) : Bool :=
  let .Virtaddr addr : virtaddr := typ_0
  ((Int.tmod (BitVec.toNatInt addr) width) == 0)

/-- Type quantifiers: k_ex754654_ : Bool, k_ex754653_ : Bool, k_ex754652_ : Bool -/
def read_kind_of_flags (aq : Bool) (rl : Bool) (res : Bool) : SailM read_kind := do
  match (aq, rl, res) with
  | (false, false, false) => (pure Read_plain)
  | (true, false, false) =>
    (internal_error "sys/mem.sail" 52 "Unreserved load with acquire semantics should be unreachable")
  | (true, true, false) =>
    (internal_error "sys/mem.sail" 53
      "Unreserved load with acquire-release semantics should be unreachable")
  | (false, false, true) => (pure Read_RISCV_reserved)
  | (true, false, true) => (pure Read_RISCV_reserved_acquire)
  | (true, true, true) => (pure Read_RISCV_reserved_strong_acquire)
  | (false, true, false) =>
    (internal_error "sys/mem.sail" 58 "Unreserved Load with release semantics should be unreachable")
  | (false, true, true) =>
    (internal_error "sys/mem.sail" 59 "Load-reserved with release semantics should be unreachable")

/-- Type quantifiers: k_ex754660_ : Bool, k_ex754659_ : Bool, k_ex754658_ : Bool -/
def write_kind_of_flags (aq : Bool) (rl : Bool) (con : Bool) : SailM write_kind := do
  match (aq, rl, con) with
  | (false, false, false) => (pure Write_plain)
  | (false, true, false) =>
    (internal_error "sys/mem.sail" 65
      "Unconditional store with release semantics should be unreachable")
  | (false, false, true) => (pure Write_RISCV_conditional)
  | (false, true, true) => (pure Write_RISCV_conditional_release)
  | (true, true, false) =>
    (internal_error "sys/mem.sail" 68
      "Unconditional store with acquire-release semantics should be unreachable")
  | (true, true, true) => (pure Write_RISCV_conditional_strong_release)
  | (true, false, false) =>
    (internal_error "sys/mem.sail" 71
      "Unconditional store with acquire semantics should be unreachable")
  | (true, false, true) =>
    (internal_error "sys/mem.sail" 72
      "Store-conditional with acquire semantics should be unreachable")

/-- Type quantifiers: k_ex754664_ : Bool, width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def pmaCheck (paddr : physaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (res_or_con : Bool) : SailM (Option ExceptionType) := do
  match (matching_pma (← readReg pma_regions) paddr width) with
  | none => (pure (some (accessFaultFromAccessType access)))
  | .some { attributes := attributes, size := _, include_in_device_tree := _, base := _ } =>
    (do
      let misaligned := (not (is_aligned_paddr paddr width))
      match attributes.misaligned_fault with
      | AccessFault =>
        (do
          if (misaligned : Bool)
          then (pure (some (accessFaultFromAccessType access)))
          else
            (do
              let canAccess ← (( do
                match access with
                | .InstructionFetch () => (pure attributes.executable)
                | .Load _ =>
                  (do
                    assert (not res_or_con) "sys/mem.sail:96.58-96.59"
                    (pure attributes.readable))
                | .Store _ => (pure attributes.writable)
                | .LoadReserved _ =>
                  (do
                    assert res_or_con "sys/mem.sail:102.53-102.54"
                    (pure (attributes.readable && (bne attributes.reservability RsrvNone))))
                | .StoreConditional _ =>
                  (do
                    assert res_or_con "sys/mem.sail:103.53-103.54"
                    (pure (attributes.writable && (bne attributes.reservability RsrvNone))))
                | .Atomic (_, _, _) =>
                  (do
                    assert res_or_con "sys/mem.sail:106.53-106.54"
                    (pure (attributes.readable && attributes.writable)))
                | .CacheAccess (.CB_zero ()) =>
                  (pure (attributes.writable && attributes.supports_cbo_zero))
                | .CacheAccess (.CB_manage _) => (pure (attributes.readable || attributes.writable))
                | .CacheAccess (.CB_prefetch p) =>
                  (match p with
                  | PREFETCH_R => (pure attributes.readable)
                  | PREFETCH_W => (pure attributes.writable)
                  | PREFETCH_I => (pure attributes.executable)) ) : SailM Bool )
              let _ : Unit :=
                if (((get_config_print_pma ()) && (not canAccess)) : Bool)
                then
                  (print_endline
                    (HAppend.hAppend "PMA check failed for "
                      (HAppend.hAppend (hex_bits_str (bits_of_physaddr paddr))
                        (HAppend.hAppend " PMA " (pma_attributes_to_str attributes)))))
                else ()
              if (canAccess : Bool)
              then (pure none)
              else (pure (some (accessFaultFromAccessType access)))))
      | AlignmentFault =>
        (do
          if (misaligned : Bool)
          then (pure (some (alignmentFaultFromAccessType access)))
          else
            (do
              let canAccess ← (( do
                match access with
                | .InstructionFetch () => (pure attributes.executable)
                | .Load _ =>
                  (do
                    assert (not res_or_con) "sys/mem.sail:96.58-96.59"
                    (pure attributes.readable))
                | .Store _ => (pure attributes.writable)
                | .LoadReserved _ =>
                  (do
                    assert res_or_con "sys/mem.sail:102.53-102.54"
                    (pure (attributes.readable && (bne attributes.reservability RsrvNone))))
                | .StoreConditional _ =>
                  (do
                    assert res_or_con "sys/mem.sail:103.53-103.54"
                    (pure (attributes.writable && (bne attributes.reservability RsrvNone))))
                | .Atomic (_, _, _) =>
                  (do
                    assert res_or_con "sys/mem.sail:106.53-106.54"
                    (pure (attributes.readable && attributes.writable)))
                | .CacheAccess (.CB_zero ()) =>
                  (pure (attributes.writable && attributes.supports_cbo_zero))
                | .CacheAccess (.CB_manage _) => (pure (attributes.readable || attributes.writable))
                | .CacheAccess (.CB_prefetch p) =>
                  (match p with
                  | PREFETCH_R => (pure attributes.readable)
                  | PREFETCH_W => (pure attributes.writable)
                  | PREFETCH_I => (pure attributes.executable)) ) : SailM Bool )
              let _ : Unit :=
                if (((get_config_print_pma ()) && (not canAccess)) : Bool)
                then
                  (print_endline
                    (HAppend.hAppend "PMA check failed for "
                      (HAppend.hAppend (hex_bits_str (bits_of_physaddr paddr))
                        (HAppend.hAppend " PMA " (pma_attributes_to_str attributes)))))
                else ()
              if (canAccess : Bool)
              then (pure none)
              else (pure (some (accessFaultFromAccessType access)))))
      | _ =>
        (do
          let canAccess ← (( do
            match access with
            | .InstructionFetch () => (pure attributes.executable)
            | .Load _ =>
              (do
                assert (not res_or_con) "sys/mem.sail:96.58-96.59"
                (pure attributes.readable))
            | .Store _ => (pure attributes.writable)
            | .LoadReserved _ =>
              (do
                assert res_or_con "sys/mem.sail:102.53-102.54"
                (pure (attributes.readable && (bne attributes.reservability RsrvNone))))
            | .StoreConditional _ =>
              (do
                assert res_or_con "sys/mem.sail:103.53-103.54"
                (pure (attributes.writable && (bne attributes.reservability RsrvNone))))
            | .Atomic (_, _, _) =>
              (do
                assert res_or_con "sys/mem.sail:106.53-106.54"
                (pure (attributes.readable && attributes.writable)))
            | .CacheAccess (.CB_zero ()) =>
              (pure (attributes.writable && attributes.supports_cbo_zero))
            | .CacheAccess (.CB_manage _) => (pure (attributes.readable || attributes.writable))
            | .CacheAccess (.CB_prefetch p) =>
              (match p with
              | PREFETCH_R => (pure attributes.readable)
              | PREFETCH_W => (pure attributes.writable)
              | PREFETCH_I => (pure attributes.executable)) ) : SailM Bool )
          let _ : Unit :=
            if (((get_config_print_pma ()) && (not canAccess)) : Bool)
            then
              (print_endline
                (HAppend.hAppend "PMA check failed for "
                  (HAppend.hAppend (hex_bits_str (bits_of_physaddr paddr))
                    (HAppend.hAppend " PMA " (pma_attributes_to_str attributes)))))
            else ()
          if (canAccess : Bool)
          then (pure none)
          else (pure (some (accessFaultFromAccessType access)))))

def alignmentOrAccessFaultPriority (exc : ExceptionType) : SailM Nat := do
  match exc with
  | .E_Fetch_Access_Fault () => (pure 1)
  | .E_Load_Access_Fault () => (pure 1)
  | .E_SAMO_Access_Fault () => (pure 1)
  | .E_Fetch_Addr_Align () => (pure 0)
  | .E_Load_Addr_Align () => (pure 0)
  | .E_SAMO_Addr_Align () => (pure 0)
  | _ =>
    (internal_error "sys/mem.sail" 162
      (HAppend.hAppend "Invalid exception: " (exceptionType_to_str exc)))

def highestPriorityAlignmentOrAccessFault (l : ExceptionType) (r : ExceptionType) : SailM ExceptionType := do
  if (((← (alignmentOrAccessFaultPriority l)) >b (← (alignmentOrAccessFaultPriority r))) : Bool)
  then (pure l)
  else (pure r)

/-- Type quantifiers: k_ex754760_ : Bool, width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def phys_access_check (access : (MemoryAccessType mem_payload)) (priv : Privilege) (paddr : physaddr) (width : Nat) (res_or_con : Bool) : SailM (Option ExceptionType) := do
  let pmpError ← (( do (pmpCheck paddr width access priv) ) : SailM (Option ExceptionType) )
  let pmaError ← (( do (pmaCheck paddr width access res_or_con) ) : SailM (Option ExceptionType) )
  match (pmpError, pmaError) with
  | (none, none) => (pure none)
  | (.some e, none) => (pure (some e))
  | (none, .some e) => (pure (some e))
  | (.some e0, .some e1) => (pure (some (← (highestPriorityAlignmentOrAccessFault e0 e1))))

/-- Type quantifiers: k_ex754765_ : Bool, k_ex754764_ : Bool, k_ex754763_ : Bool, k_ex754762_ : Bool, width
  : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def checked_mem_read (access : (MemoryAccessType mem_payload)) (priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta' : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) ExceptionType) := do
  match (← (phys_access_check access priv paddr width res)) with
  | .some e => (pure (Err e))
  | none =>
    (do
      if ((← (within_mmio_readable paddr width)) : Bool)
      then (pure (MemoryOpResult_add_meta (← (mmio_read access paddr width)) default_meta))
      else
        (do
          let rk ← do (read_kind_of_flags aq rl res)
          (pure (Ok (← (read_ram rk paddr width meta'))))))

/-- Type quantifiers: k_ex754774_ : Bool, k_ex754773_ : Bool, k_ex754772_ : Bool, k_ex754771_ : Bool, width
  : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_read_priv_meta (access : (MemoryAccessType mem_payload)) (priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta' : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) ExceptionType) := do
  let result ← (( do
    if (((aq || res) && (not (is_aligned_paddr paddr width))) : Bool)
    then (pure (Err (E_Load_Addr_Align ())))
    else
      (do
        match (aq, rl, res) with
        | (false, true, false) => sailThrow ((Error_not_implemented "load.rl"))
        | (false, true, true) => sailThrow ((Error_not_implemented "lr.rl"))
        | (_, _, _) => (checked_mem_read access priv paddr width aq rl res meta')) ) : SailM
    (MemoryOpResult ((BitVec (8 * width)) × mem_meta)) )
  let _ : Unit :=
    match result with
    | .Ok (value, _) =>
      (mem_read_callback (accessType_to_str access) (bits_of_physaddr paddr) width value)
    | .Err e => (mem_exception_callback (bits_of_physaddr paddr) (exceptionType_bits_forwards e))
  (pure result)

/-- Type quantifiers: k_ex754828_ : Bool, k_ex754827_ : Bool, k_ex754826_ : Bool, k_ex754825_ : Bool, width
  : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_read_meta (access : (MemoryAccessType mem_payload)) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta' : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) ExceptionType) := do
  (mem_read_priv_meta access
    (← (effectivePrivilege access (← readReg mstatus) (← readReg cur_privilege))) paddr width
    aq rl res meta')

/-- Type quantifiers: k_ex754831_ : Bool, k_ex754830_ : Bool, k_ex754829_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_read_priv (access : (MemoryAccessType mem_payload)) (priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExceptionType) := do
  (pure (MemoryOpResult_drop_meta (← (mem_read_priv_meta access priv paddr width aq rl res false))))

/-- Type quantifiers: k_ex754834_ : Bool, k_ex754833_ : Bool, k_ex754832_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_read (access : (MemoryAccessType mem_payload)) (paddr : physaddr) (width : Nat) (aq : Bool) (rel : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExceptionType) := do
  (mem_read_priv access
    (← (effectivePrivilege access (← readReg mstatus) (← readReg cur_privilege))) paddr width
    aq rel res)

/-- Type quantifiers: k_ex754837_ : Bool, k_ex754836_ : Bool, k_ex754835_ : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def mem_write_ea (addr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Unit ExceptionType) := do
  if (((rl || con) && (not (is_aligned_paddr addr width))) : Bool)
  then (pure (Err (E_SAMO_Addr_Align ())))
  else (pure (Ok (write_ram_ea (← (write_kind_of_flags aq rl con)) addr width)))

/-- Type quantifiers: k_ex754848_ : Bool, k_ex754847_ : Bool, k_ex754846_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def checked_mem_write (paddr : physaddr) (width : Nat) (data : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (meta' : Unit) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  match (← (phys_access_check access priv paddr width con)) with
  | .some e => (pure (Err e))
  | none =>
    (do
      if ((← (within_mmio_writable paddr width)) : Bool)
      then (mmio_write paddr width data)
      else
        (do
          let wk ← do (write_kind_of_flags aq rl con)
          (pure (Ok (← (write_ram wk paddr width data meta'))))))

/-- Type quantifiers: k_ex754860_ : Bool, k_ex754859_ : Bool, k_ex754858_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_write_value_priv_meta (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (meta' : Unit) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  if (((rl || con) && (not (is_aligned_paddr paddr width))) : Bool)
  then (pure (Err (E_SAMO_Addr_Align ())))
  else
    (do
      let result ← do (checked_mem_write paddr width value access priv meta' aq rl con)
      let _ : Unit :=
        match result with
        | .Ok _ =>
          (mem_write_callback (accessType_to_str access) (bits_of_physaddr paddr) width value)
        | .Err e =>
          (mem_exception_callback (bits_of_physaddr paddr) (exceptionType_bits_forwards e))
      (pure result))

/-- Type quantifiers: k_ex754872_ : Bool, k_ex754871_ : Bool, k_ex754870_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_write_value_priv (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (priv : Privilege) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  (mem_write_value_priv_meta paddr width value (Store default_write_acc) priv default_meta aq rl con)

/-- Type quantifiers: k_ex754875_ : Bool, k_ex754874_ : Bool, k_ex754873_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_write_value_meta (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (payload : mem_payload) (meta' : Unit) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  let access := (Store payload)
  let ep ← do (effectivePrivilege access (← readReg mstatus) (← readReg cur_privilege))
  (mem_write_value_priv_meta paddr width value access ep meta' aq rl con)

/-- Type quantifiers: k_ex754878_ : Bool, k_ex754877_ : Bool, k_ex754876_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_write_value (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  (mem_write_value_meta paddr width value default_write_acc default_meta aq rl con)

