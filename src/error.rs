// Copyright 2016 6WIND S.A. <quentin.monnet@6wind.com>
//
// Licensed under the Apache License, Version 2.0 <http://www.apache.org/licenses/LICENSE-2.0> or
// the MIT license <http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! This module contains error and result types

use {
    crate::{elf::ElfError, memory_region::AccessType, verifier::VerifierError},
    std::error::Error,
};

/// Error definitions
#[derive(Debug)]
#[repr(u64)] // discriminant size, used in emit_exception_kind in JIT
pub enum EbpfError {
    /// ELF error
    ElfError(ElfError),
    /// Function was already registered
    FunctionAlreadyRegistered(usize),
    /// Exceeded max BPF to BPF call depth
    CallDepthExceeded,
    /// Attempt to exit from root call frame
    ExitRootCallFrame,
    /// Divide by zero"
    DivideByZero,
    /// Divide overflow
    DivideOverflow,
    /// Exceeded max instructions allowed
    ExecutionOverrun,
    /// Attempt to call to an address outside the text segment
    CallOutsideTextSegment,
    /// Exceeded max instructions allowed
    ExceededMaxInstructions,
    /// Program has not been JIT-compiled
    JitNotCompiled,
    /// Invalid virtual address
    InvalidVirtualAddress(u64),
    /// Memory region index or virtual address space is invalid
    InvalidMemoryRegion(usize),
    /// Access violation (general)
    AccessViolation(AccessType, u64, u64, &'static str),
    /// Access violation (stack specific)
    StackAccessViolation(AccessType, u64, u64, i64),
    /// Invalid instruction
    InvalidInstruction,
    /// Unsupported instruction
    UnsupportedInstruction,
    /// Compilation is too big to fit
    ExhaustedTextSegment(usize),
    /// Libc function call returned an error
    LibcInvocationFailed(&'static str, Vec<String>, i32),
    /// Verifier error
    VerifierError(VerifierError),
    /// Syscall error
    SyscallError(Box<dyn Error>),
}

#[allow(unused_qualifications)]
impl std::error::Error for EbpfError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        use EbpfError::{
            AccessViolation, CallDepthExceeded, CallOutsideTextSegment, DivideByZero,
            DivideOverflow, ElfError, ExceededMaxInstructions, ExecutionOverrun,
            ExhaustedTextSegment, ExitRootCallFrame, FunctionAlreadyRegistered, InvalidInstruction,
            InvalidMemoryRegion, InvalidVirtualAddress, JitNotCompiled, LibcInvocationFailed,
            StackAccessViolation, SyscallError, UnsupportedInstruction, VerifierError,
        };
        match self {
            ElfError(source) => Some(source),
            CallDepthExceeded
            | ExitRootCallFrame
            | FunctionAlreadyRegistered(_)
            | InvalidVirtualAddress(_)
            | InvalidMemoryRegion(_)
            | AccessViolation(..)
            | DivideByZero
            | DivideOverflow
            | ExecutionOverrun
            | CallOutsideTextSegment
            | ExceededMaxInstructions
            | JitNotCompiled
            | InvalidInstruction
            | StackAccessViolation(..)
            | ExhaustedTextSegment(_)
            | LibcInvocationFailed(..)
            | SyscallError(_)
            | UnsupportedInstruction => None,
            VerifierError(source) => Some(source),
        }
    }
}
#[allow(unused_qualifications)]
impl std::fmt::Display for EbpfError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use EbpfError::{
            AccessViolation, CallDepthExceeded, CallOutsideTextSegment, DivideByZero,
            DivideOverflow, ElfError, ExceededMaxInstructions, ExecutionOverrun,
            ExhaustedTextSegment, ExitRootCallFrame, FunctionAlreadyRegistered, InvalidInstruction,
            InvalidMemoryRegion, InvalidVirtualAddress, JitNotCompiled, LibcInvocationFailed,
            StackAccessViolation, SyscallError, UnsupportedInstruction, VerifierError,
        };
        match self {
            ElfError(e) => write!(f, "ELF error: {e}"),
            FunctionAlreadyRegistered(x) => {
                write!(f, "function #{x} was already registered")
            }
            CallDepthExceeded => write!(f, "exceeded max BPF to BPF call depth"),
            ExitRootCallFrame => write!(f, "attempted to exit root call frame"),
            DivideByZero => write!(f, "divide by zero at BPF instruction"),
            DivideOverflow => write!(f, "division overflow at BPF instruction"),
            ExecutionOverrun => write!(
                f,
                "attempted to execute past the end of the text segment at BPF instruction"
            ),
            CallOutsideTextSegment => {
                write!(f, "callx attempted to call outside of the text segment")
            }
            ExceededMaxInstructions => {
                write!(f, "exceeded CUs meter at BPF instruction")
            }
            JitNotCompiled => write!(f, "program has not been JIT-compiled"),
            InvalidVirtualAddress(address) => {
                write!(f, "invalid virtual address {address:x?}")
            }
            InvalidMemoryRegion(idx) => {
                write!(f, "Invalid memory region at index {idx}")
            }
            AccessViolation(_0, address, size, section) => write!(
                f,
                "Access violation in {section} section at address {address:#x} of size {size:?}"
            ),
            StackAccessViolation(_0, address, size, frame) => write!(
                f,
                "Access violation in stack frame {frame} at address {address:#x} of size {size:?}"
            ),
            InvalidInstruction => write!(f, "invalid BPF instruction"),
            UnsupportedInstruction => write!(f, "unsupported BPF instruction"),
            ExhaustedTextSegment(ix) => write!(
                f,
                "Compilation exhausted text segment at BPF instruction {ix}"
            ),
            LibcInvocationFailed(a, b, code) => {
                write!(f, "Libc calling {a} {b:?} returned error code {code}")
            }
            VerifierError(e) => write!(f, "Verifier error: {e}"),
            SyscallError(e) => write!(f, "Syscall error: {e}"),
        }
    }
}
impl From<ElfError> for EbpfError {
    #[allow(deprecated)]
    fn from(source: ElfError) -> Self {
        EbpfError::ElfError { 0: source }
    }
}
impl From<VerifierError> for EbpfError {
    #[allow(deprecated)]
    fn from(source: VerifierError) -> Self {
        EbpfError::VerifierError { 0: source }
    }
}

/// Same as `Result` but provides a stable memory layout
#[derive(Debug)]
#[repr(C, u64)]
pub enum StableResult<T, E> {
    /// Success
    Ok(T),
    /// Failure
    Err(E),
}

impl<T: std::fmt::Debug, E: std::fmt::Debug> StableResult<T, E> {
    /// `true` if `Ok`
    pub fn is_ok(&self) -> bool {
        match self {
            Self::Ok(_) => true,
            Self::Err(_) => false,
        }
    }

    /// `true` if `Err`
    pub fn is_err(&self) -> bool {
        match self {
            Self::Ok(_) => false,
            Self::Err(_) => true,
        }
    }

    /// Returns the inner value if `Ok`, panics otherwise
    pub fn unwrap(self) -> T {
        match self {
            Self::Ok(value) => value,
            Self::Err(error) => panic!("unwrap {:?}", error),
        }
    }

    /// Returns the inner error if `Err`, panics otherwise
    pub fn unwrap_err(self) -> E {
        match self {
            Self::Ok(value) => panic!("unwrap_err {:?}", value),
            Self::Err(error) => error,
        }
    }

    /// Maps ok values, leaving error values untouched
    pub fn map<U, O: FnOnce(T) -> U>(self, op: O) -> StableResult<U, E> {
        match self {
            Self::Ok(value) => StableResult::<U, E>::Ok(op(value)),
            Self::Err(error) => StableResult::<U, E>::Err(error),
        }
    }

    /// Maps error values, leaving ok values untouched
    pub fn map_err<F, O: FnOnce(E) -> F>(self, op: O) -> StableResult<T, F> {
        match self {
            Self::Ok(value) => StableResult::<T, F>::Ok(value),
            Self::Err(error) => StableResult::<T, F>::Err(op(error)),
        }
    }

    #[cfg_attr(
        any(
            not(feature = "jit"),
            target_os = "windows",
            not(target_arch = "x86_64")
        ),
        allow(dead_code)
    )]
    pub(crate) fn discriminant(&self) -> u64 {
        unsafe { *std::ptr::addr_of!(*self).cast::<u64>() }
    }
}

impl<T, E> From<StableResult<T, E>> for Result<T, E> {
    fn from(result: StableResult<T, E>) -> Self {
        match result {
            StableResult::Ok(value) => Ok(value),
            StableResult::Err(value) => Err(value),
        }
    }
}

impl<T, E> From<Result<T, E>> for StableResult<T, E> {
    fn from(result: Result<T, E>) -> Self {
        match result {
            Ok(value) => Self::Ok(value),
            Err(value) => Self::Err(value),
        }
    }
}

/// Return value of programs and syscalls
pub type ProgramResult = StableResult<u64, EbpfError>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_program_result_is_stable() {
        let ok = ProgramResult::Ok(42);
        assert_eq!(ok.discriminant(), 0);
        let err = ProgramResult::Err(EbpfError::JitNotCompiled);
        assert_eq!(err.discriminant(), 1);
    }
}
