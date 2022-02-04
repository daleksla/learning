;; program showing syscalls
;; if you're using 32-bit ASM, use int 0x80 as a kernel interrupt & syscalls of this link: http://faculty.nps.edu/cseagle/assembly/sys_call.html
;; if you're using 64-bit ASM, use syscall as a kernel interrupt & syscalls of this link: http://blog.rchapman.org/posts/Linux_System_Call_Table_for_x86_64/
;; main command is stored in eax & args are stored in rbx, rcx, rdx, esx, edi registers in 32-bit mode
;; main command is stored in rax & args are stored in rdi, rsi, rdx, r10, r8, r9 in 64-bit mode (in that order)
;; note: syscalls which return stuff typically store return value in EAX/RAX in 32-bit & 64-bit mode, respectively

section .text ;; stores actual code
	global _start ;; this tells linker which label the programs' execution begins	

_start:
	;; 32 bit version
	;; mov eax, 1 ;; in EAX -> sys_call id (1 = sys_exit)
	;; mov ebx, 0 ;; in EBX -> arg#1 (0 exit code)
	;; int 0x80 ;; call interrupt to be handled by kernel
	
	;; 64 bit version
	mov rax, 60 ;; 60 = x86 64bit syscall id for sys_exit
	mov rdi, 0
	syscall ;; call kernel interrupt
