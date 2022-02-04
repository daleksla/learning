;; barebones of every asm program
;; program consists of 'section .data/.bss/.text'
;; all other labels have colons afterwards

;; note: .data&.bss store are responsible for storing data
;; they store in RAM, not registers - the variable names are in-fact pointers
;; when to use which? well, use .data if you don't plan to change the values immediately once the program runs
;; use .bss if you do and just want memory as it allows for improved run-time speed & store space as all it does it allocate space, not store and copy over preliminary values

section .data ;; stores intiailised rw data
	;; here you put a variable name with a max amount of bytes

section .bss ;; stores uninitialised rw data
	;; here you reserve an amount of memory in bytes

;; note: storing anything in the two above makes it a global variable! which are evil!!!

section .text ;; stores actual code
	global _start ;; this tells linker which label the programs' execution begins (you can call it main if you like)	

_start: ;; all user-chosen labels require colon after
	;; commands in asm follow format: [label]   mnemonic   [operands]
	
	;; all programs must call for exit use syscall - it will fail to compile to a correct format otherwise

	;; following two lines are for 32-bit mode
	;; mov eax, 1 ;; put system call number into register (sys_exit)
	;; int 0x80 ;; call interrupt again to be handled by kernel

	;; following two lines are for 64-bit mode
	mov rax, 60 ;; put system call number into register (sys_exit)
	syscall ;; call interrupt again to be handled by kernel
	
	;; for more info on sys-calls, see "sys.asm"
