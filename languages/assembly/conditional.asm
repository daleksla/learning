;; two types of 'conditional' jumps
;; unconditional jumps - uses JMP instruction
;; conditional jumps - jumps based on conditions
	;; The following conditional jump instructions operate by checking value stored in select register flags
	;; these register flags are set after logical / arithmetic operations have been conducted (eg AND bitwise, sub, inc, etc.)
	;; there are differing commands with regards to check numeric values (ie is equal, greater than, etc.) - some for signed and some for unsigned values. however commands relating purely to checking the flag registers are usuable regardless of the arithmetic mechanisms that filled them

;; Instruct. 	       Description 	             Flags checked
;; ---------------------------------------------------------------
;; JE          Jump Equal                           ZF
;; JNE         Jump not Equal (signed)              ZF
;; JNE         Jump not Equal (unsigned)            ZF
;; JNZ         Jump Not Zero (signed)               ZF
;; JNZ         Jump Not Zero (unsigned)             ZF
;; JG          Jump Greater (signed)                OF, SF, ZF
;; JA          Jump Above (unsigned)                CF, ZF
;; JNLE        Jump Not Less/Equal (signed)         OF, SF, ZF
;; JNBE        Jump Not Below/Equal (unsigned)      CF, ZF
;; JGE         Jump Greater/Equal (signed)          OF, SF
;; JAE         Jump Above/Equal (unsigned)          CF
;; JNL         Jump Not Less (signed)               OF, SF
;; JNB         Jump Not Below (unsigned)            CF
;; JL          Jump Less (signed)                   OF, SF
;; JB          Jump Below  (unsigned)               CF
;; JNGE        Jump Not Greater/Equal (signed)      OF, SF
;; JNAE        Jump Not Above/Equal (unsigned)      CF
;; JLE         Jump Less/Equal (signed)             OF, SF, ZF
;; JBE         Jump Below/Equal (unsigned)          AF, CF
;; JLE/JNG     Jump Not Greater (signed)            OF, SF, ZF
;; JNA         Jump Not Above (unsigned)            AF, CF
;; JZ          Jump Zero                            ZF
;; JC          Jump If Carry                        CF
;; JNC         Jump If No Carry                     CF
;; JO          Jump If Overflow                     OF
;; JNO         Jump If No Overflow                  OF 
;; JP          Jump Parity                          PF
;; JPE         Jump Parity Even                     PF
;; JNP/JPO     Jump No Parity                       PF
;; JPO         Jump Parity Odd                      PF
;; JS          Jump Sign (negative value)           SF
;; JNS         Jump No Sign (positive value)        SF

;; the way everyone else writes the commands is horrible, so hope this is more understandable

section .data
	ymsg db "YAY", 0x10
	len2 equ $-ymsg

	nmsg db "NAY", 0x10
	len1 equ $-nmsg

section .text
	global _start
	
_start:
	mov eax, 1
	cmp eax, 1
	je _yay_msg ;; if equal
	jmp _nay_msg ;; else

_exit:	
	mov eax, 1
	mov ebx, 0
	int 0x80
	
_nay_msg:	
	mov eax, 4
	mov ebx, 1
	mov ecx, nmsg
	mov edx, len1
	int 0x80
	jmp _exit
	
_yay_msg:	
	mov eax, 4
	mov ebx, 1
	mov ecx, ymsg
	mov edx, len2
	int 0x80
	jmp _exit
