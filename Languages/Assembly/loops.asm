;; there are two ways of implementing loops in asm - in a while loop or for loop-esque manner
;; both require the use of goto's - labels to jump from
;; for loops can be implemented using the LOOP instruction, where the counter is stored in the ECX, checked and automatically changed
;; while loops are implemented using if statements and manual decrementation

section .data
	count db 9
	
section .text
	global _start
	
_start:
	call _print ;; call print - original value is 9
	mov rcx, 5 ;; set counter for for_loop_one
	call for_loop_one ;; call loop func - uses loop instruction
	call _print ;; call print showing updated value - will show 4
	mov rcx, 2 ;; set counter for for_loop_one
	call for_loop_two ;; call loop func, uses jmp's and conditionals
	call _print ;; will show 2
	jmp _exit ;; finally, end program 

_exit:
	mov rax, 1
	mov rbx, 0
	int 0x80
	
_print:
	mov rax, 4
	mov rbx, 1
	add byte [count], 0x30
	mov rcx, count
	mov rdx, 2
	int 0x80
	sub byte [count], 0x30
	ret	
	
for_loop_one:
	dec byte [count]
	loop for_loop_one
	ret ;; after loop completes
	
for_loop_two:
	dec byte [count]
	loop for_loop_one
	dec rcx ;; manually decrement counter
	jnz for_loop_two ;; if decrement op didn't make rcx 0, jump to start of loop
	ret ;; else, return (after loop completes)
