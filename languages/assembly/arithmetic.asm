;; assembly language supports mathematical operations (d'uh)
;; like moving data, you can also add and subtract to and using data from registers and main memory
;; when it comes to stuff like incrementing and decrementing, you must specify the size of the variable (ie  byte, word, dword)
;; multiplication and division are a little strange...
;; see https://www.tutorialspoint.com/assembly_programming/assembly_arithmetic_instructions.htm for full list & usage

section .data
	number db 1 ;; define a byte, initialise to 1
	small db 1
	bigger dw 12
	biggest dd 1222 ;; define double word
	end db 0x0 ;; define byte as end bit

section .bss
	result resb 2 ;; reserve 2 bytes
	bigger_res resw 2
	biggest_res resd 2 ;; reserve double word
	
section .text
	global _start
	
_start:
	;; init
	;; -----------------------------------------
		mov eax, 5
		

	;; increment... (for variables, specify word size -t needs to know how long it is to access that last byte)
	;; -----------------------------------------
		inc eax ;; increment (value in) register
		inc byte [number] ;; increment value at position held by number
	

	;; anddd decrement... (for variables, specify word size)
	;; -----------------------------------------
		dec eax ;; increment (value in) register
		dec byte [number] ;; increment value at position held by number


	;; adding
	;; -----------------------------------------	
		add eax, 2
		add eax, [number]
		add [number], eax ;; remember, can't use raw values on variables!
	
	
	;; subtracting
	;; -----------------------------------------
		sub [number], eax
		sub eax, [number] 
			
	
	;; multipliying - there are two instructions - MUL & IMUL (integer multiply - when using signed numbers (ie negative))
	;; -----------------------------------------
	;; to get results, you need to extract high and low bits from two seperate locations
	;; 3 differemt scemarios
	
		;; i - if you're multiplying byte * byte...
			mov al, 1 ;; place multiplicand (thing to be multiplied) in AL register
			mov eax, 2
			mul eax ;; multiply by another byte. 
			;; result is 2 bytes long - high order from AH, low order from AL
			mov [result], ah ;; add high order bit...
			add byte [result], ah ;; adding twice is equivalent of a bit-shift for high-order byte
			add byte [result], al ;; then add low bit once

	
		;; ii - if you're multiplying word * <=word
			mov ax, [bigger] ;; place multiplicand in AX register
			mul word [result] ;; multiply by another word
			;; result is 2 words long (doubleword) - high order from DX, low order from AX
			mov [bigger_res], dx ;; add high order bit...
			add word [bigger_res], dx ;; adding twice is equivalent of a bit-shift for high-order byte
			add word [bigger_res], ax ;; then add low bits once


		;; iii - if you're multiplying doubleword * <=doubleword
			mov ax, [biggest] ;; place multiplicand in AX register
			mul dword [bigger_res] ;; multiply by another word
			;; result is 2 doublewords long (doubleword) - high order from EDX, low order from EAX
			mov [biggest_res], edx ;; add high order bit...
			add dword [biggest_res], edx ;; adding twice is equivalent of a bit-shift for high-order byte
			add dword [biggest_res], eax ;; then add low bits once


	;; division - there are two instructions - DIV & IDIV (integer divide - when using signed numbers (ie negative))
	;; -----------------------------------------
	;; to get results, you need to extract quotient (amount of possible divides) and remainder	
	
		;; i - if you're dividing a number by a byte (1 byte)
			mov ax, 2 ;; value to be divided is placed in ax
			mov byte [number], 2
			div byte [number] ;; divide 2 in ax by byte w value of 2
			;; quotient in AL as a byte, remainder in AH as a byte
			
	
		;; ii - if you're dividing a number by a word (2 bytes)
			;; it assumes you're dividing a doubleword (4 bytes) and provides the space for it, 2 bytes in each register
			;; therefore if we want to divide 22...
			mov dx, 0 ;; place two high order bytes into DX
			mov ax, 22 ;; place two low order bytes into AX
			mov word [bigger], 10
			div word [bigger] ;; divide 0022 in dx,ax by word w value of 10		
			;; quotient in AX as a word (2 bytes), remainder in DX as a word (2 bytes)

	
		;; iii - if you're dividing a number by a doubleword (4 bytes)
			;; it assumes you're dividing a quadword (8 bytes) and provides the space for it, 4 bytes in each register
			;; therefore if we want to divide 2020...
			mov edx, 0 ;; place high order bit into EDX
			mov eax, 2020 ;; place low order bit into EAX
			mov dword [biggest], 1010
			div dword [biggest] ;; divide number in edx,eax by word w value of 1010	
			;; quotient in EAX as a doubleword (4 bytes), remainder in EDX as a doubleword (4 bytes)

			mov [biggest], eax
			mov ecx, biggest
			mov edx, 4
			call _print_number
			
	;; exit	
	mov eax, 1
	mov ebx, 0
	int 0x80	
	
;; this is a goto which acts as a function (at least when you command it by call instruction)
;; more on that later
_print_number:
	mov eax, 4
	mov ebx, 1
	add dword [ecx], 0x30
	int 0x80
	sub dword [ecx], 0x30
	ret
