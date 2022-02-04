;; there are 3 types of numbers, or rather ways of implementing / storing them, in ASM
;; traditionally we have worked with pure deenary (ie 1, 2, 1000, etc)
;; however disadvantages including having to convert each character to it's character equivalent (by adding 0x30 / 30h) and back again in order to print
;; there are two alternative forms of representation - storing directly as ASCII or using BCD (binary coded decimal) representation
;; ASCII representation involves doing arithmetic using characters, then issuing a command stating what arithmetic was done so the values can be adjusted. the commands following the pottern AA* (ASCII Adjust (after) *)
	;; AAA - ASCII adjust after addition
	;; AAS - ASCII adjust after subtraction
	;; AAM - ASCII adjust after multiplication
	;; AAD - ASCII adjust after division
	;; (note: these commands assume the ascii value is storded in register AL)

;; note: there's an issue when using 64-bit mode. make compatible notes
