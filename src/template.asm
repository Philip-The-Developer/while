;===============================================================================
; Macros and Defines
;===============================================================================

; Length of our input buffer
%define buffer_length 24

; The macro which reads from STDIN via SYSCALL
%macro  read 0
    mov QWORD [buffer.current], buffer
    mov rax, 0
    mov rdi, 0
    mov rsi, buffer
    mov rdx, buffer_length
    syscall
    mov QWORD [buffer.remaining], rax
%endmacro

; Increment our rsi register (=buffer.current) and decrent the remaining bytes
%macro inc_rsi 0
    ; Move forward in our buffer
    inc rsi
    dec QWORD [buffer.remaining]
%endmacro

; Debugging macro, outputs the current value of [rsi]
%macro debug_rsi 0
     ;push rax
     ;xor rax, rax
     ;mov al, BYTE [rsi]
     ;add rax, 100000000
     ;call output_number
     ;pop rax
%endmacro

; Debugging macro, outputs the current value of [rsi]
%macro debug_rbp 0
     mov [macro_save], rax
     xor rax, rax
     mov rax, rbp
     call output_number
     mov rax, [macro_save]
%endmacro

%macro method_call 3
  multipush r8, r9, r10, r11  
  ;get the class
  mov r8, [%2] ; (r8) = class
  add r8, r8, 24
  mov r9, [r8] ; (r9) = function ideces
  add r11, %3, 16 ; (r11) = %3+16
  mov r10, [r11] ; (r10) = index
  imul r10, 8
  add r10, r10, 8
  add r11, r9, r10
  cmp %3 , [r11]
  jne alloc_error ; TODO change error prompt
  add r8, r8, 32
  mov r9, [r8] ; (r9) = function offsets
  add r11, r9, r10
  mov r8, [r11] ; (r8) = function address
  call r8
  pop rax ; (rax) = return value
  multipop r8,r9,r10, r11
  mov %1, rax
%endmacro

%macro debug_rsp 0
     mov [macro_save], rax
     xor rax, rax
     mov rax, rsp
     call output_number
     mov rax, [macro_save]
%endmacro

; Macros to push and pop multiple registers on the stack
; You don't have to reverse the argument order for pop
; Taken from: http://www.nasm.us/doc/nasmdoc4.html
%macro multipush 1-*
    %rep %0
        push %1
        %rotate 1
    %endrep
%endmacro
%macro multipop 1-*
    %rep %0
        %rotate -1
        pop %1
    %endrep
%endmacro
; $ Added macros for double-precision floating-point cases 
%macro multifpush 1-*
    %rep %0
        movq rax, %1
        push rax
        %rotate 1
    %endrep
%endmacro
%macro multifpop 1-*
    %rep %0
        %rotate -1
        pop rdx
        movq %1, rdx
    %endrep
%endmacro

;===============================================================================
; Generated initialized Data
;===============================================================================
section .data

;{-# GENERATED #-}

;===============================================================================
; The code
;===============================================================================
section .text

;import from OS
extern malloc
extern free

;import from Environment
extern sign_mask
extern alloc_error
extern alloc_error2
extern index_error
extern return_error
extern input_number
extern output_number
extern input_float
extern output_float
extern input_character
extern output_character
extern buffer.remaining
extern buffer.current
extern buffer
extern env_class_class
extern env_label_class
extern label_env_parent
extern type_int
extern type_double
extern type_char
extern type_ref  
extern type_array_int
extern type_array_double
extern type_array_char
extern type_array_ref
extern exit_program
extern label_env_new

global main_code
main_code:
;+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
; MAIN CODE STARTS HERE
;+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;{-# MAIN CODE #-}
;+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
; MAIN CODE ENDS HERE
;+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
jmp exit_program

;===============================================================================
; $ User-defined functions.
;===============================================================================
