; autoclicker.asm
; NASM-based autoclicker with Sleep for controlled clicking speed

global _start              ; Entry point
extern _mouse_event@20     ; Windows API: mouse_event
extern _Sleep@4            ; Windows API: Sleep function

section .data
    click_delay dd 1000     ; Delay in milliseconds (1000 ms = 1 second)

section .text

_start:
main_loop:
    ; Press left mouse button (MOUSEEVENTF_LEFTDOWN = 0x0002)
    push 0                ; dwExtraInfo
    push 0                ; dwData
    push 0                ; dy
    push 0                ; dx
    push 2                ; MOUSEEVENTF_LEFTDOWN
    call _mouse_event@20

    ; Release left mouse button (MOUSEEVENTF_LEFTUP = 0x0004)
    push 0                ; dwExtraInfo
    push 0                ; dwData
    push 0                ; dy
    push 0                ; dx
    push 4                ; MOUSEEVENTF_LEFTUP
    call _mouse_event@20

    ; Delay (Sleep for 'click_delay' milliseconds)
    push dword [click_delay]
    call _Sleep@4

    jmp main_loop       ; Infinite loop for continuous clicking
