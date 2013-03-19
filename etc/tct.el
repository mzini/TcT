;;; tct.el --- a simple interface to TCT (http://cl-informatik.uibk.ac.at)
;; 
;; To integrate this mode into emacs, put (require 'tct)
;; into your emacs config, which usually resides in ~/.emacs. 
;;
;; The mode should be pretty self-explanatory, in particular the 
;; complete functionality is reflected in the menu-bar. 
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; This file is not yet part of GNU Emacs.
;;
;; This module is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 2, or (at your
;; option) any later version.
;;
;; This module is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'inf-haskell)
(require 'dired)

(defgroup tct nil
  "Special support for the Tyrolean Complexity Tool."
  :group 'tools
  :prefix "tct-")


(defcustom tct-executable "tct"
  "Path to TcT executable file"
  :type 'string
  :group 'tct)

(defcustom tct-base "~/.tct"
  "The TcT configuration directory."
  :type 'string
  :group 'tct)

(defcustom tct.hs (concatenate 'string tct-base "/tct.hs")
  "The path to TcT configuration file"
  :type 'string
  :group 'tct)

(defcustom tct-home-folder tct-base
  "The path that is used as home folder"
  :type 'string
  :group 'tct)

(defcustom xtc2tpdb-xsl "http://termcomp.uibk.ac.at/status/xtc2tpdb.xsl"
  "The path to xtc2tpdb"
  :type 'string
  :group 'tct)


(defvar tct-state-file "~/.tct/state.org")
(defvar tct-proof-file "~/.tct/proof.org")
(defvar tct-answer-type "rc")
(defvar input-system nil)
(defvar tct-strategy nil)



(defvar tct-output-buffer-name "TcT-output")
(defvar tcti-buffer-name "TcT-interactive")



;; ----------------------------------------------------------------------
;;menus

(defvar tct-doc-menu
  '("Documentation"
    ["Interactive Mode"        tct-documentation-interactive t]
    ["Processor Overview"      tct-documentation-processors t]
    ["Processor Instances"     tct-documentation-instances t]
    ["Configuration"           tct-documentation-configuration t]
    ["Library"                 tct-documentation t]
    ["Rewriting Library"       tct-documentation-rewriting t]))

(defvar tct-measure-menu
  '("Set Complexity Measure"
    ["Runtime Complexity"                  tct-set-rc           t]
    ["Runtime Complexity Innermost"        tct-set-rci          t]
    ["Derivational Complexity"             tct-set-dc           t]
    ["Derivational Complexity Innermost"   tct-set-dci          t]))


;; ----------------------------------------------------------------------
;; tct dired

;;;###autoload
;; (define-derived-mode tct-dired-mode dired-mode "TcT"
;;   "Tct mode.
;; \\<tct-dired-mode-map>"
;;   :group 'tct
;;     (make-local-variable 'tct-rc)
;;     (setq input-system nil)
;;     (setq input-strategy nil)
;;     (setq tct-answer-type "rc"))

;; (add-to-list 'auto-mode-alist '("\\.strat$" . tct-dired-mode))


(defvar tct-dired-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [return] 'tct-dired-find-file)
    (define-key map [mouse-1] 'tct-dired-find-file)
    (define-key map [mouse-2] 'tct-dired-find-file)
    (define-key map "x"        'tct-dired-on-file)
    (define-key map "l" 'tct-dired-load-interactive)
    (define-key map "s" 'tct-dired-show-trs)
    (define-key map "q" 'tct-dired-quit)
    (define-key map "\C-c\C-i" 'tct-interactive)
    map))

(easy-menu-define tct-dired-mode-menu tct-dired-mode-map 
  "Menu used in `tct-dired-mode'."
  `("TCT dired"
    ,tct-measure-menu
    ["Run TcT"                       tct-dired-on-file t]
    ["Load file in interactive mode" tct-dired-load-interactive t]
    ["Open tct.hs"                   tct-open-hs       t]
    ["Show TRS"                      tct-dired-show-trs      t]
    ["Quit"                          tct-dired-quit    t]))

;;;###autoload
(define-minor-mode tct-dired-mode
  "Add tct capabilities to dired"
  :initial-value nil
  :lighter " TcT"
  :keymap tct-dired-mode-map
  :group 'tct
  (make-local-variable 'tct-rc)
  (setq input-system nil)
  (setq input-strategy nil)
  (setq tct-answer-type "rc"))

(defvar tct-dired-buffer nil)

(defun enable-tct-dired-mode (buffer)
  (with-current-buffer buffer
    (setq tct-dired-buffer buffer)
    (tct-dired-mode 1)
    (menu-bar-mode 1)
    (rename-buffer "*TcT-dired*")))
    
(defun tct-dired ()
  (interactive)
  (if (and tct-dired-buffer (buffer-live-p tct-dired-buffer))
      (switch-to-buffer-other-window tct-dired-buffer)
    (progn 
      (if tct-dired-buffer (kill-buffer tct-dired-buffer))
	(if (file-exists-p tct-home-folder)
	    (enable-tct-dired-mode (dired tct-home-folder))
	  (message (concat "Directory " 
			   tct-home-folder 
			   " does not exist. Please configure variable tct-home-folder from the tct configuration group"))))))


(defun tct-dired-find-file ()
  (interactive)
  (if (file-directory-p (dired-get-file-for-visit))
      (progn 
	(dired-find-alternate-file)
	(enable-tct-dired-mode (current-buffer)))
    (dired-find-file)))


(defun tct-dired-quit ()
  (interactive)
  (if tct-dired-buffer 
      (progn 
	(kill-buffer tct-dired-buffer)
	(setq tct-dired-buffer nil)
	(message "TcT stopped."))))


(defun tct-dired-on-file (strat)
  (interactive "sStrategy: ")
  (call-tct strat (dired-get-file-for-visit)))


(defun tct-dired-show-trs ()
  (interactive)
  (let ((file (dired-get-file-for-visit)))
    (if (equal (file-name-extension file) "xml")
	(shell-command (concat 
			"xsltproc --maxdepth 1024 --maxparserdepth 1024 " 
			xtc2tpdb-xsl
			" " 
			file))
        (shell-command (concat "cat " file)))))


(defun call-tct (strat system)
  (setq input-system (expand-file-name system))
  (setq tct-strategy strat)
  (let ((output-buffer (get-buffer tct-output-buffer-name))
	(strategyarg (if (equal strat "") 
			 "" 
		       (concat "-s \"" strat "\""))))
    (if output-buffer (kill-buffer output-buffer))
    (start-process-shell-command tct-executable 
				 tct-output-buffer-name 
				 (concat 
				  tct-executable
				  strategyarg
				  "-a" tct-answer-type
				  input-system))
    (save-excursion
      (set-buffer (get-buffer tct-output-buffer-name))
      (org-mode)
      (toggle-read-only t)
      (goto-char 0))
    (switch-to-buffer-other-window tct-output-buffer-name)))


;; ----------------------------------------------------------------------
;; tct inferior mode

(defvar tcti-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-ch" 'tcti-symbols)
    (define-key map "\C-cs" 'tct-state-buffer)
    (define-key map "\C-cp" 'tct-proof-buffer)
    (define-key map "\C-crr" 'tcti-reload)
    (define-key map "\C-cq" 'tcti-quit)
    map))


(easy-menu-define tcti-mode-menu tcti-mode-map 
  "Menu used in `tcti-mode'."
  `("TcT interactive"
    ,tct-measure-menu
    ,tct-doc-menu
    ["Show State "                tct-state-buffer  t]
    ["Show Proof "                tct-proof-buffer  t]
    ["Show Symbols"               tcti-symbols      t]
    ["Reset Session"              tcti-reset       t]
    ["Open tct.hs"                tct-open-hs       t]
    ["Quit"                       tcti-quit         t]))

;;;###autoload
(define-minor-mode tcti-mode
  "Add tct capabilities to haskell inferior mode"

  :initial-value nil
  :lighter " TcT"
  :keymap tcti-mode-map
  :group 'tct)


(defvar tct-inferior-buffer nil
  "The buffer in which the inferior process is running.")

(defun tcti-start-process ()
  (setq tct-inferior-buffer
	(save-excursion
	  ;; (cd tct-base)
	  (make-comint tcti-buffer-name tct-executable nil "-i")))
  (with-current-buffer tct-inferior-buffer
    (inferior-haskell-mode)
    (tcti-mode 1)
    (run-hooks 'inferior-haskell-hook)))

(defun tcti-process ()
  (or (if (buffer-live-p tct-inferior-buffer)
	  (get-buffer-process tct-inferior-buffer))
      (progn
	(tcti-start-process)
	;; Try again.
	(tcti-process))))

(defun tcti-get-buffer ()
  (process-buffer (tcti-process)))
  
(defun tcti-pop-to-buffer ()
  (pop-to-buffer (tcti-get-buffer)))

(defun tct-interactive ()
  (interactive)
  (tcti-pop-to-buffer))

(defun tcti-quit ()
  (interactive)
  (let ((buffer (tcti-get-buffer)))
    (if buffer
	(with-current-buffer (tcti-get-buffer)
	  (kill-buffer-and-window)
	  (message "TcTi stopped")))))


(defun tcti-send (str)
  (interactive "p")
  (inferior-haskell-send-command (tcti-process) str))

(defun tcti-send-block ()
  (interactive)
 (let (p1 p2)
    (setq p1 (point))
    (backward-paragraph)
    (forward-line)
    (setq p2 (point))
    (goto-char p1)
    (tcti-send (buffer-substring p2 p1))))


(defun tcti-load-file (file) 
  (interactive "f")
  (let ((load (cond 
	       ((equal tct-answer-type "rc") "loadRC")
	       ((equal tct-answer-type "dc") "loadDC")
	       ((equal tct-answer-type "idc") "loadIDC")
	       ((equal tct-answer-type "irc") "loadIRC")
	       (t "load"))))
    (tcti-send (concat load " \"" (expand-file-name file) "\""))
    (tcti-pop-to-buffer)))

(defun tcti-symbols ()
  (interactive)
  (tcti-send ":browse")
  (tcti-send ":browse Tct.Instances")
  (tcti-send ":browse Tct.Processors"))

(defun tcti-reset ()
  (interactive)
  (tcti-send "reset"))

(defun tct-dired-load-interactive ()
  (interactive)
  (tcti-load-file (dired-get-file-for-visit)))

(defun tct-visit-org-output (file name)
  (if (and (file-exists-p file) (file-readable-p file))
      (progn
	(let ((buffer (find-file-noselect file)))
	    (with-current-buffer buffer
	      (rename-buffer (concat "*" name "*"))
	      (auto-revert-mode 1) 
	      (org-display-inline-images) 
	      (add-hook 'after-revert-hook 'org-display-inline-images) 
	      (setq auto-revert-interval 1)
	      (view-buffer-other-frame buffer))))
    (message "TcTi output not available")))


(defun tct-state-buffer ()
  (interactive)
  (tct-visit-org-output tct-state-file "state"))

(defun tct-proof-buffer ()
  (interactive)
  (tct-visit-org-output tct-proof-file "proof"))

      

;; ----------------------------------------------------------------------
;; common utility

(defun tct ()
  (interactive)
  (tct-dired)
  (tct-interactive))

(defun tct-quit ()
  (interactive)
  (tct-dired-quit)
  (tcti-quit))

(defun tct-open-hs ()
  (interactive)
  (find-file tct.hs))

(defun tct-set-answertype (name set-cmd)
  (setq tct-answer-type name)
  (when (buffer-live-p tct-inferior-buffer)
    (tcti-send set-cmd)))

(defun tct-set-rc ()
  (interactive)
  (tct-set-answertype "rc" "setRC"))

(defun tct-set-rci ()
  (interactive)
  (tct-set-answertype "irc" "setIRC"))

(defun tct-set-dc ()
  (interactive)
  (tct-set-answertype "dc" "setDC"))

(defun tct-set-dci ()
  (interactive)
  (tct-set-answertype "idc" "setIDC"))

;; ----------------------------------------------------------------------
;; common utility


(defcustom tct-documentation-url "http://cl-informatik.uibk.ac.at/software/tct/projects/tct/docs"
  "Url where TcT documentation is located."
  :type 'string
  :group 'tct)

(defcustom tct-termlib-documentation-url "http://cl-informatik.uibk.ac.at/software/tct/projects/termlib/docs"
  "Url where Termlib documentation is located."
  :type 'string
  :group 'tct)


(defun tct-open-doc (url)
  (browse-url url))

(defun tct-documentation ()
  (interactive)
  (tct-open-doc (concat tct-documentation-url "/index.html")))

(defun tct-documentation-interactive ()
  (interactive)
  (tct-open-doc (concat tct-documentation-url "/Tct-Interactive.html")))

(defun tct-documentation-configuration ()
  (interactive)
  (tct-open-doc (concat tct-documentation-url "/Tct-Configuration.html")))

(defun tct-documentation-processors ()
  (interactive)
  (tct-open-doc (concat tct-documentation-url "/Tct-Processors.html")))

(defun tct-documentation-instances ()
  (interactive)
  (tct-open-doc (concat tct-documentation-url "/Tct-Instances.html")))

(defun tct-documentation-rewriting ()
  (interactive)
  (tct-open-doc (concat tct-termlib-documentation-rewriting "/Termlib-Repl.html")))

(provide 'tct)
;;; tct.el ends here
