(defun czt-java-mode-hook ()
  ;; set indentation to 2
  (setq c-basic-offset 2)
  ;; do not indent braces
  (c-set-offset 'substatement-open 0)
  ;; make sure spaces are used instead of tabs
  indent-tabs-mode nil)
(add-hook 'java-mode-hook 'czt-java-mode-hook)
