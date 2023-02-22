mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
project_dir := $(dir $(mkfile_path))
build_dir :=$(project_dir)/_build
discussion_dir := $(project_dir)/discussion
md_files := $(shell find $(discussion_dir) -name '*.md')

vars :
	$(info $$var is [ ${md_files} ${mkfile_path} ${current_dir}])

pandoc:
	{ \
	 	for md in $(md_files) ; do \
 	 		pandoc -s  --embed-resources --standalone -c $(discussion_dir)/html/mail.css --lua-filter=$(discussion_dir)/html/tikz.lua  $$md -o $(subst discussion,discussion/html,$$md).html; \
 	 	done; \
 	}
