```hackage-download.py``` from https://github.com/nh2/hackage-download.

Run ```./analyzer.sh``` ```dir_with_Hackage_packages``` for counting extension. Results will be in *report.txt*. In case of error, check *counter.sh* (package="$(cut -d'/' -f2 <<<"${file}")").

Run ```./cov_percent.py``` ```full_list.txt``` ```report.txt``` to count percent Hackage, which can be parsed. In *report.txt* supported extensions should be marked '+'. 