# Make table (V-Table)を推計するためのプログラム

産業別商品別商品算出表([https://www.soumu.go.jp/toukei_toukatsu/data/io/index.htm](url) )
を経済センサス個票データから推計するためのプログラムです.

言語はHaskellで記述されています.

下記,経済センサスデータをData/Recordに入れることで推計が可能です.
なお,個人的な制作物であり,公式の推計手法とは異なります.
詳細は,論文を参考にしてください.


# 経済センサスデータ
> •   平成24年経済センサス-活動調査
> 【02～05,12】単独事業所調査票（鉱業,採掘業,砂利採取業・製造業・卸売業,小売業,産業共通）,【13】企業調査票及び【17～19】事業所調査票（鉱業,採掘業,砂利採取業・製造業・卸売業,小売業）

> •   平成28年経済センサス-活動調査
>【01】個人経営調査票,【03～05】単独事業所調査票（鉱業,採掘業,砂利採取業・製造業・卸売業,小売業）,【11】産業共通調査票,【12】企業調査票及び【16～18】事業所調査票（鉱業,採掘業,砂利採取業・製造業・卸売業,小売業）

(本リポジトリにはデータは含まれていません. データの構成などが公開できないため, このプログラムだけでは推計はできません. 推計を行いたい場合は,製作者にご連絡ください.)

# プログラム概要
------------------------------------------------------------------
src フォルダ以降に具体的な推計手続きがあります.

## 構成

	src
	└ VTable
    	├ Compliation
    	│ 		└ Conversion.hs
    	├ Compliation.hs
    	└ Data
        		├ Classification.hs
        		└ Structure.hs

各プログラムにはHTML形式の簡単なDocument (Haddock)があります.
[haddock/index.html](https://htmlpreview.github.io/?https://raw.githubusercontent.com/yakagika/sna_make_table/master/haddock/index.html) から閲覧してください.


### src/VTable/Compilation.hs
    実際の推計に関わるプログラム
    これを実行することで,V表が推計される

### src/VTable/Compilation/Conversion.hs
    申請によって得られた経済センサスデータを共通の形式に変換するプログラム

### src/VTable/Data/Structure.hs
    データ構造を定義

### src/VTable/Data/Classification.hs
    元データをデータ型に変換する際に使用するシソーラス

# 研究利用に関して 
各種研究などで,このプログラムを利用したい場合は,ご連絡ください.

また,推計手法に関して,疑問点,改善点などある場合には,是非ご教示ください.
issue等での議論や指摘もぜひご活用ください.



