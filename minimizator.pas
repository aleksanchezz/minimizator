unit minimizator;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, ToolWin, ComCtrls, Menus, ImgList, StdCtrls, ExtCtrls, Grids;

type
  TForm1 = class(TForm)
    MainMenu1: TMainMenu;
    ToolBar1: TToolBar;
    File1: TMenuItem;
    He1: TMenuItem;
    ToolButton1: TToolButton;
    ToolButton2: TToolButton;
    ToolButton3: TToolButton;
    ToolButton4: TToolButton;
    ToolButton5: TToolButton;
    ToolButton6: TToolButton;
    ImageList48: TImageList;  
    ToolBar2: TToolBar;
    Label1: TLabel;
    Edit1: TEdit;
    ToolButton12: TToolButton;
    ToolButton7: TToolButton;
    Image1: TImage;
    Image2: TImage;
    ToolButton8: TToolButton;
    N1: TMenuItem;
    N2: TMenuItem;
    N3: TMenuItem;
    N4: TMenuItem;
    ImageList1: TImageList;
    OpenDialog1: TOpenDialog;
    N5: TMenuItem;
    N6: TMenuItem;
    ScrollBox1: TScrollBox;
    StringGrid1: TStringGrid;
    StringGrid2: TStringGrid;
    StringGrid3: TStringGrid;
    SaveDialog1: TSaveDialog;
    ToolBar3: TToolBar;
    Label2: TLabel;
    Label5: TLabel;
    SaveDialog2: TSaveDialog;
    Label4: TLabel;
    Label6: TLabel;
    Label7: TLabel;
    Label8: TLabel;
    Label9: TLabel;
    Label10: TLabel;
    procedure FormCreate(Sender: TObject);
    procedure ToolButton4Click(Sender: TObject);
    procedure ToolButton1Click(Sender: TObject);
    procedure ToolButton2Click(Sender: TObject);
    procedure ToolButton3Click(Sender: TObject);
    procedure ToolButton6Click(Sender: TObject);
    procedure N1Click(Sender: TObject);
    procedure N6Click(Sender: TObject);
    procedure wheelmove(Sender: TObject; Shift: TShiftState;//прокрутка scrollbox колесом мышки
      WheelDelta: Integer; MousePos: TPoint; var Handled: Boolean);
    procedure setscrfocus(Sender: TObject);
    procedure StringGrid2DrawCel(Sender: TObject; ACol, ARow: Integer;
      Rect: TRect; State: TGridDrawState);
    procedure ResizeForm1(Sender: TObject);
    procedure N2Click(Sender: TObject);
    procedure N4Click(Sender: TObject);
    procedure N3Click(Sender: TObject);// установка фокуса на компонент

  private
    { Private declarations }
  public
    { Public declarations }
  end;

  const
symbols=['a'..'z','A'..'Z','0'..'9'];
operation_symbols=['(',')','+','*','!'];
true_operation_symbols=['+','!','*'];
barheight=104;
zazor=8;
labelh=20;
type
a=array [1..100] of char;
b=array [1..100] of integer;
Number=record
operand:char;
operator:integer;
end;

Table=record
term:string;
func:string;
kol_vo_1:longint;
nomer_stroki:string;
skleen:boolean;
end;

otv=record
stroka:string;
kol_vo_implicant:integer;
end;



Tablica=Array [0..10,1..3000] of Table;
Tablica_implicant=array[1..3000] of table;

Matrica=array [1..31,1..31] of string;

Nomer_implican=array[1..31] of integer;

var

Form1: TForm1;
translate,minimize,truthtable,clearation:boolean;
strgrid: array [1..10] of Tstringgrid;
f:textfile;
f1:textfile;
f2:textfile;
fname,filename,filestring:string;
M:Matrica;
N_i:Nomer_implican;
Numbers:Array [1..10] of number;
otvet:array [1..10] of otv;
Tables:Tablica;
Implicant_matrix:Tablica_implicant;
Implicant_matrix_1:Tablica_implicant;
Implicant_matrix_mid:Tablica_implicant;
input_string,q:string;
output_string:string;
term_output:string;
string_pointer,N:word;
symbol:char;
stack:a;
stack_int:b;
stack_pointer,kount,chislo:word;
stack_empty:boolean;
i,y,h,x,g,prioritet,resalt,stepen,w,l,count_opn:integer;
hight,hight_1, Implicant_matrix_hight:longint;
kol_vo_nach_term,nomer,final_kol_vo_term,vyzov_sckl:integer;
implicant_mask,Otvet_mask:longint;
ALL0,ALL1:boolean;
dlabel:array [1..10] of TLabel;
nomer_clear:integer;
  implementation

uses Unit2;

{$R *.dfm}
Procedure get_symbol(var stroka:string);// переписывает в переменную symbol значение элемента входной строки
// если он не ноль и не табуляция по окончанию входной строки в symbol записывается код 0
begin
 while (string_pointer<=length(stroka))and(stroka[string_pointer] in [#32,#9]) do
   inc(string_pointer);// пропустить пробелы и табуляции
 if string_pointer>length(stroka) then symbol:=#0 // записать в symbol признак конца строки
   else
    begin
     symbol:=stroka[string_pointer];inc(string_pointer);
    end;
end;//of get_symbol
//__________________________________________________________________________________________
Procedure push(var symbol:char); //записывает символ в стэк
var i:integer;
begin
 stack[stack_pointer]:=symbol;
 if stack_pointer<100 then inc(stack_pointer);
 stack_empty:=false;
end;//of push
//___________________________________________________________________________________________
Procedure pop(var symbol:char); // выталкивает символ из стэка
var i:integer;
begin
if stack_pointer>1 then dec(stack_pointer);
 symbol:=stack[stack_pointer];
 if stack_pointer=1 then stack_empty:=true;
end;//of pop
//______________________________________________________________________________________
Procedure push_int(var symbol:integer); //записывает символ в стэк
var i:integer;
begin
 stack_int[stack_pointer]:=symbol;
 if stack_pointer<100 then inc(stack_pointer);
 stack_empty:=false;
end;//of push
//______________________________________________________________________________________
Procedure pop_int(var symbol:integer); // выталкивает символ из стэка
var i:integer;
begin
if stack_pointer>=1 then dec(stack_pointer);
 symbol:=stack_int[stack_pointer];
 if stack_pointer=1 then stack_empty:=true;

end;//if pop
//____________________________________________________________________________
function priority(symbol:char):integer;// приписывает приоритет операции в ссответсвии
// с алгоритмом Дейстры
begin
case symbol of
'(':prioritet:=0;
')':prioritet:=1;
'+':prioritet:=2;
'*':prioritet:=3;
'!':prioritet:=4;
end;//of case
priority:=prioritet;
end;// of priority

//___________________________________________________________________________________________________
   procedure MsgBox(Capt,Msg:string);
   begin
    MessageBox(0,PChar(msg),PChar(capt),0);
   end;

//__________________________________________________________________-
procedure search_string_error(input_string:string;var error:word);
var
i,j:word;
symbol_s:char;
skobkaR,skobkaL:word;
output_string:string;
error_string:string;

name:boolean;
var_name:array [1..10] of char;
point_var_name:word;
 begin
 error:=0;
 output_string:='';
 string_pointer:=1;
 skobkaR:=0;
 skobkaL:=0;
 point_var_name:=1;
 for j:=1 to 10 do var_name[j]:=' ';

  Repeat
   get_symbol(input_string);
   if ((symbol<>#32) or  (symbol<>#9)) then
   output_string:=output_string+symbol;
  until symbol=#0;//выбросили из входной строки пробелы и табуляции


   string_pointer:=1;
   if ((output_string[string_pointer] = '+') or (output_string[string_pointer] = '*')) then
    begin// функция не может начинаться зо знака операции
     error:= error or 1;// выставляем первый бит
     error_string:='формула не может начинаться со знака операции + или *';
    end;

  repeat// основной цикл поиска ошибок
   symbol_s:=output_string[string_pointer];

   if symbol_s in symbols then // проверка на кол-во переменных
    begin
     if point_var_name=1 then
     begin
      var_name[1]:=symbol_s;
      inc(point_var_name);
     end
     else
      begin
       name:=true;
        for j:=1 to point_var_name-1 do
         begin
          if var_name[j]=symbol_s then name:=false;
         end;
        if name then
         begin
          var_name[j]:=symbol_s;
          inc(point_var_name);
         end;
      end;
     end;// if symbol_s in symbols

   if symbol_s='(' then inc(skobkaL); //считаем открывающие скобки
   if symbol_s=')' then inc(skobkaR); // считаем закрывающие скобки

   if symbol_s in symbols then // проверка на длину переменной в символах
    begin
     if string_pointer<length(output_string) then // строка не кончилась?
      begin
       if output_string[string_pointer+1] in symbols then // если следующий символ буква
        begin
         error:= error or 2;// выставляем второй бит
         error_string:='Имя переменной не может содержать более одного символа';
        end;
      end;
    end;// if symbol_s in symbols

    if symbol_s in ['+','*'] then // проверка на два знака операции подряд
    begin
     if string_pointer<length(output_string) then // строка не кончилась?
      begin
       if output_string[string_pointer+1] in  ['+','*'] then // если второй символ операции + или -
        begin
         error:= error or 4;// выставляем третий бит
        error_string:='Cимволы операции не могут следовать друг за другом';
        end;
      end;
    end;// if symbol_s in symbols

    if symbol_s='!' then // проверка на два знака ! подряд
    begin        
     if string_pointer<length(output_string) then // строка не кончилась?
      begin
       if output_string[string_pointer+1]='!' then // если второй символ операции !
        begin
         error:= error or 8;// выставляем 4 бит
         error_string:='Два символа отрицания не могут следовать друг за другом';
        end;
      end;
    end;// if symbol_s in symbols


    if symbol_s  in (operation_symbols+symbols+[#0]) then   // проверка на недопустимый символ
    else
    begin
      error:= error or 16;// выставляем 5 бит
    error_string:='В формуле применен недопустимый символ';
    end;// if symbol_s in symbols

   inc( string_pointer);
  until symbol_s=#0;
 if skobkaL<>skobkaR then // проверка равного кол-ва скобок ( и )
   begin
    error:= error or 32;//выставляем 6 бит
    error_string:='Кол-во открывающих и закрывающих скобок не равно';
 end;

  if point_var_name-1>5 then
    begin
     error:= error or 64;//выставляем 7 бит
     error_string:='Максимальное кол-во переменных равно 5';
    end;

  If point_var_name=1 then
    begin
     error:= error or 128;//выставляем 8 бит
     error_string:='Нет функции для минимизации';
    end;

 //________________________________________________________________________
 //Биты ошибок в переменной Error
//1 формула начинается со знака операции + или *
//2 размер переменной больше двух символов
//4 два символа операции следуют друг за другом
//8 два символа операции !! следуют друг за другом
//16 недопустимый символ
//32 неравное кол-во открывающих и закрывающих скобок
//64 превышено кол-во переменных
//128 Нет функции для минимизации
//_________________________________________________________________________
if Error<>0 then
 begin
  //MsgBox('Ошибка во входной строке',error_string);
   MessageDlg('Ошибка в формуле. - '+error_string,mtError,[mbOK],0);
 end;
end;// search_string_error
 //________________________________________________________________________________________________________
procedure OPN;// Переводит выражение зап. в входной строке в обратную польскую нотацию
// в соответсвии с алгоритмом Дейкстры
 var symbol1:char;
j,z:integer;
error:word;
begin
//search_string_error(input_string,error);
string_pointer:=1;
kount:=1;
//If error=0 then // старт перевода в опн при отсутсвии синтаксических ошибок
//begin
Repeat
  j:=0;
  get_symbol(input_string); // берем символ из входной строки
  {writeln('symbol = ', symbol);}
  if symbol in symbols then
  begin
  output_string:= output_string+symbol; //все символы входной строки ссответсвующие переменным переписываются в выходную строку

 for z:=1 to kount do
  begin
  if
  numbers[z].operand=symbol then
  inc(j);
  end;
  if j=0 then begin
  numbers[kount].operand:=symbol;           //Запись переменных в отдельный массив record
  inc(kount);
  end;
    if stack_empty=false then // обработка унарного оператора !
   begin
    if (stack[stack_pointer-1]='!') then
     begin
      pop(symbol); output_string:= output_string+symbol;
     end;
   end;
  end
   else // обработка символов операций
    if symbol in operation_symbols then // обработка символов +-*/()
     begin
      if stack_empty then push(symbol)// если стэк пуст, то операция переписывается в стэк
       else // если стэк не пуст
        begin
         if (symbol in true_operation_symbols) then//если symbol + - * /
          begin
           if priority(symbol) > priority(stack[stack_pointer-1]) then
               push(symbol) // если приоритет входного символа больше чем приоритет
                            // символа вершины стэка то он записывается в стэк
             else
              begin
               repeat
                pop(symbol1);
                output_string:= output_string+symbol1;
               until  (priority(symbol) >= priority(stack[stack_pointer-1]))
                  or (stack[stack_pointer-1]='(')
                   or (stack[stack_pointer-1]=')');
               push(symbol); // при меньшем приоритете символы из стэка выталкиваются в выходную строку
               //до тех пор пока приоритет входно символа будет больше или равен приоритету
               //символа вершины стэка, затем символ записывается в стэк
              end;
            end; // priority(symbol)<priority(stack(stack_pointer-1)
         if symbol=')' then // если symbol закр скобка то из стэка в выходную строку
         //переписываются все символы операций кроме скобок до отккрывающей скобки
          begin
           repeat
            pop(symbol1);
             if ( (symbol1<>')') and (symbol1<>'(') )
              then output_string:= output_string+symbol1;
           until symbol1='(';
            if stack_empty=false then // обработка унарного оператора !
              begin
               if (stack[stack_pointer-1]='!') then
                begin
                 pop(symbol); output_string:= output_string+symbol;
                end;
              end;
          end;
         if symbol='(' then push(symbol);//если символ открыв. скобка то она записывается в стэк

        end// else of if stack_empty then
      
     end;// if symbol in operation_symbols
until symbol=#0;
 while stack_empty=false do // по окончанию входной строки символы из стэка выводяться в выходную
  // строку
  begin
   pop(symbol1); output_string:= output_string+symbol1;
  end;// of stack_empty=false
  dec(kount);
// end// проверка синтаксической ошибки
 end;//of OPN
//_____________________________________________________________________________
Procedure count_OPZ;// рассчет значения функции
var res,sym,sym_1,b,w:integer;
begin
w:=10;
string_pointer:=1;// переменная цикла для входной строки
stack_pointer:=1; // указатель стэка
stack_empty:=true;// стэк пуст
Repeat
get_symbol(output_string);
 if symbol in symbols then
  begin
   for b:=1 to kount  do
    begin
     if numbers[b].operand=symbol then
     res:=numbers[b].operator;
    end;//of for
    push_int(res);
   end// if symbol in symbols
 else
 begin
 if symbol='!' then
 begin
 pop_int(sym);
 res:=(not sym)and 1;
 push_int(res);
 end
 else
 begin
 pop_int(sym);
 pop_int(sym_1);
 Case symbol of
 '+':res:=sym_1 or sym;
 '*':res:=sym_1 and sym;
 end;//of case
 push_int(res);
end;//of else
end;//of else
 until symbol=#0;
pop_int(sym);
count_opn:=sym;
end;//of count_opz
//_____________________________________________________________________
procedure stepen_chisla(var stepen:integer);
var h,d,i:longint;
 begin
  resalt:=1;
  if stepen=0 then resalt:=1
   else
    begin
     For i:=1 to stepen do
     resalt:=resalt*2;
    end;
  end;
//_________________________________________________________________
Function step_2(stepen:integer):integer;
var h,d,i:integer;
 begin
  resalt:=1;
  if stepen=0 then resalt:=1
   else
    begin
     For i:=1 to stepen do
     resalt:=resalt*2;
    end;
  step_2:=resalt;
  end;
//________________________________________________________________________
Procedure Skleivanie(term_1,term_2:string;var resalt:string;var skleika:boolean;var kol_vo_skleek:integer);
var
 term_finish:string;
 i,kol_vo_otl,position:integer;
 BEGIN
  kol_vo_otl:=0;
 For i:=1 to length(term_1) do
  begin
   if term_1[i]<>term_2[i] then
    begin
     inc(kol_vo_otl);
     position:=i;
    end;
   end;
 if kol_vo_otl=1 then
  begin
   term_finish:=term_1;
   term_finish[position]:='x';
   skleika:=true;
   inc(kol_vo_skleek);
   resalt:=term_finish;
  end
 else
  begin
   skleika:=false;
   end;
 END;
//_____________________________________________________________________
Procedure Minimization(kol_vo_term_1,nomer:integer;var Massiv_1:Tablica;var Massiv_2:Tablica;var kol_vo_term:integer;var kol_vo_skleek:integer);
 var w,g,z,i,k:integer;
     correct:boolean;
     resalt,nomer_stroki:string;
BEGIN
  w:=Massiv_1[nomer-1,1].kol_vo_1;// кол-во единиц в терме
  g:=1;//счетчик старой таблицы
  k:=1;//счетчик новой таблицы
  For z:=1 to kol_vo_term_1 do
   begin
    While Massiv_1[nomer-1,g].kol_vo_1=w do
     begin
      Form1.Canvas.TextOut(760,150,'qwert');
      For i:=1 to kol_vo_term_1 do
      begin
       if Massiv_1[nomer-1,i].kol_vo_1=w+1 then
        begin
         Skleivanie(Massiv_1[nomer-1,g].term,Massiv_1[nomer-1,i].term,resalt,correct,kol_vo_skleek);
         if (correct=true)then
          begin
           Massiv_2[nomer,k].term:=resalt;
           Massiv_2[nomer,k].kol_vo_1:=w;
           Massiv_1[nomer-1,g].skleen:=true;
           Massiv_1[nomer-1,i].skleen:=true;
           Massiv_1[nomer-1,g].func:='+';
           Massiv_1[nomer-1,i].func:='+';
           nomer_stroki:=Massiv_1[nomer-1,g].nomer_stroki+','+Massiv_1[nomer-1,i].nomer_stroki;
           Massiv_2[nomer,k].nomer_stroki:=nomer_stroki;
           inc(k);
          end;// of if  correct=true
         end;//of if Massiv_1[nomer-1,i].kol_vo_1=w+1
      end;// i:=1 to stepen do
   inc(g);
  end;//of   While Massiv_1[nomer-1,g].kol_vo_1=w
  inc(w);
 end;// of  For z:=1 to kount-1
dec(k);
kol_vo_term:=k;
END;// of Minimization
//___________________________________________________________________________
Procedure Poisk_kol_va_x_v_stolbe(Massiv:Matrica;nomer_stolba,final_kol_vo_term:integer; var kol_vo_x_stolb:integer);
var i,g:integer;
begin
kol_vo_x_stolb:=0;
 For g:=1 to final_kol_vo_term do
  begin
   if Massiv[nomer_stolba,g]='X' then
    begin
     inc(kol_vo_x_stolb);
    end;
  end;
end;
//_____________________________________________________________________________
Procedure Poisk_suchestven_implicant(var Impl_matr:Tablica_implicant;Massiv:Matrica;final_kol_vo_term,kol_vo_nach_term:integer);
var i,g,kol_vo_x_stolb:integer;
begin
for g:=1 to final_kol_vo_term do
 begin
  for i:=1 to kol_vo_nach_term do
   begin
     if Massiv[i,g]='X' then
     begin
      Poisk_kol_va_x_v_stolbe(Massiv,i,final_kol_vo_term,kol_vo_x_stolb);
       if kol_vo_x_stolb=1 then
        begin
         Impl_matr[g].skleen:=true;
        end;
     end;
   end;
 end;

end;
//____________________________________________________________________________
function Chet_1(chislo:integer):integer;     //Процедура считает количество 1 в двоичной записи числа
var  kol_vo_1_v_2_zapisi:integer;
promegutoch_res:integer;
chislo_dvoichnoe:string;
Begin
chislo_dvoichnoe:='';
While chislo>=2 do
 begin
  promegutoch_res:=chislo mod 2;
  chislo:=chislo div 2;
  chislo_dvoichnoe:=inttostr(promegutoch_res)+chislo_dvoichnoe;
 end;
chislo_dvoichnoe:=inttostr(chislo)+chislo_dvoichnoe;
kol_vo_1_v_2_zapisi:=0;
For i:=1 to length(chislo_dvoichnoe) do
begin
if chislo_dvoichnoe[i]='1' then
inc(kol_vo_1_v_2_zapisi);
end;
Chet_1:=kol_vo_1_v_2_zapisi
End;
//________________________________________________________
Procedure otvetnaia(Massiv:tablica_implicant;chislo:integer;var stroka_otvet:string;final_kol_vo_term:integer);
var promegutoch_res,k,qq,i:integer;
chislo_dvoichnoe,otvet_term:string;      // процедура из переданной в неё импликанты делает нормальный ответ
Begin                                    // например, 1хх0=a!d
chislo_dvoichnoe:='';
for i:=1 to final_kol_vo_term do
chislo_dvoichnoe:=chislo_dvoichnoe+'0';
qq:=0;
if chislo=3 then
begin
qq:=1;
end;
For i:=1 to final_kol_vo_term do
begin
if ((chislo div step_2(i-1)) and 1) =1 then
chislo_dvoichnoe[i]:='1'
else
chislo_dvoichnoe[i]:='0';
end;
stroka_otvet:='       ';
for i:=1 to length(chislo_dvoichnoe) do
begin
if chislo_dvoichnoe[i]='1' then
begin
otvet_term:='  ';
For k:=1 to length(massiv[i].term) do
begin
if massiv[i].term[k]<>'x' then
begin
if Massiv[i].term[k]='1' then
otvet_term:=otvet_term+numbers[k].operand;
if Massiv[i].term[k]='0' then
otvet_term:=otvet_term+'!'+numbers[k].operand;
end;
end;
if stroka_otvet='       ' then
stroka_otvet:=stroka_otvet+otvet_term+' '
else
if stroka_otvet<> '       ' then
stroka_otvet:=stroka_otvet+'+'+otvet_term+' ';
end;
end;

End;
//______________________________________________________________________
procedure TForm1.FormCreate(Sender: TObject);
var i,g:integer;
begin
minimize:=false;
truthtable:=false;
clearation:=true;
application.HintHidePause:=5000;// задает время высвечивания подсказки hint 5 секунд.
stringgrid1.Visible:=false;
stringgrid2.Visible:=false;
stringgrid3.Visible:=false;
For i:=1 to 10 do
begin
For g:=1 to 3000 do
begin
Tables[i,g].skleen:=false;
Tables[i,g].func:='-';
Tables[i,g].term:='q';
end;
end;
For i:=1 to 31 do begin
For g:=1 to 31 do begin
M[i,g]:='';
end;
end;
end;

procedure TForm1.ToolButton2Click(Sender: TObject);// заполнение таблицы истинности
var x,i:integer;
prom_term1,prom_term2:string;
begin
if translate=false then
begin
MessageDlg('Трансляция не проведена',mtError,[mbOK],0);
exit;
end;
if truthtable=true then
begin
MessageDlg('Таблица истинности построена для создания новой выполните очистку',mtError,[mbOK],0);
exit;
end;
 hight:=0;
 hight:=hight+labelh;
 Label6.Top:=0;
 Label6.left:=10;
 Label6.Caption:='Таблица истинности';
 x:=kount;// кол-во переменных
 stepen_chisla(x);
 stepen:=resalt;// кол-во переборов переменных
 stringgrid1.rowcount:=resalt+1;// размеры таблицы
 stringgrid1.colcount:=kount+2;
 stringgrid1.top:=hight;
 stringgrid1.Visible:=true;
 stringgrid1.height:=25*stringgrid1.rowcount;
 stringgrid1.DefaultColWidth:=50;
 stringgrid1.Width:=(stringgrid1.DefaultColWidth+1)*stringgrid1.colcount;
 hight:=hight+stringgrid1.height+zazor;

 Implicant_matrix_hight:= hight;

 For i:=1 to kount do stringgrid1.cells[i,0]:=numbers[i].operand;// имена переменных в таблицу
 stringgrid1.cells[kount+1,0]:='Function';// имя поля в таблицу

 For i:=1 to stepen do stringgrid1.cells[0,i]:=Floattostr(i-1);// столбец с номером переменной в табл.

 chislo:=0; // заполнение таблицы истинности
 x:=kount;
 stepen_chisla(x);
 stepen:=resalt;
// цикл заполнения значениями переменных
 For i:=1 to stepen do // кол-во переборов
  begin
   tables[0,i].term:='';
    For g:=kount downto 1 DO // кол-во переменных
     begin
      y:=kount-g;// 0,1,2,3,4..
      stepen_chisla(y);
      h:=resalt;// 1,2,4,8,16..
      numbers[g].operator:=(chislo div h) and 1;// делим число на 1,2,4,8.., берем h разряд
      stringgrid1.cells[g,i]:=inttostr(numbers[g].operator);// запись в таблицу
      tables[0,i].term:=tables[0,i].term+inttostr(numbers[g].operator);// запись в массив
     end;
    Count_OPZ; // рассчет значения функции
    stringgrid1.cells[kount+1,i]:=Inttostr(count_opn);// вывод значения на экран
    tables[0,i].func:=Inttostr(count_opn);
    tables[0,i].nomer_stroki:=inttostr(i-1);
    inc(chislo);
   end;

   all0:=true;// ответ равен 1 или 0 начало
   all1:=true;
   For i:=1 to stepen do
    begin
      if tables[0,i].func<>'0' then all0:=false;
      if tables[0,i].func<>'1' then all1:=false;
    end;
      // if all0 then MessageDlg('ALL0',mtError,[mbOK],0);
      // if all1 then MessageDlg('ALL1',mtError,[mbOK],0);
   For i:=1 to stepen do // изменение порядка следования разрядов в терме
     begin
      prom_term1:=tables[0,i].term;
      prom_term2:=tables[0,i].term;//открыть в строке kount позиций
      for g:=1 to kount do
       begin
        prom_term2[kount-g+1]:=prom_term1[g];
       end;
     tables[0,i].term:=prom_term2;
     end;
    truthtable:=true;
    clearation:=false;
    Scrollbox1.VertScrollBar.Range:=hight+labelh;
 end;

procedure TForm1.ToolButton3Click(Sender: TObject);
var i,z,g,k,j,gol_1,Kol_vo_term,w,nomer,kol_vo_skleek,kol_vo_prohodov:INTEGER;
kol_vo_nach_term,final_kol_vo_term,nomer_terma_int,kol_vo_term_1,nomer_implicant,kol_vo_x_stolb,kol_vo_term_povtor:integer;
gol_2,gol_4,gol_3,resalt,term_finish,nomer_terma,chislo_dvoichnoe,implicant_stroka,stroka_otvet,stroka_prom:string;
//implicant_mask:longint;
correct,povtor,right,Last_tabl_empty:boolean;
begin
Scrollbox1.VertScrollBar.Range:=0;
if truthtable=false then
begin
MessageDlg('Нет таблицы истинности',mtError,[mbOK],0);
exit;
end;

if minimize=true then
begin
MessageDlg('Минимизация проведена выполните очистку',mtError,[mbOK],0);
exit;
end;


If  ((all0=false) and (all1=false)) then
begin // если при всех наборах переменных функция не равна нулю или единице тогда минимизируем

g:=0;// кол-во единиц=0
For i:=1 to stepen do           //Поиск количества единиц в терме.
begin
string_pointer:=1;
Repeat
get_symbol(tables[0,i].term);
if symbol='1' then
inc(g);
until symbol=#0;
tables[0,i].kol_vo_1:=g;// кол-во единиц в поле записи
g:=0;
end;

for k := 1 to stepen do                   //сортировка таблицы истинности по
 begin                                    //количеству единиц в терме
  for i := 1 to stepen-1 do
   begin
    if tables[0,i].kol_vo_1 > tables[0,i+1].kol_vo_1 then
     begin
      gol_1:=tables[0,i].kol_vo_1;
      gol_2:=tables[0,i].term;
      gol_3:=tables[0,i].func;
      gol_4:=tables[0,i].nomer_stroki;
      tables[0,i].term:=tables[0,i+1].term;
      tables[0,i].func:=tables[0,i+1].func;
      tables[0,i].nomer_stroki:=tables[0,i+1].nomer_stroki;
      tables[0,i].kol_vo_1:=tables[0,i+1].kol_vo_1;

      tables[0,i+1].kol_vo_1:=gol_1;
      tables[0,i+1].term:=gol_2;
      tables[0,i+1].func:=gol_3;
      tables[0,i+1].nomer_stroki:=gol_4;
     end;
   end;
  end;

dlabel[1]:=tlabel.Create(ScrollBox1);
dlabel[1].Parent:=ScrollBox1;
dlabel[1].caption:='Сортировка термов по группам';
dlabel[1].left:=10;
dlabel[1].top:=hight;
hight:=hight+labelh;
Scrollbox1.VertScrollBar.Range:=hight+labelh;
strgrid[1]:=Tstringgrid.Create(ScrollBox1);
strgrid[1].Parent:=ScrollBox1;
strgrid[1].Visible:=true;
strgrid[1].colcount:=4;
strgrid[1].cells[0,0]:='№ Строки';
strgrid[1].cells[1,0]:='Кол-во 1';
strgrid[1].cells[2,0]:='Минтерм';
strgrid[1].cells[3,0]:='Склеивание';
strgrid[1].Top:=hight;
strgrid[1].left:=0;
strgrid[1].borderStyle:=bsNone;
strgrid[1].scrollbars:=ssnone;
g:=1;
for I := 1 to stepen do
begin
if tables[0,i].func='1' then
begin
Tables[1,g].nomer_stroki:=tables[0,i].nomer_stroki;
Tables[1,g].kol_vo_1:=tables[0,i].kol_vo_1;
Tables[1,g].term:=tables[0,i].term;
inc(g);
end;
end;
kol_vo_nach_term:=g;
kol_vo_term:=g;
strgrid[1].rowcount:=kol_vo_term;
strgrid[1].height:=24*(kol_vo_term+2);
hight_1:=hight+strgrid[1].height+zazor;;
hight:=hight+strgrid[1].height+zazor;
dec(kol_vo_nach_term);
dec(kol_vo_term);
For  g:=1 to kol_vo_term do
begin
strgrid[1].cells[0,g]:=tables[1,g].nomer_stroki; //заполнение второй таблицы
strgrid[1].cells[1,g]:=inttostr(tables[1,g].kol_vo_1);
strgrid[1].cells[2,g]:=tables[1,g].term;
strgrid[1].cells[3,g]:=tables[1,g].func;
end;

//________________________________________________________________________________________

if kol_vo_nach_term>1 then
begin
nomer:=2;
nomer_implicant:=1;                     
Repeat
 kol_vo_term_1:=kol_vo_term;
 kol_vo_skleek:=0;
 Minimization(kol_vo_term_1,nomer,Tables,Tables,kol_vo_term,kol_vo_skleek);
    For i:=1 to kol_vo_term_1 do
  begin
   strgrid[nomer-1].Cells[3,i]:=Tables[nomer-1,i].func;
   if (tables[nomer-1,i].skleen = false) then
    begin
     Implicant_matrix[nomer_implicant].term:=Tables[nomer-1,i].term;
     Implicant_matrix[nomer_implicant].nomer_stroki:=Tables[nomer-1,i].nomer_stroki;
     Implicant_matrix[nomer_implicant].kol_vo_1:=Tables[nomer-1,i].kol_vo_1;
     inc(nomer_implicant);
    end;
  end;

 if kol_vo_skleek<>0 then
 begin
 dlabel[nomer]:=tlabel.Create(form1.ScrollBox1);
 dlabel[nomer].Parent:=Form1.ScrollBox1;
 dlabel[nomer].caption:='Склеивание термов';
 dlabel[nomer].left:=10;
 dlabel[nomer].top:=hight;
 hight:=hight+labelh;

 strgrid[nomer]:=Tstringgrid.Create(form1.ScrollBox1);
 strgrid[nomer].Parent:=Form1.ScrollBox1;
 strgrid[nomer].Visible:=true;
 strgrid[nomer].colcount:=4;
 strgrid[nomer].cells[0,0]:='№ Строки';
 strgrid[nomer].cells[1,0]:='Кол-во 1';
 strgrid[nomer].cells[2,0]:='Минтерм';
 strgrid[nomer].cells[3,0]:='Склеивание';
 //strgrid[nomer].cells[4,0]:='Кол-во склеек';
 strgrid[nomer].Top:=hight;
 strgrid[nomer].left:=0;
 strgrid[nomer].borderStyle:=bsNone;
 strgrid[nomer].scrollbars:=ssnone;
 strgrid[nomer].DefaultColWidth:=100;
 strgrid[nomer].ColWidths[0]:=250;
 strgrid[nomer].width:=(strgrid[nomer].DefaultColWidth+2)*3+strgrid[nomer].ColWidths[0];
 strgrid[nomer].rowcount:=kol_vo_term+1;
 strgrid[nomer].height:=24*(kol_vo_term+3);
  For i:=1 to kol_vo_term do
   begin
    strgrid[nomer].Cells[0,i]:=Tables[nomer,i].nomer_stroki;
    strgrid[nomer].Cells[1,i]:=inttostr(Tables[nomer,i].kol_vo_1);
    strgrid[nomer].Cells[2,i]:=Tables[nomer,i].term;
    //strgrid[nomer].Cells[4,i]:=inttostr(kol_vo_skleek);
    strgrid[nomer].Cells[3,i]:=tables[nomer,i].func;
   end;
  hight:=hight+strgrid[nomer].height+zazor;
  vyzov_sckl:=0;
   For i:=2 to kol_vo_term do
    begin
     if Tables[nomer,i].kol_vo_1<>Tables[nomer,1].kol_vo_1 then
        vyzov_sckl:=1;
    end;
 For i:=1 to kol_vo_term_1 do
  begin
   strgrid[nomer-1].Cells[3,i]:=Tables[nomer-1,i].func;
   if (tables[nomer-1,i].skleen = false) then
    begin
     Implicant_matrix[nomer_implicant].term:=Tables[nomer-1,i].term;
     Implicant_matrix[nomer_implicant].nomer_stroki:=Tables[nomer-1,i].nomer_stroki;
     Implicant_matrix[nomer_implicant].kol_vo_1:=Tables[nomer-1,i].kol_vo_1;
     inc(nomer_implicant);
    end;
  end;

 inc(nomer);

 end
 else
 begin

end;
Until (kol_vo_skleek=0) or (vyzov_sckl=0) ;
dec(nomer_implicant);

final_kol_vo_term:=nomer_implicant+kol_vo_term;

g:=1;
For i:=1 to (final_kol_vo_term) do
begin
if i<= kol_vo_term then
begin
Implicant_matrix_mid[i].term:=Tables[nomer-1,i].term;
Implicant_matrix_mid[i].nomer_stroki:=Tables[nomer-1,i].nomer_stroki;
end
else
begin
Implicant_matrix_mid[i].term:=Implicant_matrix[g].term;
Implicant_matrix_mid[i].nomer_stroki:=Implicant_matrix[g].nomer_stroki;
inc(g);
end;
end;

k:=2;
implicant_matrix_1[1].term:=implicant_matrix_mid[1].term;
implicant_matrix_1[1].nomer_stroki:=implicant_matrix_mid[1].nomer_stroki;
For i:=2 to final_kol_vo_term do
begin
 povtor:=false;
 For g:=1 to k do
  begin
   if implicant_matrix_mid[i].term = implicant_matrix_1[g].term then
    begin
     povtor:=true;
    end;
  end;
 if povtor=false then
  begin
   Implicant_matrix_1[k].term:=Implicant_matrix_mid[i].term;
   Implicant_matrix_1[k].kol_vo_1:=Implicant_matrix_mid[i].kol_vo_1;
   Implicant_matrix_1[k].nomer_stroki:=Implicant_matrix_mid[i].nomer_stroki;
   inc(k);
  end;
end;

dec(k);
final_kol_vo_term:=k;
;
 if hight>32767 then
  begin
   MessageDlg('Размеры таблиц склеивания термов слишком большие и не будут выведены',mtInformation,[mbOK],0);
   hight:=Implicant_matrix_hight;
   strgrid[1].Visible:=false;
   dlabel[1].Visible:=False;
 end;
//================================================================
Label7.Top:=hight;
Label7.left:=10;
Label7.Caption:='Импликантная матрица. Поиск минимального покрытия.';
hight:=hight+labelh;
Label8.Top:=hight;
Label8.left:=10;
Label8.Caption:='Голубым цветом выделены существенные импликанты, зеленым несущественные импликанты входящие в покрытие.';
hight:=hight+labelh;

stringgrid2.Parent:=Form1.ScrollBox1;
stringgrid2.Visible:=true;
stringgrid2.colcount:=kol_vo_nach_term+1;
stringgrid2.Top:=hight;
stringgrid2.left:=0;
stringgrid2.borderStyle:=bsNone;
//stringgrid2.scrollbars:=ssnone;
stringgrid2.rowcount:=final_kol_vo_term+1;
stringgrid2.DefaultColWidth:=100;
stringgrid2.ColWidths[0]:=250;
stringgrid2.height:=24*(final_kol_vo_term+2);
//stringgrid2.Width:=stringgrid2.DefaultColWidth*(kol_vo_nach_term+2);
stringgrid2.Width:=form1.Width-30;
//Form1.canvas.TextOut(600,400,inttostr(final_kol_vo_term));



For i:=1 to kol_vo_nach_term do
begin
stringgrid2.cells[i,0]:=Tables[1,i].term+','+Tables[1,i].nomer_stroki;
end;



For i:=1 to final_kol_vo_term do
begin
stringgrid2.Cells[0,i]:=Implicant_matrix_1[i].term+','+Implicant_matrix_1[i].nomer_stroki;
end;



For k:=1 to final_kol_vo_term do
begin
For i:=1 to length(Implicant_matrix_1[k].nomer_stroki) do
begin
if (Implicant_matrix_1[k].nomer_stroki[i] in symbols) and (Implicant_matrix_1[k].nomer_stroki[i+1] in symbols) then
begin
nomer_terma_int:=strtoint(Implicant_matrix_1[k].nomer_stroki[i]+Implicant_matrix_1[k].nomer_stroki[i+1]);
end
else
begin
if (Implicant_matrix_1[k].nomer_stroki[i] in symbols)and not(Implicant_matrix_1[k].nomer_stroki[i-1] in symbols) then
begin
nomer_terma_int:=strtoint(Implicant_matrix_1[k].nomer_stroki[i]);
end;
end;
For g:=1 to kol_vo_nach_term do
begin
if nomer_terma_int=strtoint(tables[1,g].nomer_stroki) then
begin
M[g,k]:='X';
stringgrid2.Cells[g,k]:=M[g,k];
end;
end;
end;
end;

 for i:=1 to final_kol_vo_term do
Implicant_matrix_1[i].skleen:=false;
hight:=hight+stringgrid2.height+zazor;

Poisk_suchestven_implicant(Implicant_matrix_1,M,final_kol_vo_term,kol_vo_nach_term);
implicant_mask:=0;
for i:=1 to final_kol_vo_term do
begin
if Implicant_matrix_1[i].skleen=true then
begin
implicant_mask:=implicant_mask or step_2(i-1);
end;
end;
//_____________________________________________________________________________
implicant_stroka:='                                                                 ';
Last_tabl_empty:=true;
kol_vo_prohodov:=1;
For i:=1 to (step_2(final_kol_vo_term))-1 do // переборы всех импликант
begin
  right:=true;
  stroka_otvet:='';
  implicant_stroka:='                                                                 ';
  if (implicant_mask and i)= implicant_mask then
  begin

  For g:=1 to final_kol_vo_term do // перебор импликант в наборе
   begin
    if ((i div step_2(g-1))and 1)=1 then // проверка входит ли импликанта в набор
     begin
      for k:=1 to kol_vo_nach_term do // перебор строк импликантной матрицы и запись крестиков в выходную строку
       begin
        if M[k,g]='X' then
         begin
          implicant_stroka[k]:='X';
         end// of if M[k,g]='X'
       end;// of for k:=1 to kol_vo_nach_term
     end;// of if ((i div step_2(g-1))and 1)=1
  end;// For g:=1 to nomer_implicant do
  for z:=1 to kol_vo_nach_term do
   begin
    if implicant_stroka[z]<>'X' then
     right:=false;
    end;
    if right=true then
     begin
      if kol_vo_prohodov=1 then
       begin
        Otvet[1].kol_vo_implicant:=chet_1(i);
        otvetnaia(Implicant_matrix_1,i,stroka_otvet,final_kol_vo_term);
        Otvet[1].stroka:=stroka_otvet;
        Otvet_mask:=i;
        inc(kol_vo_prohodov);
       end;// kol_vo_prohodov=1

       kol_vo_term:=chet_1(i);

      if kol_vo_term < otvet[1].kol_vo_implicant then
       begin
        Otvet[1].kol_vo_implicant:=chet_1(i);
        otvetnaia(Implicant_matrix_1,i,stroka_otvet,final_kol_vo_term);
        Otvet[1].stroka:=stroka_otvet;
        Otvet_mask:=i;
       end;//kol_vo_term < otvet[1].kol_vo_implicant
     end;// if right=true
    end;//for z:=1 to kol_vo_nach_term
  end;//For i:=1 to (step_2(final_kol_vo_term))-1

Label9.Top:=hight;
Label9.left:=10;
Label9.Caption:='Результат минимизации - ответ.';
hight:=hight+labelh;

Label10.Top:=hight;
Label10.left:=10;
Label10.Caption:=otvet[1].stroka;
hight:=hight+labelh;

Scrollbox1.VertScrollBar.Range:=hight+labelh;

end//of if kol_vo_nach_term>1
else // функция содержит один терм
begin

if kol_vo_nach_term=1 then
begin
 Implicant_matrix_1[1].term:=tables[1,1].term;
 Implicant_matrix_1[1].nomer_stroki:=tables[1,1].nomer_stroki;
 final_kol_vo_term:=1;
 nomer_implicant:=0;
end;
//hight:=hight+strgrid[1].height+zazor;
hight:=hight_1;
Scrollbox1.VertScrollBar.Range:=hight+labelh;
Label9.Top:=hight;
Label9.left:=10;
Label9.Caption:='Минимизация не проводилась, функция состоит из одного терма - ответ.';
hight:=hight+labelh;
Label10.Top:=hight;
Label10.left:=10;
stroka_prom:=tables[1,1].term;
stroka_otvet:='';

for i:=1 to kount  do
    begin
     if stroka_prom[i]='1' then stroka_otvet:=stroka_otvet+numbers[i].operand;
     if stroka_prom[i]='0' then stroka_otvet:=stroka_otvet+'!'+numbers[i].operand;
    end;
Label10.Caption:=stroka_otvet;
Scrollbox1.VertScrollBar.Range:=hight+labelh;

end;

end//of функция не равна нулю или единице
else // функция равна нулю или единице
 begin
//MessageDlg('ALL0',mtError,[mbOK],0);
//MessageDlg('ALL1',mtError,[mbOK],0);

if all0 then
begin
 Label9.Top:=hight;
 Label9.left:=10;
 Label9.Caption:='Минимизация не проводилась, функция равна нулю - ответ.';
 hight:=hight+labelh;
 Label10.Top:=hight;
 Label10.left:=10;
 Label10.Caption:='0';
end;// of all0

if all1 then
begin
 Label9.Top:=hight;
 Label9.left:=10;
 Label9.Caption:='Минимизация не проводилась, функция равна единице - ответ.';
 hight:=hight+labelh;
 Label10.Top:=hight;
 Label10.left:=10;
 Label10.Caption:='1';
end;// of all0


Scrollbox1.VertScrollBar.Range:=hight+labelh;
 end;
nomer_clear:=nomer;
minimize:=true;
clearation:=false;
end;
//_____________________________________________________________________


procedure TForm1.ToolButton4Click(Sender: TObject);
var i,j,k:integer;
begin
if clearation=true then
begin
MessageDlg('Очистка уже проведена',mtError,[mbOK],0);
exit;
end;


label10.Caption:='';
label4.Caption:='';
label6.Caption:='';
label7.Caption:='';
label8.Caption:='';
label9.Caption:='';
label5.Caption:='';

edit1.text:='';

output_string:='';
input_string:='';


for i:=0 to 70 do
 begin
  for j:=0 to 10 do
   begin
    stringgrid1.cells[j,i]:=' ';
    stringgrid2.cells[j,i]:=' ';
   end;
 end;

If minimize=true then// стирать динамические компоненты если они были созданы
begin
if not(all0 or all1) then dlabel[1].free;//счет nomer начинается с двух обращение к 1 компоненту выглядит как dlabel[1]
//в цикле его стереть нельзя, поскольку при единичном терме nomer=0. При единичной или нулевой функции dlabel[1]
// не создается

for i:=2 to nomer_clear-1 do dlabel[i].free;

if not(all0 or all1) then strgrid[1].free;//счет nomer начинается с двух обращение к 1 компоненту выглядит как strgrid[1]
//в цикле его стереть нельзя, поскольку при единичном терме nomer=0 При единичной или нулевой функции strgrid[1]
//не создается
for i:=2 to nomer_clear-1 do strgrid[i].free;
end;

stringgrid1.visible:=false;
stringgrid2.visible:=false;


kount:=0;

for i:=1 to 10 do
begin
 numbers[i].operand:=' ';
 numbers[i].operator:=2;
end;

for i:=1 to 10 do
 begin
  otvet[i].stroka:=' ';
  otvet[i].kol_vo_implicant:=0;
 end;


for k:=0 to nomer_clear-1 do
 begin
  for i:=0 to 3000 do
   begin
      tables[k,i].kol_vo_1:=0;
      tables[k,i].skleen:=false;

      tables[k,i].term:='q';
      tables[k,i].func:='-';
      tables[k,i].nomer_stroki:='';
   end;
 end;

  for i:=0 to 3000 do
   begin
    implicant_matrix[i].term:='';
    implicant_matrix[i].func:='-';
    implicant_matrix[i].kol_vo_1:=0;
    implicant_matrix[i].nomer_stroki:='';
    implicant_matrix[i].skleen:=false;

    implicant_matrix_1[i].term:='';
    implicant_matrix_1[i].func:='-';
    implicant_matrix_1[i].kol_vo_1:=0;
    implicant_matrix_1[i].nomer_stroki:='';
    implicant_matrix_1[i].skleen:=false;

    implicant_matrix_mid[i].term:='-';
    implicant_matrix_mid[i].func:='';
    implicant_matrix_mid[i].kol_vo_1:=0;
    implicant_matrix_mid[i].nomer_stroki:='';
    implicant_matrix_mid[i].skleen:=false;
   end;
 for i:=1 to 31 do
 begin
  for j:=0 to 31 do
   begin
    M[i,j]:='';
   end;
 end;
clearation:=true;
translate:=false;
truthtable:=false;
minimize:=false;
Scrollbox1.VertScrollBar.Range:=0;
InvalidateRect(form1.Handle,nil,true);//очистка экрана


end;

procedure TForm1.ToolButton1Click(Sender: TObject);

var error:word;
begin
if clearation=false then
begin
 MessageDlg('Очистка не проведена для минимизации новой функции выполните очистку',mtError,[mbOK],0);
 exit;
end;
if translate=true then
begin
 MessageDlg('Трансляция уже проведена выполните очистку',mtError,[mbOK],0);
 exit;
end;

string_pointer:=1;// переменная цикла для входной строки
stack_pointer:=1; // указатель стэка
stack_empty:=true;// стэк пуст
input_string:=(edit1.Text);
search_string_error(input_string,error);
if error=0 then
begin
OPN;
label5.Caption:=output_string;
translate:=true;
clearation:=false;
end;
end;

procedure TForm1.ToolButton6Click(Sender: TObject);
begin
close;
end;





procedure TForm1.N1Click(Sender: TObject);
begin
if OpenDialog1.Execute then
 begin
  FName := OpenDialog1.FileName;
  AssignFile(f, FName);
  reset(f);
  while not eof(f) do
   begin
    ReadLn(f, filestring);
    edit1.text:=filestring;
   end;
   closefile(f);
 end;
end;
   




procedure TForm1.N6Click(Sender: TObject);
begin
if SaveDialog1.Execute then
 begin
  FName := SaveDialog1.FileName;
  AssignFile(f1, FName);
  rewrite(f1);
  filestring:=edit1.text;
  write(f1,filestring);
  closefile(f1);
 end;
end;
//прокрутка scrollbox колесом мышки
procedure TForm1.wheelmove(Sender: TObject; Shift: TShiftState;
  WheelDelta: Integer; MousePos: TPoint; var Handled: Boolean);
begin
ScrollBox1.VertScrollBar.Position :=
ScrollBox1.VertScrollBar.Position - WheelDelta;
end;
//установка фокуса на scrollbox1 по клику на него для прокрутки мышкой
procedure TForm1.setscrfocus(Sender: TObject);
begin
 ScrollBox1.SetFocus;
end;

procedure TForm1.StringGrid2DrawCel(Sender: TObject; ACol, ARow: Integer;
  Rect: TRect; State: TGridDrawState);
  var row:integer;
begin

 row:=arow-1;
 stepen_chisla(row);// позиция бита столбца
 if (otvet_mask and resalt)<>0
  then
   begin
     if (implicant_mask and resalt)<>0// в импликантной маске выставлен бит столбца
      then StringGrid2.Canvas.Brush.color := clskyblue//ставим цвет строки существенной импликанты
       else StringGrid2.Canvas.Brush.color := clmoneygreen;//ставим цвет строки несущественной импликанты
   end//otvet_mask and resalt
    else StringGrid2.Canvas.Brush.color := clwhite;

If (ACol > 0) and (ARow>0) then
  begin

   if StringGrid2.Cells[ACol,ARow]='X' then
   begin
      //красим фон
    StringGrid2.canvas.fillRect(Rect);

      //красим текст
    StringGrid2.canvas.TextOut(Rect.Left,Rect.Top,StringGrid2.Cells[ACol,ARow]);
    end;

  end;

end;

procedure TForm1.ResizeForm1(Sender: TObject);
begin
stringgrid2.Width:=form1.Width-30;
Label5.Width:=form1.Width-45;
form1.edit1.Width:=form1.Width-35;
end;

procedure TForm1.N2Click(Sender: TObject);
var
i:integer;
Output_string:string;
begin
 Output_string:='';
 for i:=1 to length(otvet[1].stroka)//выбрасываем пробелы из ответа
  do
  begin
   if ((otvet[1].stroka[i]<>#32)) then Output_string:=Output_string+otvet[1].stroka[i];
  end;
 if SaveDialog2.Execute then
 begin
  FName := SaveDialog2.FileName;
  AssignFile(f2, FName);
  rewrite(f2);
  filestring:=edit1.text+' = '+Output_string;
  write(f2,filestring);
  closefile(f2);
 end;
end;

procedure TForm1.N4Click(Sender: TObject);
begin
Form2.ShowModal;
end;

procedure TForm1.N3Click(Sender: TObject);
begin
 if h=0 then
 WinExec('hh.exe help.htm',SW_Restore)
else
  begin
   ShowWindow(h,SW_Restore);
   Windows.SetForegroundWindow(h);
  end;
end;

end.


