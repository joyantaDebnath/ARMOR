import sys

sys.setrecursionlimit(7000)

from modules.helper import *
from modules.x509_ds import *


def Type(Begin):
    Temp = Begin
    FLAG_1, SIZE_1, VAL_1, Begin = match('1', True, Begin)
    if FLAG_1:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['1'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_2, SIZE_2, VAL_2, Begin = match('2', True, Begin)
    if FLAG_2:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['2'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_3, SIZE_3, VAL_3, Begin = match('3', True, Begin)
    if FLAG_3:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['3'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_4, SIZE_4, VAL_4, Begin = match('4', True, Begin)
    if FLAG_4:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['4'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_5, SIZE_5, VAL_5, Begin = match('5', True, Begin)
    if FLAG_5:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['5'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_6, SIZE_6, VAL_6, Begin = match('6', True, Begin)
    if FLAG_6:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['6'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_7, SIZE_7, VAL_7, Begin = match('7', True, Begin)
    if FLAG_7:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['7'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_8, SIZE_8, VAL_8, Begin = match('8', True, Begin)
    if FLAG_8:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['8'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_9, SIZE_9, VAL_9, Begin = match('9', True, Begin)
    if FLAG_9:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['9'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_10, SIZE_10, VAL_10, Begin = match('10', True, Begin)
    if FLAG_10:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['10'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_11, SIZE_11, VAL_11, Begin = match('11', True, Begin)
    if FLAG_11:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['11'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_12, SIZE_12, VAL_12, Begin = match('12', True, Begin)
    if FLAG_12:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['12'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_13, SIZE_13, VAL_13, Begin = match('13', True, Begin)
    if FLAG_13:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['13'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_14, SIZE_14, VAL_14, Begin = match('14', True, Begin)
    if FLAG_14:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['14'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_15, SIZE_15, VAL_15, Begin = match('15', True, Begin)
    if FLAG_15:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['15'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_16, SIZE_16, VAL_16, Begin = match('16', True, Begin)
    if FLAG_16:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['16'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_17, SIZE_17, VAL_17, Begin = match('17', True, Begin)
    if FLAG_17:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['17'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_18, SIZE_18, VAL_18, Begin = match('18', True, Begin)
    if FLAG_18:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['18'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_19, SIZE_19, VAL_19, Begin = match('19', True, Begin)
    if FLAG_19:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['19'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_20, SIZE_20, VAL_20, Begin = match('20', True, Begin)
    if FLAG_20:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['20'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_21, SIZE_21, VAL_21, Begin = match('21', True, Begin)
    if FLAG_21:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['21'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_22, SIZE_22, VAL_22, Begin = match('22', True, Begin)
    if FLAG_22:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['22'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_23, SIZE_23, VAL_23, Begin = match('23', True, Begin)
    if FLAG_23:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['23'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_24, SIZE_24, VAL_24, Begin = match('24', True, Begin)
    if FLAG_24:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['24'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_25, SIZE_25, VAL_25, Begin = match('25', True, Begin)
    if FLAG_25:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['25'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_26, SIZE_26, VAL_26, Begin = match('26', True, Begin)
    if FLAG_26:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['26'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_27, SIZE_27, VAL_27, Begin = match('27', True, Begin)
    if FLAG_27:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['27'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_28, SIZE_28, VAL_28, Begin = match('28', True, Begin)
    if FLAG_28:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['28'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_29, SIZE_29, VAL_29, Begin = match('29', True, Begin)
    if FLAG_29:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['29'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_30, SIZE_30, VAL_30, Begin = match('30', True, Begin)
    if FLAG_30:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['30'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_31, SIZE_31, VAL_31, Begin = match('31', True, Begin)
    if FLAG_31:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['31'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_32, SIZE_32, VAL_32, Begin = match('32', True, Begin)
    if FLAG_32:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['32'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_33, SIZE_33, VAL_33, Begin = match('33', True, Begin)
    if FLAG_33:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['33'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_34, SIZE_34, VAL_34, Begin = match('34', True, Begin)
    if FLAG_34:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['34'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_35, SIZE_35, VAL_35, Begin = match('35', True, Begin)
    if FLAG_35:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['35'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_36, SIZE_36, VAL_36, Begin = match('36', True, Begin)
    if FLAG_36:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['36'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_37, SIZE_37, VAL_37, Begin = match('37', True, Begin)
    if FLAG_37:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['37'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_38, SIZE_38, VAL_38, Begin = match('38', True, Begin)
    if FLAG_38:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['38'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_39, SIZE_39, VAL_39, Begin = match('39', True, Begin)
    if FLAG_39:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['39'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_40, SIZE_40, VAL_40, Begin = match('40', True, Begin)
    if FLAG_40:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['40'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_41, SIZE_41, VAL_41, Begin = match('41', True, Begin)
    if FLAG_41:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['41'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_42, SIZE_42, VAL_42, Begin = match('42', True, Begin)
    if FLAG_42:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['42'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_43, SIZE_43, VAL_43, Begin = match('43', True, Begin)
    if FLAG_43:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['43'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_44, SIZE_44, VAL_44, Begin = match('44', True, Begin)
    if FLAG_44:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['44'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_45, SIZE_45, VAL_45, Begin = match('45', True, Begin)
    if FLAG_45:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['45'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_46, SIZE_46, VAL_46, Begin = match('46', True, Begin)
    if FLAG_46:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['46'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_47, SIZE_47, VAL_47, Begin = match('47', True, Begin)
    if FLAG_47:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['47'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_48, SIZE_48, VAL_48, Begin = match('48', True, Begin)
    if FLAG_48:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['48'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_49, SIZE_49, VAL_49, Begin = match('49', True, Begin)
    if FLAG_49:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['49'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_50, SIZE_50, VAL_50, Begin = match('50', True, Begin)
    if FLAG_50:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['50'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_51, SIZE_51, VAL_51, Begin = match('51', True, Begin)
    if FLAG_51:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['51'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_52, SIZE_52, VAL_52, Begin = match('52', True, Begin)
    if FLAG_52:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['52'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_53, SIZE_53, VAL_53, Begin = match('53', True, Begin)
    if FLAG_53:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['53'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_54, SIZE_54, VAL_54, Begin = match('54', True, Begin)
    if FLAG_54:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['54'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_55, SIZE_55, VAL_55, Begin = match('55', True, Begin)
    if FLAG_55:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['55'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_56, SIZE_56, VAL_56, Begin = match('56', True, Begin)
    if FLAG_56:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['56'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_57, SIZE_57, VAL_57, Begin = match('57', True, Begin)
    if FLAG_57:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['57'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_58, SIZE_58, VAL_58, Begin = match('58', True, Begin)
    if FLAG_58:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['58'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_59, SIZE_59, VAL_59, Begin = match('59', True, Begin)
    if FLAG_59:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['59'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_60, SIZE_60, VAL_60, Begin = match('60', True, Begin)
    if FLAG_60:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['60'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_61, SIZE_61, VAL_61, Begin = match('61', True, Begin)
    if FLAG_61:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['61'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_62, SIZE_62, VAL_62, Begin = match('62', True, Begin)
    if FLAG_62:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['62'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_63, SIZE_63, VAL_63, Begin = match('63', True, Begin)
    if FLAG_63:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['63'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_64, SIZE_64, VAL_64, Begin = match('64', True, Begin)
    if FLAG_64:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['64'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_65, SIZE_65, VAL_65, Begin = match('65', True, Begin)
    if FLAG_65:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['65'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_66, SIZE_66, VAL_66, Begin = match('66', True, Begin)
    if FLAG_66:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['66'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_67, SIZE_67, VAL_67, Begin = match('67', True, Begin)
    if FLAG_67:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['67'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_68, SIZE_68, VAL_68, Begin = match('68', True, Begin)
    if FLAG_68:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['68'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_69, SIZE_69, VAL_69, Begin = match('69', True, Begin)
    if FLAG_69:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['69'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_70, SIZE_70, VAL_70, Begin = match('70', True, Begin)
    if FLAG_70:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['70'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_71, SIZE_71, VAL_71, Begin = match('71', True, Begin)
    if FLAG_71:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['71'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_72, SIZE_72, VAL_72, Begin = match('72', True, Begin)
    if FLAG_72:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['72'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_73, SIZE_73, VAL_73, Begin = match('73', True, Begin)
    if FLAG_73:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['73'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_74, SIZE_74, VAL_74, Begin = match('74', True, Begin)
    if FLAG_74:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['74'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_75, SIZE_75, VAL_75, Begin = match('75', True, Begin)
    if FLAG_75:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['75'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_76, SIZE_76, VAL_76, Begin = match('76', True, Begin)
    if FLAG_76:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['76'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_77, SIZE_77, VAL_77, Begin = match('77', True, Begin)
    if FLAG_77:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['77'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_78, SIZE_78, VAL_78, Begin = match('78', True, Begin)
    if FLAG_78:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['78'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_79, SIZE_79, VAL_79, Begin = match('79', True, Begin)
    if FLAG_79:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['79'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_80, SIZE_80, VAL_80, Begin = match('80', True, Begin)
    if FLAG_80:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['80'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_81, SIZE_81, VAL_81, Begin = match('81', True, Begin)
    if FLAG_81:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['81'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_82, SIZE_82, VAL_82, Begin = match('82', True, Begin)
    if FLAG_82:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['82'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_83, SIZE_83, VAL_83, Begin = match('83', True, Begin)
    if FLAG_83:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['83'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_84, SIZE_84, VAL_84, Begin = match('84', True, Begin)
    if FLAG_84:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['84'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_85, SIZE_85, VAL_85, Begin = match('85', True, Begin)
    if FLAG_85:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['85'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_86, SIZE_86, VAL_86, Begin = match('86', True, Begin)
    if FLAG_86:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['86'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_87, SIZE_87, VAL_87, Begin = match('87', True, Begin)
    if FLAG_87:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['87'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_88, SIZE_88, VAL_88, Begin = match('88', True, Begin)
    if FLAG_88:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['88'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_89, SIZE_89, VAL_89, Begin = match('89', True, Begin)
    if FLAG_89:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['89'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_90, SIZE_90, VAL_90, Begin = match('90', True, Begin)
    if FLAG_90:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['90'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_91, SIZE_91, VAL_91, Begin = match('91', True, Begin)
    if FLAG_91:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['91'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_92, SIZE_92, VAL_92, Begin = match('92', True, Begin)
    if FLAG_92:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['92'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_93, SIZE_93, VAL_93, Begin = match('93', True, Begin)
    if FLAG_93:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['93'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_94, SIZE_94, VAL_94, Begin = match('94', True, Begin)
    if FLAG_94:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['94'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_95, SIZE_95, VAL_95, Begin = match('95', True, Begin)
    if FLAG_95:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['95'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_96, SIZE_96, VAL_96, Begin = match('96', True, Begin)
    if FLAG_96:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['96'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_97, SIZE_97, VAL_97, Begin = match('97', True, Begin)
    if FLAG_97:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['97'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_98, SIZE_98, VAL_98, Begin = match('98', True, Begin)
    if FLAG_98:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['98'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_99, SIZE_99, VAL_99, Begin = match('99', True, Begin)
    if FLAG_99:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['99'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_100, SIZE_100, VAL_100, Begin = match('100', True, Begin)
    if FLAG_100:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['100'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_101, SIZE_101, VAL_101, Begin = match('101', True, Begin)
    if FLAG_101:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['101'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_102, SIZE_102, VAL_102, Begin = match('102', True, Begin)
    if FLAG_102:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['102'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_103, SIZE_103, VAL_103, Begin = match('103', True, Begin)
    if FLAG_103:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['103'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_104, SIZE_104, VAL_104, Begin = match('104', True, Begin)
    if FLAG_104:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['104'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_105, SIZE_105, VAL_105, Begin = match('105', True, Begin)
    if FLAG_105:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['105'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_106, SIZE_106, VAL_106, Begin = match('106', True, Begin)
    if FLAG_106:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['106'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_107, SIZE_107, VAL_107, Begin = match('107', True, Begin)
    if FLAG_107:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['107'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_108, SIZE_108, VAL_108, Begin = match('108', True, Begin)
    if FLAG_108:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['108'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_109, SIZE_109, VAL_109, Begin = match('109', True, Begin)
    if FLAG_109:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['109'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_110, SIZE_110, VAL_110, Begin = match('110', True, Begin)
    if FLAG_110:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['110'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_111, SIZE_111, VAL_111, Begin = match('111', True, Begin)
    if FLAG_111:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['111'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_112, SIZE_112, VAL_112, Begin = match('112', True, Begin)
    if FLAG_112:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['112'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_113, SIZE_113, VAL_113, Begin = match('113', True, Begin)
    if FLAG_113:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['113'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_114, SIZE_114, VAL_114, Begin = match('114', True, Begin)
    if FLAG_114:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['114'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_115, SIZE_115, VAL_115, Begin = match('115', True, Begin)
    if FLAG_115:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['115'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_116, SIZE_116, VAL_116, Begin = match('116', True, Begin)
    if FLAG_116:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['116'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_117, SIZE_117, VAL_117, Begin = match('117', True, Begin)
    if FLAG_117:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['117'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_118, SIZE_118, VAL_118, Begin = match('118', True, Begin)
    if FLAG_118:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['118'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_119, SIZE_119, VAL_119, Begin = match('119', True, Begin)
    if FLAG_119:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['119'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_120, SIZE_120, VAL_120, Begin = match('120', True, Begin)
    if FLAG_120:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['120'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_121, SIZE_121, VAL_121, Begin = match('121', True, Begin)
    if FLAG_121:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['121'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_122, SIZE_122, VAL_122, Begin = match('122', True, Begin)
    if FLAG_122:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['122'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_123, SIZE_123, VAL_123, Begin = match('123', True, Begin)
    if FLAG_123:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['123'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_124, SIZE_124, VAL_124, Begin = match('124', True, Begin)
    if FLAG_124:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['124'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_125, SIZE_125, VAL_125, Begin = match('125', True, Begin)
    if FLAG_125:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['125'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_126, SIZE_126, VAL_126, Begin = match('126', True, Begin)
    if FLAG_126:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['126'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_127, SIZE_127, VAL_127, Begin = match('127', True, Begin)
    if FLAG_127:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['127'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_128, SIZE_128, VAL_128, Begin = match('128', True, Begin)
    if FLAG_128:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['128'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_129, SIZE_129, VAL_129, Begin = match('129', True, Begin)
    if FLAG_129:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['129'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_130, SIZE_130, VAL_130, Begin = match('130', True, Begin)
    if FLAG_130:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['130'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_131, SIZE_131, VAL_131, Begin = match('131', True, Begin)
    if FLAG_131:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['131'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_132, SIZE_132, VAL_132, Begin = match('132', True, Begin)
    if FLAG_132:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['132'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_133, SIZE_133, VAL_133, Begin = match('133', True, Begin)
    if FLAG_133:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['133'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_134, SIZE_134, VAL_134, Begin = match('134', True, Begin)
    if FLAG_134:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['134'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_135, SIZE_135, VAL_135, Begin = match('135', True, Begin)
    if FLAG_135:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['135'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_136, SIZE_136, VAL_136, Begin = match('136', True, Begin)
    if FLAG_136:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['136'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_137, SIZE_137, VAL_137, Begin = match('137', True, Begin)
    if FLAG_137:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['137'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_138, SIZE_138, VAL_138, Begin = match('138', True, Begin)
    if FLAG_138:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['138'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_139, SIZE_139, VAL_139, Begin = match('139', True, Begin)
    if FLAG_139:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['139'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_140, SIZE_140, VAL_140, Begin = match('140', True, Begin)
    if FLAG_140:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['140'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_141, SIZE_141, VAL_141, Begin = match('141', True, Begin)
    if FLAG_141:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['141'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_142, SIZE_142, VAL_142, Begin = match('142', True, Begin)
    if FLAG_142:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['142'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_143, SIZE_143, VAL_143, Begin = match('143', True, Begin)
    if FLAG_143:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['143'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_144, SIZE_144, VAL_144, Begin = match('144', True, Begin)
    if FLAG_144:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['144'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_145, SIZE_145, VAL_145, Begin = match('145', True, Begin)
    if FLAG_145:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['145'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_146, SIZE_146, VAL_146, Begin = match('146', True, Begin)
    if FLAG_146:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['146'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_147, SIZE_147, VAL_147, Begin = match('147', True, Begin)
    if FLAG_147:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['147'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_148, SIZE_148, VAL_148, Begin = match('148', True, Begin)
    if FLAG_148:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['148'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_149, SIZE_149, VAL_149, Begin = match('149', True, Begin)
    if FLAG_149:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['149'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_150, SIZE_150, VAL_150, Begin = match('150', True, Begin)
    if FLAG_150:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['150'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_151, SIZE_151, VAL_151, Begin = match('151', True, Begin)
    if FLAG_151:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['151'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_152, SIZE_152, VAL_152, Begin = match('152', True, Begin)
    if FLAG_152:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['152'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_153, SIZE_153, VAL_153, Begin = match('153', True, Begin)
    if FLAG_153:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['153'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_154, SIZE_154, VAL_154, Begin = match('154', True, Begin)
    if FLAG_154:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['154'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_155, SIZE_155, VAL_155, Begin = match('155', True, Begin)
    if FLAG_155:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['155'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_156, SIZE_156, VAL_156, Begin = match('156', True, Begin)
    if FLAG_156:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['156'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_157, SIZE_157, VAL_157, Begin = match('157', True, Begin)
    if FLAG_157:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['157'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_158, SIZE_158, VAL_158, Begin = match('158', True, Begin)
    if FLAG_158:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['158'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_159, SIZE_159, VAL_159, Begin = match('159', True, Begin)
    if FLAG_159:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['159'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_160, SIZE_160, VAL_160, Begin = match('160', True, Begin)
    if FLAG_160:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['160'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_161, SIZE_161, VAL_161, Begin = match('161', True, Begin)
    if FLAG_161:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['161'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_162, SIZE_162, VAL_162, Begin = match('162', True, Begin)
    if FLAG_162:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['162'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_163, SIZE_163, VAL_163, Begin = match('163', True, Begin)
    if FLAG_163:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['163'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_164, SIZE_164, VAL_164, Begin = match('164', True, Begin)
    if FLAG_164:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['164'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_165, SIZE_165, VAL_165, Begin = match('165', True, Begin)
    if FLAG_165:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['165'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_166, SIZE_166, VAL_166, Begin = match('166', True, Begin)
    if FLAG_166:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['166'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_167, SIZE_167, VAL_167, Begin = match('167', True, Begin)
    if FLAG_167:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['167'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_168, SIZE_168, VAL_168, Begin = match('168', True, Begin)
    if FLAG_168:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['168'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_169, SIZE_169, VAL_169, Begin = match('169', True, Begin)
    if FLAG_169:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['169'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_170, SIZE_170, VAL_170, Begin = match('170', True, Begin)
    if FLAG_170:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['170'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_171, SIZE_171, VAL_171, Begin = match('171', True, Begin)
    if FLAG_171:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['171'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_172, SIZE_172, VAL_172, Begin = match('172', True, Begin)
    if FLAG_172:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['172'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_173, SIZE_173, VAL_173, Begin = match('173', True, Begin)
    if FLAG_173:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['173'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_174, SIZE_174, VAL_174, Begin = match('174', True, Begin)
    if FLAG_174:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['174'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_175, SIZE_175, VAL_175, Begin = match('175', True, Begin)
    if FLAG_175:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['175'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_176, SIZE_176, VAL_176, Begin = match('176', True, Begin)
    if FLAG_176:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['176'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_177, SIZE_177, VAL_177, Begin = match('177', True, Begin)
    if FLAG_177:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['177'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_178, SIZE_178, VAL_178, Begin = match('178', True, Begin)
    if FLAG_178:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['178'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_179, SIZE_179, VAL_179, Begin = match('179', True, Begin)
    if FLAG_179:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['179'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_180, SIZE_180, VAL_180, Begin = match('180', True, Begin)
    if FLAG_180:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['180'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_181, SIZE_181, VAL_181, Begin = match('181', True, Begin)
    if FLAG_181:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['181'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_182, SIZE_182, VAL_182, Begin = match('182', True, Begin)
    if FLAG_182:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['182'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_183, SIZE_183, VAL_183, Begin = match('183', True, Begin)
    if FLAG_183:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['183'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_184, SIZE_184, VAL_184, Begin = match('184', True, Begin)
    if FLAG_184:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['184'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_185, SIZE_185, VAL_185, Begin = match('185', True, Begin)
    if FLAG_185:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['185'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_186, SIZE_186, VAL_186, Begin = match('186', True, Begin)
    if FLAG_186:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['186'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_187, SIZE_187, VAL_187, Begin = match('187', True, Begin)
    if FLAG_187:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['187'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_188, SIZE_188, VAL_188, Begin = match('188', True, Begin)
    if FLAG_188:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['188'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_189, SIZE_189, VAL_189, Begin = match('189', True, Begin)
    if FLAG_189:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['189'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_190, SIZE_190, VAL_190, Begin = match('190', True, Begin)
    if FLAG_190:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['190'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_191, SIZE_191, VAL_191, Begin = match('191', True, Begin)
    if FLAG_191:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['191'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_192, SIZE_192, VAL_192, Begin = match('192', True, Begin)
    if FLAG_192:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['192'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_193, SIZE_193, VAL_193, Begin = match('193', True, Begin)
    if FLAG_193:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['193'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_194, SIZE_194, VAL_194, Begin = match('194', True, Begin)
    if FLAG_194:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['194'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_195, SIZE_195, VAL_195, Begin = match('195', True, Begin)
    if FLAG_195:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['195'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_196, SIZE_196, VAL_196, Begin = match('196', True, Begin)
    if FLAG_196:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['196'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_197, SIZE_197, VAL_197, Begin = match('197', True, Begin)
    if FLAG_197:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['197'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_198, SIZE_198, VAL_198, Begin = match('198', True, Begin)
    if FLAG_198:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['198'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_199, SIZE_199, VAL_199, Begin = match('199', True, Begin)
    if FLAG_199:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['199'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_200, SIZE_200, VAL_200, Begin = match('200', True, Begin)
    if FLAG_200:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['200'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_201, SIZE_201, VAL_201, Begin = match('201', True, Begin)
    if FLAG_201:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['201'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_202, SIZE_202, VAL_202, Begin = match('202', True, Begin)
    if FLAG_202:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['202'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_203, SIZE_203, VAL_203, Begin = match('203', True, Begin)
    if FLAG_203:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['203'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_204, SIZE_204, VAL_204, Begin = match('204', True, Begin)
    if FLAG_204:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['204'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_205, SIZE_205, VAL_205, Begin = match('205', True, Begin)
    if FLAG_205:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['205'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_206, SIZE_206, VAL_206, Begin = match('206', True, Begin)
    if FLAG_206:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['206'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_207, SIZE_207, VAL_207, Begin = match('207', True, Begin)
    if FLAG_207:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['207'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_208, SIZE_208, VAL_208, Begin = match('208', True, Begin)
    if FLAG_208:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['208'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_209, SIZE_209, VAL_209, Begin = match('209', True, Begin)
    if FLAG_209:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['209'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_210, SIZE_210, VAL_210, Begin = match('210', True, Begin)
    if FLAG_210:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['210'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_211, SIZE_211, VAL_211, Begin = match('211', True, Begin)
    if FLAG_211:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['211'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_212, SIZE_212, VAL_212, Begin = match('212', True, Begin)
    if FLAG_212:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['212'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_213, SIZE_213, VAL_213, Begin = match('213', True, Begin)
    if FLAG_213:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['213'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_214, SIZE_214, VAL_214, Begin = match('214', True, Begin)
    if FLAG_214:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['214'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_215, SIZE_215, VAL_215, Begin = match('215', True, Begin)
    if FLAG_215:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['215'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_216, SIZE_216, VAL_216, Begin = match('216', True, Begin)
    if FLAG_216:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['216'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_217, SIZE_217, VAL_217, Begin = match('217', True, Begin)
    if FLAG_217:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['217'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_218, SIZE_218, VAL_218, Begin = match('218', True, Begin)
    if FLAG_218:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['218'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_219, SIZE_219, VAL_219, Begin = match('219', True, Begin)
    if FLAG_219:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['219'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_220, SIZE_220, VAL_220, Begin = match('220', True, Begin)
    if FLAG_220:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['220'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_221, SIZE_221, VAL_221, Begin = match('221', True, Begin)
    if FLAG_221:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['221'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_222, SIZE_222, VAL_222, Begin = match('222', True, Begin)
    if FLAG_222:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['222'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_223, SIZE_223, VAL_223, Begin = match('223', True, Begin)
    if FLAG_223:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['223'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_224, SIZE_224, VAL_224, Begin = match('224', True, Begin)
    if FLAG_224:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['224'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_225, SIZE_225, VAL_225, Begin = match('225', True, Begin)
    if FLAG_225:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['225'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_226, SIZE_226, VAL_226, Begin = match('226', True, Begin)
    if FLAG_226:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['226'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_227, SIZE_227, VAL_227, Begin = match('227', True, Begin)
    if FLAG_227:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['227'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_228, SIZE_228, VAL_228, Begin = match('228', True, Begin)
    if FLAG_228:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['228'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_229, SIZE_229, VAL_229, Begin = match('229', True, Begin)
    if FLAG_229:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['229'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_230, SIZE_230, VAL_230, Begin = match('230', True, Begin)
    if FLAG_230:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['230'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_231, SIZE_231, VAL_231, Begin = match('231', True, Begin)
    if FLAG_231:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['231'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_232, SIZE_232, VAL_232, Begin = match('232', True, Begin)
    if FLAG_232:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['232'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_233, SIZE_233, VAL_233, Begin = match('233', True, Begin)
    if FLAG_233:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['233'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_234, SIZE_234, VAL_234, Begin = match('234', True, Begin)
    if FLAG_234:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['234'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_235, SIZE_235, VAL_235, Begin = match('235', True, Begin)
    if FLAG_235:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['235'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_236, SIZE_236, VAL_236, Begin = match('236', True, Begin)
    if FLAG_236:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['236'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_237, SIZE_237, VAL_237, Begin = match('237', True, Begin)
    if FLAG_237:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['237'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_238, SIZE_238, VAL_238, Begin = match('238', True, Begin)
    if FLAG_238:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['238'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_239, SIZE_239, VAL_239, Begin = match('239', True, Begin)
    if FLAG_239:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['239'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_240, SIZE_240, VAL_240, Begin = match('240', True, Begin)
    if FLAG_240:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['240'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_241, SIZE_241, VAL_241, Begin = match('241', True, Begin)
    if FLAG_241:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['241'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_242, SIZE_242, VAL_242, Begin = match('242', True, Begin)
    if FLAG_242:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['242'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_243, SIZE_243, VAL_243, Begin = match('243', True, Begin)
    if FLAG_243:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['243'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_244, SIZE_244, VAL_244, Begin = match('244', True, Begin)
    if FLAG_244:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['244'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_245, SIZE_245, VAL_245, Begin = match('245', True, Begin)
    if FLAG_245:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['245'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_246, SIZE_246, VAL_246, Begin = match('246', True, Begin)
    if FLAG_246:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['246'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_247, SIZE_247, VAL_247, Begin = match('247', True, Begin)
    if FLAG_247:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['247'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_248, SIZE_248, VAL_248, Begin = match('248', True, Begin)
    if FLAG_248:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['248'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_249, SIZE_249, VAL_249, Begin = match('249', True, Begin)
    if FLAG_249:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['249'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_250, SIZE_250, VAL_250, Begin = match('250', True, Begin)
    if FLAG_250:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['250'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_251, SIZE_251, VAL_251, Begin = match('251', True, Begin)
    if FLAG_251:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['251'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_252, SIZE_252, VAL_252, Begin = match('252', True, Begin)
    if FLAG_252:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['252'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_253, SIZE_253, VAL_253, Begin = match('253', True, Begin)
    if FLAG_253:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['253'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_254, SIZE_254, VAL_254, Begin = match('254', True, Begin)
    if FLAG_254:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['254'])
        return True, SIZE_Type, VAL_Type, Begin
    FLAG_255, SIZE_255, VAL_255, Begin = match('255', True, Begin)
    if FLAG_255:
        SIZE_Type = 1
        VAL_Type = hex_n_bytes_to_int_dsl(['255'])
        return True, SIZE_Type, VAL_Type, Begin
    return False, 0, None, Temp


def Typecheck(VAL_Id, Begin):
    Temp = Begin
    FLAG_Type, SIZE_Type, VAL_Type, Begin = Type(Begin)
    if FLAG_Type:
        SIZE_Typecheck = SIZE_Type
        VAL_Typecheck = VAL_Type
        if not (VAL_Type == VAL_Id):
            return False, 0, None, Temp
        return True, SIZE_Typecheck, VAL_Typecheck, Begin
    return False, 0, None, Temp


def Length(Begin):
    Temp = Begin
    FLAG_Shortlength, SIZE_Shortlength, VAL_Shortlength, Begin = Shortlength(Begin)
    if FLAG_Shortlength:
        SIZE_Length = SIZE_Shortlength
        VAL_Length = VAL_Shortlength
        return True, SIZE_Length, VAL_Length, Begin
    FLAG_Longlength, SIZE_Longlength, VAL_Longlength, Begin = Longlength(Begin)
    if FLAG_Longlength:
        SIZE_Length = SIZE_Longlength
        VAL_Length = hex_n_bytes_to_int_dsl([VAL_Longlength])
        if not (VAL_Length >= 128):
            return False, 0, None, Temp
        return True, SIZE_Length, VAL_Length, Begin
    return False, 0, None, Temp


def Shortlength(Begin):
    Temp = Begin
    FLAG_0, SIZE_0, VAL_0, Begin = match('0', True, Begin)
    if FLAG_0:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['0'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_1, SIZE_1, VAL_1, Begin = match('1', True, Begin)
    if FLAG_1:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['1'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_2, SIZE_2, VAL_2, Begin = match('2', True, Begin)
    if FLAG_2:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['2'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_3, SIZE_3, VAL_3, Begin = match('3', True, Begin)
    if FLAG_3:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['3'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_4, SIZE_4, VAL_4, Begin = match('4', True, Begin)
    if FLAG_4:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['4'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_5, SIZE_5, VAL_5, Begin = match('5', True, Begin)
    if FLAG_5:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['5'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_6, SIZE_6, VAL_6, Begin = match('6', True, Begin)
    if FLAG_6:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['6'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_7, SIZE_7, VAL_7, Begin = match('7', True, Begin)
    if FLAG_7:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['7'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_8, SIZE_8, VAL_8, Begin = match('8', True, Begin)
    if FLAG_8:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['8'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_9, SIZE_9, VAL_9, Begin = match('9', True, Begin)
    if FLAG_9:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['9'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_10, SIZE_10, VAL_10, Begin = match('10', True, Begin)
    if FLAG_10:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['10'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_11, SIZE_11, VAL_11, Begin = match('11', True, Begin)
    if FLAG_11:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['11'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_12, SIZE_12, VAL_12, Begin = match('12', True, Begin)
    if FLAG_12:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['12'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_13, SIZE_13, VAL_13, Begin = match('13', True, Begin)
    if FLAG_13:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['13'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_14, SIZE_14, VAL_14, Begin = match('14', True, Begin)
    if FLAG_14:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['14'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_15, SIZE_15, VAL_15, Begin = match('15', True, Begin)
    if FLAG_15:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['15'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_16, SIZE_16, VAL_16, Begin = match('16', True, Begin)
    if FLAG_16:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['16'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_17, SIZE_17, VAL_17, Begin = match('17', True, Begin)
    if FLAG_17:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['17'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_18, SIZE_18, VAL_18, Begin = match('18', True, Begin)
    if FLAG_18:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['18'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_19, SIZE_19, VAL_19, Begin = match('19', True, Begin)
    if FLAG_19:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['19'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_20, SIZE_20, VAL_20, Begin = match('20', True, Begin)
    if FLAG_20:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['20'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_21, SIZE_21, VAL_21, Begin = match('21', True, Begin)
    if FLAG_21:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['21'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_22, SIZE_22, VAL_22, Begin = match('22', True, Begin)
    if FLAG_22:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['22'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_23, SIZE_23, VAL_23, Begin = match('23', True, Begin)
    if FLAG_23:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['23'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_24, SIZE_24, VAL_24, Begin = match('24', True, Begin)
    if FLAG_24:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['24'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_25, SIZE_25, VAL_25, Begin = match('25', True, Begin)
    if FLAG_25:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['25'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_26, SIZE_26, VAL_26, Begin = match('26', True, Begin)
    if FLAG_26:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['26'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_27, SIZE_27, VAL_27, Begin = match('27', True, Begin)
    if FLAG_27:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['27'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_28, SIZE_28, VAL_28, Begin = match('28', True, Begin)
    if FLAG_28:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['28'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_29, SIZE_29, VAL_29, Begin = match('29', True, Begin)
    if FLAG_29:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['29'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_30, SIZE_30, VAL_30, Begin = match('30', True, Begin)
    if FLAG_30:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['30'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_31, SIZE_31, VAL_31, Begin = match('31', True, Begin)
    if FLAG_31:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['31'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_32, SIZE_32, VAL_32, Begin = match('32', True, Begin)
    if FLAG_32:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['32'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_33, SIZE_33, VAL_33, Begin = match('33', True, Begin)
    if FLAG_33:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['33'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_34, SIZE_34, VAL_34, Begin = match('34', True, Begin)
    if FLAG_34:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['34'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_35, SIZE_35, VAL_35, Begin = match('35', True, Begin)
    if FLAG_35:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['35'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_36, SIZE_36, VAL_36, Begin = match('36', True, Begin)
    if FLAG_36:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['36'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_37, SIZE_37, VAL_37, Begin = match('37', True, Begin)
    if FLAG_37:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['37'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_38, SIZE_38, VAL_38, Begin = match('38', True, Begin)
    if FLAG_38:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['38'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_39, SIZE_39, VAL_39, Begin = match('39', True, Begin)
    if FLAG_39:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['39'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_40, SIZE_40, VAL_40, Begin = match('40', True, Begin)
    if FLAG_40:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['40'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_41, SIZE_41, VAL_41, Begin = match('41', True, Begin)
    if FLAG_41:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['41'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_42, SIZE_42, VAL_42, Begin = match('42', True, Begin)
    if FLAG_42:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['42'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_43, SIZE_43, VAL_43, Begin = match('43', True, Begin)
    if FLAG_43:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['43'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_44, SIZE_44, VAL_44, Begin = match('44', True, Begin)
    if FLAG_44:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['44'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_45, SIZE_45, VAL_45, Begin = match('45', True, Begin)
    if FLAG_45:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['45'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_46, SIZE_46, VAL_46, Begin = match('46', True, Begin)
    if FLAG_46:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['46'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_47, SIZE_47, VAL_47, Begin = match('47', True, Begin)
    if FLAG_47:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['47'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_48, SIZE_48, VAL_48, Begin = match('48', True, Begin)
    if FLAG_48:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['48'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_49, SIZE_49, VAL_49, Begin = match('49', True, Begin)
    if FLAG_49:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['49'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_50, SIZE_50, VAL_50, Begin = match('50', True, Begin)
    if FLAG_50:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['50'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_51, SIZE_51, VAL_51, Begin = match('51', True, Begin)
    if FLAG_51:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['51'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_52, SIZE_52, VAL_52, Begin = match('52', True, Begin)
    if FLAG_52:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['52'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_53, SIZE_53, VAL_53, Begin = match('53', True, Begin)
    if FLAG_53:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['53'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_54, SIZE_54, VAL_54, Begin = match('54', True, Begin)
    if FLAG_54:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['54'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_55, SIZE_55, VAL_55, Begin = match('55', True, Begin)
    if FLAG_55:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['55'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_56, SIZE_56, VAL_56, Begin = match('56', True, Begin)
    if FLAG_56:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['56'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_57, SIZE_57, VAL_57, Begin = match('57', True, Begin)
    if FLAG_57:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['57'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_58, SIZE_58, VAL_58, Begin = match('58', True, Begin)
    if FLAG_58:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['58'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_59, SIZE_59, VAL_59, Begin = match('59', True, Begin)
    if FLAG_59:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['59'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_60, SIZE_60, VAL_60, Begin = match('60', True, Begin)
    if FLAG_60:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['60'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_61, SIZE_61, VAL_61, Begin = match('61', True, Begin)
    if FLAG_61:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['61'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_62, SIZE_62, VAL_62, Begin = match('62', True, Begin)
    if FLAG_62:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['62'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_63, SIZE_63, VAL_63, Begin = match('63', True, Begin)
    if FLAG_63:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['63'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_64, SIZE_64, VAL_64, Begin = match('64', True, Begin)
    if FLAG_64:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['64'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_65, SIZE_65, VAL_65, Begin = match('65', True, Begin)
    if FLAG_65:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['65'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_66, SIZE_66, VAL_66, Begin = match('66', True, Begin)
    if FLAG_66:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['66'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_67, SIZE_67, VAL_67, Begin = match('67', True, Begin)
    if FLAG_67:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['67'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_68, SIZE_68, VAL_68, Begin = match('68', True, Begin)
    if FLAG_68:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['68'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_69, SIZE_69, VAL_69, Begin = match('69', True, Begin)
    if FLAG_69:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['69'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_70, SIZE_70, VAL_70, Begin = match('70', True, Begin)
    if FLAG_70:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['70'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_71, SIZE_71, VAL_71, Begin = match('71', True, Begin)
    if FLAG_71:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['71'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_72, SIZE_72, VAL_72, Begin = match('72', True, Begin)
    if FLAG_72:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['72'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_73, SIZE_73, VAL_73, Begin = match('73', True, Begin)
    if FLAG_73:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['73'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_74, SIZE_74, VAL_74, Begin = match('74', True, Begin)
    if FLAG_74:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['74'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_75, SIZE_75, VAL_75, Begin = match('75', True, Begin)
    if FLAG_75:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['75'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_76, SIZE_76, VAL_76, Begin = match('76', True, Begin)
    if FLAG_76:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['76'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_77, SIZE_77, VAL_77, Begin = match('77', True, Begin)
    if FLAG_77:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['77'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_78, SIZE_78, VAL_78, Begin = match('78', True, Begin)
    if FLAG_78:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['78'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_79, SIZE_79, VAL_79, Begin = match('79', True, Begin)
    if FLAG_79:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['79'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_80, SIZE_80, VAL_80, Begin = match('80', True, Begin)
    if FLAG_80:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['80'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_81, SIZE_81, VAL_81, Begin = match('81', True, Begin)
    if FLAG_81:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['81'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_82, SIZE_82, VAL_82, Begin = match('82', True, Begin)
    if FLAG_82:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['82'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_83, SIZE_83, VAL_83, Begin = match('83', True, Begin)
    if FLAG_83:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['83'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_84, SIZE_84, VAL_84, Begin = match('84', True, Begin)
    if FLAG_84:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['84'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_85, SIZE_85, VAL_85, Begin = match('85', True, Begin)
    if FLAG_85:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['85'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_86, SIZE_86, VAL_86, Begin = match('86', True, Begin)
    if FLAG_86:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['86'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_87, SIZE_87, VAL_87, Begin = match('87', True, Begin)
    if FLAG_87:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['87'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_88, SIZE_88, VAL_88, Begin = match('88', True, Begin)
    if FLAG_88:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['88'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_89, SIZE_89, VAL_89, Begin = match('89', True, Begin)
    if FLAG_89:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['89'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_90, SIZE_90, VAL_90, Begin = match('90', True, Begin)
    if FLAG_90:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['90'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_91, SIZE_91, VAL_91, Begin = match('91', True, Begin)
    if FLAG_91:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['91'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_92, SIZE_92, VAL_92, Begin = match('92', True, Begin)
    if FLAG_92:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['92'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_93, SIZE_93, VAL_93, Begin = match('93', True, Begin)
    if FLAG_93:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['93'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_94, SIZE_94, VAL_94, Begin = match('94', True, Begin)
    if FLAG_94:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['94'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_95, SIZE_95, VAL_95, Begin = match('95', True, Begin)
    if FLAG_95:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['95'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_96, SIZE_96, VAL_96, Begin = match('96', True, Begin)
    if FLAG_96:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['96'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_97, SIZE_97, VAL_97, Begin = match('97', True, Begin)
    if FLAG_97:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['97'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_98, SIZE_98, VAL_98, Begin = match('98', True, Begin)
    if FLAG_98:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['98'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_99, SIZE_99, VAL_99, Begin = match('99', True, Begin)
    if FLAG_99:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['99'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_100, SIZE_100, VAL_100, Begin = match('100', True, Begin)
    if FLAG_100:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['100'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_101, SIZE_101, VAL_101, Begin = match('101', True, Begin)
    if FLAG_101:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['101'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_102, SIZE_102, VAL_102, Begin = match('102', True, Begin)
    if FLAG_102:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['102'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_103, SIZE_103, VAL_103, Begin = match('103', True, Begin)
    if FLAG_103:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['103'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_104, SIZE_104, VAL_104, Begin = match('104', True, Begin)
    if FLAG_104:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['104'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_105, SIZE_105, VAL_105, Begin = match('105', True, Begin)
    if FLAG_105:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['105'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_106, SIZE_106, VAL_106, Begin = match('106', True, Begin)
    if FLAG_106:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['106'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_107, SIZE_107, VAL_107, Begin = match('107', True, Begin)
    if FLAG_107:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['107'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_108, SIZE_108, VAL_108, Begin = match('108', True, Begin)
    if FLAG_108:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['108'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_109, SIZE_109, VAL_109, Begin = match('109', True, Begin)
    if FLAG_109:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['109'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_110, SIZE_110, VAL_110, Begin = match('110', True, Begin)
    if FLAG_110:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['110'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_111, SIZE_111, VAL_111, Begin = match('111', True, Begin)
    if FLAG_111:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['111'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_112, SIZE_112, VAL_112, Begin = match('112', True, Begin)
    if FLAG_112:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['112'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_113, SIZE_113, VAL_113, Begin = match('113', True, Begin)
    if FLAG_113:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['113'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_114, SIZE_114, VAL_114, Begin = match('114', True, Begin)
    if FLAG_114:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['114'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_115, SIZE_115, VAL_115, Begin = match('115', True, Begin)
    if FLAG_115:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['115'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_116, SIZE_116, VAL_116, Begin = match('116', True, Begin)
    if FLAG_116:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['116'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_117, SIZE_117, VAL_117, Begin = match('117', True, Begin)
    if FLAG_117:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['117'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_118, SIZE_118, VAL_118, Begin = match('118', True, Begin)
    if FLAG_118:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['118'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_119, SIZE_119, VAL_119, Begin = match('119', True, Begin)
    if FLAG_119:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['119'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_120, SIZE_120, VAL_120, Begin = match('120', True, Begin)
    if FLAG_120:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['120'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_121, SIZE_121, VAL_121, Begin = match('121', True, Begin)
    if FLAG_121:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['121'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_122, SIZE_122, VAL_122, Begin = match('122', True, Begin)
    if FLAG_122:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['122'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_123, SIZE_123, VAL_123, Begin = match('123', True, Begin)
    if FLAG_123:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['123'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_124, SIZE_124, VAL_124, Begin = match('124', True, Begin)
    if FLAG_124:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['124'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_125, SIZE_125, VAL_125, Begin = match('125', True, Begin)
    if FLAG_125:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['125'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_126, SIZE_126, VAL_126, Begin = match('126', True, Begin)
    if FLAG_126:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['126'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    FLAG_127, SIZE_127, VAL_127, Begin = match('127', True, Begin)
    if FLAG_127:
        SIZE_Shortlength = 1
        VAL_Shortlength = hex_n_bytes_to_int_dsl(['127'])
        return True, SIZE_Shortlength, VAL_Shortlength, Begin
    return False, 0, None, Temp


def Longlength(Begin):
    Temp = Begin
    FLAG_Typelonglength, SIZE_Typelonglength, VAL_Typelonglength, Begin = Typelonglength(Begin)
    if FLAG_Typelonglength:
        FLAG_Longlengthvalues, SIZE_Longlengthvalues, VAL_Longlengthvalues, Begin = Longlengthvalues(VAL_Typelonglength,
                                                                                                     Begin)
        if FLAG_Longlengthvalues:
            SIZE_Longlength = SIZE_Typelonglength + SIZE_Longlengthvalues
            VAL_Longlength = VAL_Longlengthvalues
            return True, SIZE_Longlength, VAL_Longlength, Begin
    return False, 0, None, Temp


def Typelonglength(Begin):
    Temp = Begin
    FLAG_128, SIZE_128, VAL_128, Begin = match('128', True, Begin)
    if FLAG_128:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['128']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_129, SIZE_129, VAL_129, Begin = match('129', True, Begin)
    if FLAG_129:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['129']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_130, SIZE_130, VAL_130, Begin = match('130', True, Begin)
    if FLAG_130:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['130']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_131, SIZE_131, VAL_131, Begin = match('131', True, Begin)
    if FLAG_131:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['131']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_132, SIZE_132, VAL_132, Begin = match('132', True, Begin)
    if FLAG_132:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['132']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_133, SIZE_133, VAL_133, Begin = match('133', True, Begin)
    if FLAG_133:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['133']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_134, SIZE_134, VAL_134, Begin = match('134', True, Begin)
    if FLAG_134:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['134']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_135, SIZE_135, VAL_135, Begin = match('135', True, Begin)
    if FLAG_135:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['135']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_136, SIZE_136, VAL_136, Begin = match('136', True, Begin)
    if FLAG_136:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['136']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_137, SIZE_137, VAL_137, Begin = match('137', True, Begin)
    if FLAG_137:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['137']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_138, SIZE_138, VAL_138, Begin = match('138', True, Begin)
    if FLAG_138:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['138']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_139, SIZE_139, VAL_139, Begin = match('139', True, Begin)
    if FLAG_139:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['139']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_140, SIZE_140, VAL_140, Begin = match('140', True, Begin)
    if FLAG_140:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['140']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_141, SIZE_141, VAL_141, Begin = match('141', True, Begin)
    if FLAG_141:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['141']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_142, SIZE_142, VAL_142, Begin = match('142', True, Begin)
    if FLAG_142:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['142']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_143, SIZE_143, VAL_143, Begin = match('143', True, Begin)
    if FLAG_143:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['143']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_144, SIZE_144, VAL_144, Begin = match('144', True, Begin)
    if FLAG_144:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['144']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_145, SIZE_145, VAL_145, Begin = match('145', True, Begin)
    if FLAG_145:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['145']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_146, SIZE_146, VAL_146, Begin = match('146', True, Begin)
    if FLAG_146:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['146']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_147, SIZE_147, VAL_147, Begin = match('147', True, Begin)
    if FLAG_147:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['147']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_148, SIZE_148, VAL_148, Begin = match('148', True, Begin)
    if FLAG_148:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['148']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_149, SIZE_149, VAL_149, Begin = match('149', True, Begin)
    if FLAG_149:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['149']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_150, SIZE_150, VAL_150, Begin = match('150', True, Begin)
    if FLAG_150:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['150']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_151, SIZE_151, VAL_151, Begin = match('151', True, Begin)
    if FLAG_151:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['151']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_152, SIZE_152, VAL_152, Begin = match('152', True, Begin)
    if FLAG_152:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['152']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_153, SIZE_153, VAL_153, Begin = match('153', True, Begin)
    if FLAG_153:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['153']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_154, SIZE_154, VAL_154, Begin = match('154', True, Begin)
    if FLAG_154:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['154']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_155, SIZE_155, VAL_155, Begin = match('155', True, Begin)
    if FLAG_155:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['155']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_156, SIZE_156, VAL_156, Begin = match('156', True, Begin)
    if FLAG_156:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['156']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_157, SIZE_157, VAL_157, Begin = match('157', True, Begin)
    if FLAG_157:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['157']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_158, SIZE_158, VAL_158, Begin = match('158', True, Begin)
    if FLAG_158:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['158']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_159, SIZE_159, VAL_159, Begin = match('159', True, Begin)
    if FLAG_159:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['159']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_160, SIZE_160, VAL_160, Begin = match('160', True, Begin)
    if FLAG_160:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['160']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_161, SIZE_161, VAL_161, Begin = match('161', True, Begin)
    if FLAG_161:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['161']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_162, SIZE_162, VAL_162, Begin = match('162', True, Begin)
    if FLAG_162:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['162']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_163, SIZE_163, VAL_163, Begin = match('163', True, Begin)
    if FLAG_163:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['163']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_164, SIZE_164, VAL_164, Begin = match('164', True, Begin)
    if FLAG_164:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['164']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_165, SIZE_165, VAL_165, Begin = match('165', True, Begin)
    if FLAG_165:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['165']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_166, SIZE_166, VAL_166, Begin = match('166', True, Begin)
    if FLAG_166:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['166']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_167, SIZE_167, VAL_167, Begin = match('167', True, Begin)
    if FLAG_167:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['167']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_168, SIZE_168, VAL_168, Begin = match('168', True, Begin)
    if FLAG_168:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['168']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_169, SIZE_169, VAL_169, Begin = match('169', True, Begin)
    if FLAG_169:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['169']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_170, SIZE_170, VAL_170, Begin = match('170', True, Begin)
    if FLAG_170:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['170']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_171, SIZE_171, VAL_171, Begin = match('171', True, Begin)
    if FLAG_171:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['171']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_172, SIZE_172, VAL_172, Begin = match('172', True, Begin)
    if FLAG_172:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['172']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_173, SIZE_173, VAL_173, Begin = match('173', True, Begin)
    if FLAG_173:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['173']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_174, SIZE_174, VAL_174, Begin = match('174', True, Begin)
    if FLAG_174:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['174']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_175, SIZE_175, VAL_175, Begin = match('175', True, Begin)
    if FLAG_175:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['175']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_176, SIZE_176, VAL_176, Begin = match('176', True, Begin)
    if FLAG_176:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['176']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_177, SIZE_177, VAL_177, Begin = match('177', True, Begin)
    if FLAG_177:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['177']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_178, SIZE_178, VAL_178, Begin = match('178', True, Begin)
    if FLAG_178:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['178']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_179, SIZE_179, VAL_179, Begin = match('179', True, Begin)
    if FLAG_179:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['179']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_180, SIZE_180, VAL_180, Begin = match('180', True, Begin)
    if FLAG_180:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['180']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_181, SIZE_181, VAL_181, Begin = match('181', True, Begin)
    if FLAG_181:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['181']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_182, SIZE_182, VAL_182, Begin = match('182', True, Begin)
    if FLAG_182:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['182']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_183, SIZE_183, VAL_183, Begin = match('183', True, Begin)
    if FLAG_183:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['183']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_184, SIZE_184, VAL_184, Begin = match('184', True, Begin)
    if FLAG_184:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['184']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_185, SIZE_185, VAL_185, Begin = match('185', True, Begin)
    if FLAG_185:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['185']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_186, SIZE_186, VAL_186, Begin = match('186', True, Begin)
    if FLAG_186:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['186']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_187, SIZE_187, VAL_187, Begin = match('187', True, Begin)
    if FLAG_187:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['187']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_188, SIZE_188, VAL_188, Begin = match('188', True, Begin)
    if FLAG_188:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['188']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_189, SIZE_189, VAL_189, Begin = match('189', True, Begin)
    if FLAG_189:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['189']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_190, SIZE_190, VAL_190, Begin = match('190', True, Begin)
    if FLAG_190:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['190']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_191, SIZE_191, VAL_191, Begin = match('191', True, Begin)
    if FLAG_191:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['191']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_192, SIZE_192, VAL_192, Begin = match('192', True, Begin)
    if FLAG_192:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['192']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_193, SIZE_193, VAL_193, Begin = match('193', True, Begin)
    if FLAG_193:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['193']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_194, SIZE_194, VAL_194, Begin = match('194', True, Begin)
    if FLAG_194:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['194']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_195, SIZE_195, VAL_195, Begin = match('195', True, Begin)
    if FLAG_195:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['195']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_196, SIZE_196, VAL_196, Begin = match('196', True, Begin)
    if FLAG_196:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['196']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_197, SIZE_197, VAL_197, Begin = match('197', True, Begin)
    if FLAG_197:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['197']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_198, SIZE_198, VAL_198, Begin = match('198', True, Begin)
    if FLAG_198:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['198']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_199, SIZE_199, VAL_199, Begin = match('199', True, Begin)
    if FLAG_199:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['199']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_200, SIZE_200, VAL_200, Begin = match('200', True, Begin)
    if FLAG_200:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['200']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_201, SIZE_201, VAL_201, Begin = match('201', True, Begin)
    if FLAG_201:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['201']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_202, SIZE_202, VAL_202, Begin = match('202', True, Begin)
    if FLAG_202:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['202']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_203, SIZE_203, VAL_203, Begin = match('203', True, Begin)
    if FLAG_203:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['203']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_204, SIZE_204, VAL_204, Begin = match('204', True, Begin)
    if FLAG_204:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['204']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_205, SIZE_205, VAL_205, Begin = match('205', True, Begin)
    if FLAG_205:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['205']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_206, SIZE_206, VAL_206, Begin = match('206', True, Begin)
    if FLAG_206:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['206']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_207, SIZE_207, VAL_207, Begin = match('207', True, Begin)
    if FLAG_207:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['207']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_208, SIZE_208, VAL_208, Begin = match('208', True, Begin)
    if FLAG_208:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['208']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_209, SIZE_209, VAL_209, Begin = match('209', True, Begin)
    if FLAG_209:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['209']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_210, SIZE_210, VAL_210, Begin = match('210', True, Begin)
    if FLAG_210:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['210']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_211, SIZE_211, VAL_211, Begin = match('211', True, Begin)
    if FLAG_211:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['211']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_212, SIZE_212, VAL_212, Begin = match('212', True, Begin)
    if FLAG_212:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['212']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_213, SIZE_213, VAL_213, Begin = match('213', True, Begin)
    if FLAG_213:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['213']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_214, SIZE_214, VAL_214, Begin = match('214', True, Begin)
    if FLAG_214:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['214']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_215, SIZE_215, VAL_215, Begin = match('215', True, Begin)
    if FLAG_215:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['215']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_216, SIZE_216, VAL_216, Begin = match('216', True, Begin)
    if FLAG_216:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['216']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_217, SIZE_217, VAL_217, Begin = match('217', True, Begin)
    if FLAG_217:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['217']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_218, SIZE_218, VAL_218, Begin = match('218', True, Begin)
    if FLAG_218:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['218']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_219, SIZE_219, VAL_219, Begin = match('219', True, Begin)
    if FLAG_219:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['219']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_220, SIZE_220, VAL_220, Begin = match('220', True, Begin)
    if FLAG_220:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['220']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_221, SIZE_221, VAL_221, Begin = match('221', True, Begin)
    if FLAG_221:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['221']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_222, SIZE_222, VAL_222, Begin = match('222', True, Begin)
    if FLAG_222:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['222']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_223, SIZE_223, VAL_223, Begin = match('223', True, Begin)
    if FLAG_223:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['223']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_224, SIZE_224, VAL_224, Begin = match('224', True, Begin)
    if FLAG_224:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['224']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_225, SIZE_225, VAL_225, Begin = match('225', True, Begin)
    if FLAG_225:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['225']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_226, SIZE_226, VAL_226, Begin = match('226', True, Begin)
    if FLAG_226:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['226']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_227, SIZE_227, VAL_227, Begin = match('227', True, Begin)
    if FLAG_227:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['227']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_228, SIZE_228, VAL_228, Begin = match('228', True, Begin)
    if FLAG_228:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['228']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_229, SIZE_229, VAL_229, Begin = match('229', True, Begin)
    if FLAG_229:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['229']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_230, SIZE_230, VAL_230, Begin = match('230', True, Begin)
    if FLAG_230:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['230']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_231, SIZE_231, VAL_231, Begin = match('231', True, Begin)
    if FLAG_231:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['231']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_232, SIZE_232, VAL_232, Begin = match('232', True, Begin)
    if FLAG_232:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['232']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_233, SIZE_233, VAL_233, Begin = match('233', True, Begin)
    if FLAG_233:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['233']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_234, SIZE_234, VAL_234, Begin = match('234', True, Begin)
    if FLAG_234:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['234']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_235, SIZE_235, VAL_235, Begin = match('235', True, Begin)
    if FLAG_235:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['235']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_236, SIZE_236, VAL_236, Begin = match('236', True, Begin)
    if FLAG_236:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['236']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_237, SIZE_237, VAL_237, Begin = match('237', True, Begin)
    if FLAG_237:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['237']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_238, SIZE_238, VAL_238, Begin = match('238', True, Begin)
    if FLAG_238:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['238']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_239, SIZE_239, VAL_239, Begin = match('239', True, Begin)
    if FLAG_239:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['239']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_240, SIZE_240, VAL_240, Begin = match('240', True, Begin)
    if FLAG_240:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['240']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_241, SIZE_241, VAL_241, Begin = match('241', True, Begin)
    if FLAG_241:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['241']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_242, SIZE_242, VAL_242, Begin = match('242', True, Begin)
    if FLAG_242:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['242']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_243, SIZE_243, VAL_243, Begin = match('243', True, Begin)
    if FLAG_243:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['243']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_244, SIZE_244, VAL_244, Begin = match('244', True, Begin)
    if FLAG_244:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['244']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_245, SIZE_245, VAL_245, Begin = match('245', True, Begin)
    if FLAG_245:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['245']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_246, SIZE_246, VAL_246, Begin = match('246', True, Begin)
    if FLAG_246:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['246']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_247, SIZE_247, VAL_247, Begin = match('247', True, Begin)
    if FLAG_247:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['247']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_248, SIZE_248, VAL_248, Begin = match('248', True, Begin)
    if FLAG_248:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['248']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_249, SIZE_249, VAL_249, Begin = match('249', True, Begin)
    if FLAG_249:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['249']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_250, SIZE_250, VAL_250, Begin = match('250', True, Begin)
    if FLAG_250:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['250']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_251, SIZE_251, VAL_251, Begin = match('251', True, Begin)
    if FLAG_251:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['251']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_252, SIZE_252, VAL_252, Begin = match('252', True, Begin)
    if FLAG_252:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['252']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_253, SIZE_253, VAL_253, Begin = match('253', True, Begin)
    if FLAG_253:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['253']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_254, SIZE_254, VAL_254, Begin = match('254', True, Begin)
    if FLAG_254:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['254']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    FLAG_255, SIZE_255, VAL_255, Begin = match('255', True, Begin)
    if FLAG_255:
        SIZE_Typelonglength = 1
        VAL_Typelonglength = hex_n_bytes_to_int_dsl(['255']) - 128
        return True, SIZE_Typelonglength, VAL_Typelonglength, Begin
    return False, 0, None, Temp


def Longlengthvalues(VAL_Typelonglength, Begin):
    Temp = Begin
    if not (VAL_Typelonglength > 0):
        return True, 0, None, Begin
    FLAG_Bytee, SIZE_Bytee, VAL_Bytee, Begin = Bytee(Begin)
    if FLAG_Bytee:
        FLAG_Longlengthvalues, SIZE_Longlengthvalues, VAL_Longlengthvalues, Begin = Longlengthvalues(
            VAL_Typelonglength - 1, Begin)
        if FLAG_Longlengthvalues:
            SIZE_Longlengthvalues = SIZE_Bytee + SIZE_Longlengthvalues
            VAL_Longlengthvalues = addtotuple_dsl([VAL_Bytee, VAL_Longlengthvalues])
            return True, SIZE_Longlengthvalues, VAL_Longlengthvalues, Begin
    return False, 0, None, Temp


def Bytee(Begin):
    Temp = Begin
    FLAG_0, SIZE_0, VAL_0, Begin = match('0', True, Begin)
    if FLAG_0:
        SIZE_Bytee = 1
        VAL_Bytee = '0'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_1, SIZE_1, VAL_1, Begin = match('1', True, Begin)
    if FLAG_1:
        SIZE_Bytee = 1
        VAL_Bytee = '1'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_2, SIZE_2, VAL_2, Begin = match('2', True, Begin)
    if FLAG_2:
        SIZE_Bytee = 1
        VAL_Bytee = '2'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_3, SIZE_3, VAL_3, Begin = match('3', True, Begin)
    if FLAG_3:
        SIZE_Bytee = 1
        VAL_Bytee = '3'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_4, SIZE_4, VAL_4, Begin = match('4', True, Begin)
    if FLAG_4:
        SIZE_Bytee = 1
        VAL_Bytee = '4'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_5, SIZE_5, VAL_5, Begin = match('5', True, Begin)
    if FLAG_5:
        SIZE_Bytee = 1
        VAL_Bytee = '5'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_6, SIZE_6, VAL_6, Begin = match('6', True, Begin)
    if FLAG_6:
        SIZE_Bytee = 1
        VAL_Bytee = '6'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_7, SIZE_7, VAL_7, Begin = match('7', True, Begin)
    if FLAG_7:
        SIZE_Bytee = 1
        VAL_Bytee = '7'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_8, SIZE_8, VAL_8, Begin = match('8', True, Begin)
    if FLAG_8:
        SIZE_Bytee = 1
        VAL_Bytee = '8'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_9, SIZE_9, VAL_9, Begin = match('9', True, Begin)
    if FLAG_9:
        SIZE_Bytee = 1
        VAL_Bytee = '9'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_10, SIZE_10, VAL_10, Begin = match('10', True, Begin)
    if FLAG_10:
        SIZE_Bytee = 1
        VAL_Bytee = '10'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_11, SIZE_11, VAL_11, Begin = match('11', True, Begin)
    if FLAG_11:
        SIZE_Bytee = 1
        VAL_Bytee = '11'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_12, SIZE_12, VAL_12, Begin = match('12', True, Begin)
    if FLAG_12:
        SIZE_Bytee = 1
        VAL_Bytee = '12'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_13, SIZE_13, VAL_13, Begin = match('13', True, Begin)
    if FLAG_13:
        SIZE_Bytee = 1
        VAL_Bytee = '13'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_14, SIZE_14, VAL_14, Begin = match('14', True, Begin)
    if FLAG_14:
        SIZE_Bytee = 1
        VAL_Bytee = '14'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_15, SIZE_15, VAL_15, Begin = match('15', True, Begin)
    if FLAG_15:
        SIZE_Bytee = 1
        VAL_Bytee = '15'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_16, SIZE_16, VAL_16, Begin = match('16', True, Begin)
    if FLAG_16:
        SIZE_Bytee = 1
        VAL_Bytee = '16'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_17, SIZE_17, VAL_17, Begin = match('17', True, Begin)
    if FLAG_17:
        SIZE_Bytee = 1
        VAL_Bytee = '17'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_18, SIZE_18, VAL_18, Begin = match('18', True, Begin)
    if FLAG_18:
        SIZE_Bytee = 1
        VAL_Bytee = '18'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_19, SIZE_19, VAL_19, Begin = match('19', True, Begin)
    if FLAG_19:
        SIZE_Bytee = 1
        VAL_Bytee = '19'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_20, SIZE_20, VAL_20, Begin = match('20', True, Begin)
    if FLAG_20:
        SIZE_Bytee = 1
        VAL_Bytee = '20'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_21, SIZE_21, VAL_21, Begin = match('21', True, Begin)
    if FLAG_21:
        SIZE_Bytee = 1
        VAL_Bytee = '21'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_22, SIZE_22, VAL_22, Begin = match('22', True, Begin)
    if FLAG_22:
        SIZE_Bytee = 1
        VAL_Bytee = '22'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_23, SIZE_23, VAL_23, Begin = match('23', True, Begin)
    if FLAG_23:
        SIZE_Bytee = 1
        VAL_Bytee = '23'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_24, SIZE_24, VAL_24, Begin = match('24', True, Begin)
    if FLAG_24:
        SIZE_Bytee = 1
        VAL_Bytee = '24'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_25, SIZE_25, VAL_25, Begin = match('25', True, Begin)
    if FLAG_25:
        SIZE_Bytee = 1
        VAL_Bytee = '25'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_26, SIZE_26, VAL_26, Begin = match('26', True, Begin)
    if FLAG_26:
        SIZE_Bytee = 1
        VAL_Bytee = '26'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_27, SIZE_27, VAL_27, Begin = match('27', True, Begin)
    if FLAG_27:
        SIZE_Bytee = 1
        VAL_Bytee = '27'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_28, SIZE_28, VAL_28, Begin = match('28', True, Begin)
    if FLAG_28:
        SIZE_Bytee = 1
        VAL_Bytee = '28'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_29, SIZE_29, VAL_29, Begin = match('29', True, Begin)
    if FLAG_29:
        SIZE_Bytee = 1
        VAL_Bytee = '29'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_30, SIZE_30, VAL_30, Begin = match('30', True, Begin)
    if FLAG_30:
        SIZE_Bytee = 1
        VAL_Bytee = '30'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_31, SIZE_31, VAL_31, Begin = match('31', True, Begin)
    if FLAG_31:
        SIZE_Bytee = 1
        VAL_Bytee = '31'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_32, SIZE_32, VAL_32, Begin = match('32', True, Begin)
    if FLAG_32:
        SIZE_Bytee = 1
        VAL_Bytee = '32'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_33, SIZE_33, VAL_33, Begin = match('33', True, Begin)
    if FLAG_33:
        SIZE_Bytee = 1
        VAL_Bytee = '33'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_34, SIZE_34, VAL_34, Begin = match('34', True, Begin)
    if FLAG_34:
        SIZE_Bytee = 1
        VAL_Bytee = '34'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_35, SIZE_35, VAL_35, Begin = match('35', True, Begin)
    if FLAG_35:
        SIZE_Bytee = 1
        VAL_Bytee = '35'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_36, SIZE_36, VAL_36, Begin = match('36', True, Begin)
    if FLAG_36:
        SIZE_Bytee = 1
        VAL_Bytee = '36'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_37, SIZE_37, VAL_37, Begin = match('37', True, Begin)
    if FLAG_37:
        SIZE_Bytee = 1
        VAL_Bytee = '37'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_38, SIZE_38, VAL_38, Begin = match('38', True, Begin)
    if FLAG_38:
        SIZE_Bytee = 1
        VAL_Bytee = '38'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_39, SIZE_39, VAL_39, Begin = match('39', True, Begin)
    if FLAG_39:
        SIZE_Bytee = 1
        VAL_Bytee = '39'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_40, SIZE_40, VAL_40, Begin = match('40', True, Begin)
    if FLAG_40:
        SIZE_Bytee = 1
        VAL_Bytee = '40'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_41, SIZE_41, VAL_41, Begin = match('41', True, Begin)
    if FLAG_41:
        SIZE_Bytee = 1
        VAL_Bytee = '41'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_42, SIZE_42, VAL_42, Begin = match('42', True, Begin)
    if FLAG_42:
        SIZE_Bytee = 1
        VAL_Bytee = '42'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_43, SIZE_43, VAL_43, Begin = match('43', True, Begin)
    if FLAG_43:
        SIZE_Bytee = 1
        VAL_Bytee = '43'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_44, SIZE_44, VAL_44, Begin = match('44', True, Begin)
    if FLAG_44:
        SIZE_Bytee = 1
        VAL_Bytee = '44'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_45, SIZE_45, VAL_45, Begin = match('45', True, Begin)
    if FLAG_45:
        SIZE_Bytee = 1
        VAL_Bytee = '45'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_46, SIZE_46, VAL_46, Begin = match('46', True, Begin)
    if FLAG_46:
        SIZE_Bytee = 1
        VAL_Bytee = '46'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_47, SIZE_47, VAL_47, Begin = match('47', True, Begin)
    if FLAG_47:
        SIZE_Bytee = 1
        VAL_Bytee = '47'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_48, SIZE_48, VAL_48, Begin = match('48', True, Begin)
    if FLAG_48:
        SIZE_Bytee = 1
        VAL_Bytee = '48'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_49, SIZE_49, VAL_49, Begin = match('49', True, Begin)
    if FLAG_49:
        SIZE_Bytee = 1
        VAL_Bytee = '49'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_50, SIZE_50, VAL_50, Begin = match('50', True, Begin)
    if FLAG_50:
        SIZE_Bytee = 1
        VAL_Bytee = '50'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_51, SIZE_51, VAL_51, Begin = match('51', True, Begin)
    if FLAG_51:
        SIZE_Bytee = 1
        VAL_Bytee = '51'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_52, SIZE_52, VAL_52, Begin = match('52', True, Begin)
    if FLAG_52:
        SIZE_Bytee = 1
        VAL_Bytee = '52'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_53, SIZE_53, VAL_53, Begin = match('53', True, Begin)
    if FLAG_53:
        SIZE_Bytee = 1
        VAL_Bytee = '53'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_54, SIZE_54, VAL_54, Begin = match('54', True, Begin)
    if FLAG_54:
        SIZE_Bytee = 1
        VAL_Bytee = '54'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_55, SIZE_55, VAL_55, Begin = match('55', True, Begin)
    if FLAG_55:
        SIZE_Bytee = 1
        VAL_Bytee = '55'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_56, SIZE_56, VAL_56, Begin = match('56', True, Begin)
    if FLAG_56:
        SIZE_Bytee = 1
        VAL_Bytee = '56'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_57, SIZE_57, VAL_57, Begin = match('57', True, Begin)
    if FLAG_57:
        SIZE_Bytee = 1
        VAL_Bytee = '57'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_58, SIZE_58, VAL_58, Begin = match('58', True, Begin)
    if FLAG_58:
        SIZE_Bytee = 1
        VAL_Bytee = '58'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_59, SIZE_59, VAL_59, Begin = match('59', True, Begin)
    if FLAG_59:
        SIZE_Bytee = 1
        VAL_Bytee = '59'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_60, SIZE_60, VAL_60, Begin = match('60', True, Begin)
    if FLAG_60:
        SIZE_Bytee = 1
        VAL_Bytee = '60'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_61, SIZE_61, VAL_61, Begin = match('61', True, Begin)
    if FLAG_61:
        SIZE_Bytee = 1
        VAL_Bytee = '61'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_62, SIZE_62, VAL_62, Begin = match('62', True, Begin)
    if FLAG_62:
        SIZE_Bytee = 1
        VAL_Bytee = '62'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_63, SIZE_63, VAL_63, Begin = match('63', True, Begin)
    if FLAG_63:
        SIZE_Bytee = 1
        VAL_Bytee = '63'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_64, SIZE_64, VAL_64, Begin = match('64', True, Begin)
    if FLAG_64:
        SIZE_Bytee = 1
        VAL_Bytee = '64'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_65, SIZE_65, VAL_65, Begin = match('65', True, Begin)
    if FLAG_65:
        SIZE_Bytee = 1
        VAL_Bytee = '65'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_66, SIZE_66, VAL_66, Begin = match('66', True, Begin)
    if FLAG_66:
        SIZE_Bytee = 1
        VAL_Bytee = '66'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_67, SIZE_67, VAL_67, Begin = match('67', True, Begin)
    if FLAG_67:
        SIZE_Bytee = 1
        VAL_Bytee = '67'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_68, SIZE_68, VAL_68, Begin = match('68', True, Begin)
    if FLAG_68:
        SIZE_Bytee = 1
        VAL_Bytee = '68'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_69, SIZE_69, VAL_69, Begin = match('69', True, Begin)
    if FLAG_69:
        SIZE_Bytee = 1
        VAL_Bytee = '69'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_70, SIZE_70, VAL_70, Begin = match('70', True, Begin)
    if FLAG_70:
        SIZE_Bytee = 1
        VAL_Bytee = '70'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_71, SIZE_71, VAL_71, Begin = match('71', True, Begin)
    if FLAG_71:
        SIZE_Bytee = 1
        VAL_Bytee = '71'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_72, SIZE_72, VAL_72, Begin = match('72', True, Begin)
    if FLAG_72:
        SIZE_Bytee = 1
        VAL_Bytee = '72'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_73, SIZE_73, VAL_73, Begin = match('73', True, Begin)
    if FLAG_73:
        SIZE_Bytee = 1
        VAL_Bytee = '73'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_74, SIZE_74, VAL_74, Begin = match('74', True, Begin)
    if FLAG_74:
        SIZE_Bytee = 1
        VAL_Bytee = '74'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_75, SIZE_75, VAL_75, Begin = match('75', True, Begin)
    if FLAG_75:
        SIZE_Bytee = 1
        VAL_Bytee = '75'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_76, SIZE_76, VAL_76, Begin = match('76', True, Begin)
    if FLAG_76:
        SIZE_Bytee = 1
        VAL_Bytee = '76'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_77, SIZE_77, VAL_77, Begin = match('77', True, Begin)
    if FLAG_77:
        SIZE_Bytee = 1
        VAL_Bytee = '77'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_78, SIZE_78, VAL_78, Begin = match('78', True, Begin)
    if FLAG_78:
        SIZE_Bytee = 1
        VAL_Bytee = '78'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_79, SIZE_79, VAL_79, Begin = match('79', True, Begin)
    if FLAG_79:
        SIZE_Bytee = 1
        VAL_Bytee = '79'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_80, SIZE_80, VAL_80, Begin = match('80', True, Begin)
    if FLAG_80:
        SIZE_Bytee = 1
        VAL_Bytee = '80'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_81, SIZE_81, VAL_81, Begin = match('81', True, Begin)
    if FLAG_81:
        SIZE_Bytee = 1
        VAL_Bytee = '81'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_82, SIZE_82, VAL_82, Begin = match('82', True, Begin)
    if FLAG_82:
        SIZE_Bytee = 1
        VAL_Bytee = '82'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_83, SIZE_83, VAL_83, Begin = match('83', True, Begin)
    if FLAG_83:
        SIZE_Bytee = 1
        VAL_Bytee = '83'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_84, SIZE_84, VAL_84, Begin = match('84', True, Begin)
    if FLAG_84:
        SIZE_Bytee = 1
        VAL_Bytee = '84'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_85, SIZE_85, VAL_85, Begin = match('85', True, Begin)
    if FLAG_85:
        SIZE_Bytee = 1
        VAL_Bytee = '85'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_86, SIZE_86, VAL_86, Begin = match('86', True, Begin)
    if FLAG_86:
        SIZE_Bytee = 1
        VAL_Bytee = '86'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_87, SIZE_87, VAL_87, Begin = match('87', True, Begin)
    if FLAG_87:
        SIZE_Bytee = 1
        VAL_Bytee = '87'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_88, SIZE_88, VAL_88, Begin = match('88', True, Begin)
    if FLAG_88:
        SIZE_Bytee = 1
        VAL_Bytee = '88'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_89, SIZE_89, VAL_89, Begin = match('89', True, Begin)
    if FLAG_89:
        SIZE_Bytee = 1
        VAL_Bytee = '89'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_90, SIZE_90, VAL_90, Begin = match('90', True, Begin)
    if FLAG_90:
        SIZE_Bytee = 1
        VAL_Bytee = '90'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_91, SIZE_91, VAL_91, Begin = match('91', True, Begin)
    if FLAG_91:
        SIZE_Bytee = 1
        VAL_Bytee = '91'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_92, SIZE_92, VAL_92, Begin = match('92', True, Begin)
    if FLAG_92:
        SIZE_Bytee = 1
        VAL_Bytee = '92'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_93, SIZE_93, VAL_93, Begin = match('93', True, Begin)
    if FLAG_93:
        SIZE_Bytee = 1
        VAL_Bytee = '93'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_94, SIZE_94, VAL_94, Begin = match('94', True, Begin)
    if FLAG_94:
        SIZE_Bytee = 1
        VAL_Bytee = '94'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_95, SIZE_95, VAL_95, Begin = match('95', True, Begin)
    if FLAG_95:
        SIZE_Bytee = 1
        VAL_Bytee = '95'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_96, SIZE_96, VAL_96, Begin = match('96', True, Begin)
    if FLAG_96:
        SIZE_Bytee = 1
        VAL_Bytee = '96'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_97, SIZE_97, VAL_97, Begin = match('97', True, Begin)
    if FLAG_97:
        SIZE_Bytee = 1
        VAL_Bytee = '97'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_98, SIZE_98, VAL_98, Begin = match('98', True, Begin)
    if FLAG_98:
        SIZE_Bytee = 1
        VAL_Bytee = '98'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_99, SIZE_99, VAL_99, Begin = match('99', True, Begin)
    if FLAG_99:
        SIZE_Bytee = 1
        VAL_Bytee = '99'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_100, SIZE_100, VAL_100, Begin = match('100', True, Begin)
    if FLAG_100:
        SIZE_Bytee = 1
        VAL_Bytee = '100'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_101, SIZE_101, VAL_101, Begin = match('101', True, Begin)
    if FLAG_101:
        SIZE_Bytee = 1
        VAL_Bytee = '101'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_102, SIZE_102, VAL_102, Begin = match('102', True, Begin)
    if FLAG_102:
        SIZE_Bytee = 1
        VAL_Bytee = '102'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_103, SIZE_103, VAL_103, Begin = match('103', True, Begin)
    if FLAG_103:
        SIZE_Bytee = 1
        VAL_Bytee = '103'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_104, SIZE_104, VAL_104, Begin = match('104', True, Begin)
    if FLAG_104:
        SIZE_Bytee = 1
        VAL_Bytee = '104'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_105, SIZE_105, VAL_105, Begin = match('105', True, Begin)
    if FLAG_105:
        SIZE_Bytee = 1
        VAL_Bytee = '105'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_106, SIZE_106, VAL_106, Begin = match('106', True, Begin)
    if FLAG_106:
        SIZE_Bytee = 1
        VAL_Bytee = '106'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_107, SIZE_107, VAL_107, Begin = match('107', True, Begin)
    if FLAG_107:
        SIZE_Bytee = 1
        VAL_Bytee = '107'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_108, SIZE_108, VAL_108, Begin = match('108', True, Begin)
    if FLAG_108:
        SIZE_Bytee = 1
        VAL_Bytee = '108'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_109, SIZE_109, VAL_109, Begin = match('109', True, Begin)
    if FLAG_109:
        SIZE_Bytee = 1
        VAL_Bytee = '109'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_110, SIZE_110, VAL_110, Begin = match('110', True, Begin)
    if FLAG_110:
        SIZE_Bytee = 1
        VAL_Bytee = '110'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_111, SIZE_111, VAL_111, Begin = match('111', True, Begin)
    if FLAG_111:
        SIZE_Bytee = 1
        VAL_Bytee = '111'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_112, SIZE_112, VAL_112, Begin = match('112', True, Begin)
    if FLAG_112:
        SIZE_Bytee = 1
        VAL_Bytee = '112'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_113, SIZE_113, VAL_113, Begin = match('113', True, Begin)
    if FLAG_113:
        SIZE_Bytee = 1
        VAL_Bytee = '113'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_114, SIZE_114, VAL_114, Begin = match('114', True, Begin)
    if FLAG_114:
        SIZE_Bytee = 1
        VAL_Bytee = '114'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_115, SIZE_115, VAL_115, Begin = match('115', True, Begin)
    if FLAG_115:
        SIZE_Bytee = 1
        VAL_Bytee = '115'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_116, SIZE_116, VAL_116, Begin = match('116', True, Begin)
    if FLAG_116:
        SIZE_Bytee = 1
        VAL_Bytee = '116'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_117, SIZE_117, VAL_117, Begin = match('117', True, Begin)
    if FLAG_117:
        SIZE_Bytee = 1
        VAL_Bytee = '117'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_118, SIZE_118, VAL_118, Begin = match('118', True, Begin)
    if FLAG_118:
        SIZE_Bytee = 1
        VAL_Bytee = '118'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_119, SIZE_119, VAL_119, Begin = match('119', True, Begin)
    if FLAG_119:
        SIZE_Bytee = 1
        VAL_Bytee = '119'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_120, SIZE_120, VAL_120, Begin = match('120', True, Begin)
    if FLAG_120:
        SIZE_Bytee = 1
        VAL_Bytee = '120'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_121, SIZE_121, VAL_121, Begin = match('121', True, Begin)
    if FLAG_121:
        SIZE_Bytee = 1
        VAL_Bytee = '121'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_122, SIZE_122, VAL_122, Begin = match('122', True, Begin)
    if FLAG_122:
        SIZE_Bytee = 1
        VAL_Bytee = '122'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_123, SIZE_123, VAL_123, Begin = match('123', True, Begin)
    if FLAG_123:
        SIZE_Bytee = 1
        VAL_Bytee = '123'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_124, SIZE_124, VAL_124, Begin = match('124', True, Begin)
    if FLAG_124:
        SIZE_Bytee = 1
        VAL_Bytee = '124'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_125, SIZE_125, VAL_125, Begin = match('125', True, Begin)
    if FLAG_125:
        SIZE_Bytee = 1
        VAL_Bytee = '125'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_126, SIZE_126, VAL_126, Begin = match('126', True, Begin)
    if FLAG_126:
        SIZE_Bytee = 1
        VAL_Bytee = '126'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_127, SIZE_127, VAL_127, Begin = match('127', True, Begin)
    if FLAG_127:
        SIZE_Bytee = 1
        VAL_Bytee = '127'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_128, SIZE_128, VAL_128, Begin = match('128', True, Begin)
    if FLAG_128:
        SIZE_Bytee = 1
        VAL_Bytee = '128'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_129, SIZE_129, VAL_129, Begin = match('129', True, Begin)
    if FLAG_129:
        SIZE_Bytee = 1
        VAL_Bytee = '129'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_130, SIZE_130, VAL_130, Begin = match('130', True, Begin)
    if FLAG_130:
        SIZE_Bytee = 1
        VAL_Bytee = '130'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_131, SIZE_131, VAL_131, Begin = match('131', True, Begin)
    if FLAG_131:
        SIZE_Bytee = 1
        VAL_Bytee = '131'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_132, SIZE_132, VAL_132, Begin = match('132', True, Begin)
    if FLAG_132:
        SIZE_Bytee = 1
        VAL_Bytee = '132'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_133, SIZE_133, VAL_133, Begin = match('133', True, Begin)
    if FLAG_133:
        SIZE_Bytee = 1
        VAL_Bytee = '133'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_134, SIZE_134, VAL_134, Begin = match('134', True, Begin)
    if FLAG_134:
        SIZE_Bytee = 1
        VAL_Bytee = '134'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_135, SIZE_135, VAL_135, Begin = match('135', True, Begin)
    if FLAG_135:
        SIZE_Bytee = 1
        VAL_Bytee = '135'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_136, SIZE_136, VAL_136, Begin = match('136', True, Begin)
    if FLAG_136:
        SIZE_Bytee = 1
        VAL_Bytee = '136'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_137, SIZE_137, VAL_137, Begin = match('137', True, Begin)
    if FLAG_137:
        SIZE_Bytee = 1
        VAL_Bytee = '137'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_138, SIZE_138, VAL_138, Begin = match('138', True, Begin)
    if FLAG_138:
        SIZE_Bytee = 1
        VAL_Bytee = '138'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_139, SIZE_139, VAL_139, Begin = match('139', True, Begin)
    if FLAG_139:
        SIZE_Bytee = 1
        VAL_Bytee = '139'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_140, SIZE_140, VAL_140, Begin = match('140', True, Begin)
    if FLAG_140:
        SIZE_Bytee = 1
        VAL_Bytee = '140'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_141, SIZE_141, VAL_141, Begin = match('141', True, Begin)
    if FLAG_141:
        SIZE_Bytee = 1
        VAL_Bytee = '141'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_142, SIZE_142, VAL_142, Begin = match('142', True, Begin)
    if FLAG_142:
        SIZE_Bytee = 1
        VAL_Bytee = '142'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_143, SIZE_143, VAL_143, Begin = match('143', True, Begin)
    if FLAG_143:
        SIZE_Bytee = 1
        VAL_Bytee = '143'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_144, SIZE_144, VAL_144, Begin = match('144', True, Begin)
    if FLAG_144:
        SIZE_Bytee = 1
        VAL_Bytee = '144'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_145, SIZE_145, VAL_145, Begin = match('145', True, Begin)
    if FLAG_145:
        SIZE_Bytee = 1
        VAL_Bytee = '145'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_146, SIZE_146, VAL_146, Begin = match('146', True, Begin)
    if FLAG_146:
        SIZE_Bytee = 1
        VAL_Bytee = '146'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_147, SIZE_147, VAL_147, Begin = match('147', True, Begin)
    if FLAG_147:
        SIZE_Bytee = 1
        VAL_Bytee = '147'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_148, SIZE_148, VAL_148, Begin = match('148', True, Begin)
    if FLAG_148:
        SIZE_Bytee = 1
        VAL_Bytee = '148'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_149, SIZE_149, VAL_149, Begin = match('149', True, Begin)
    if FLAG_149:
        SIZE_Bytee = 1
        VAL_Bytee = '149'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_150, SIZE_150, VAL_150, Begin = match('150', True, Begin)
    if FLAG_150:
        SIZE_Bytee = 1
        VAL_Bytee = '150'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_151, SIZE_151, VAL_151, Begin = match('151', True, Begin)
    if FLAG_151:
        SIZE_Bytee = 1
        VAL_Bytee = '151'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_152, SIZE_152, VAL_152, Begin = match('152', True, Begin)
    if FLAG_152:
        SIZE_Bytee = 1
        VAL_Bytee = '152'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_153, SIZE_153, VAL_153, Begin = match('153', True, Begin)
    if FLAG_153:
        SIZE_Bytee = 1
        VAL_Bytee = '153'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_154, SIZE_154, VAL_154, Begin = match('154', True, Begin)
    if FLAG_154:
        SIZE_Bytee = 1
        VAL_Bytee = '154'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_155, SIZE_155, VAL_155, Begin = match('155', True, Begin)
    if FLAG_155:
        SIZE_Bytee = 1
        VAL_Bytee = '155'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_156, SIZE_156, VAL_156, Begin = match('156', True, Begin)
    if FLAG_156:
        SIZE_Bytee = 1
        VAL_Bytee = '156'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_157, SIZE_157, VAL_157, Begin = match('157', True, Begin)
    if FLAG_157:
        SIZE_Bytee = 1
        VAL_Bytee = '157'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_158, SIZE_158, VAL_158, Begin = match('158', True, Begin)
    if FLAG_158:
        SIZE_Bytee = 1
        VAL_Bytee = '158'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_159, SIZE_159, VAL_159, Begin = match('159', True, Begin)
    if FLAG_159:
        SIZE_Bytee = 1
        VAL_Bytee = '159'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_160, SIZE_160, VAL_160, Begin = match('160', True, Begin)
    if FLAG_160:
        SIZE_Bytee = 1
        VAL_Bytee = '160'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_161, SIZE_161, VAL_161, Begin = match('161', True, Begin)
    if FLAG_161:
        SIZE_Bytee = 1
        VAL_Bytee = '161'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_162, SIZE_162, VAL_162, Begin = match('162', True, Begin)
    if FLAG_162:
        SIZE_Bytee = 1
        VAL_Bytee = '162'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_163, SIZE_163, VAL_163, Begin = match('163', True, Begin)
    if FLAG_163:
        SIZE_Bytee = 1
        VAL_Bytee = '163'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_164, SIZE_164, VAL_164, Begin = match('164', True, Begin)
    if FLAG_164:
        SIZE_Bytee = 1
        VAL_Bytee = '164'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_165, SIZE_165, VAL_165, Begin = match('165', True, Begin)
    if FLAG_165:
        SIZE_Bytee = 1
        VAL_Bytee = '165'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_166, SIZE_166, VAL_166, Begin = match('166', True, Begin)
    if FLAG_166:
        SIZE_Bytee = 1
        VAL_Bytee = '166'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_167, SIZE_167, VAL_167, Begin = match('167', True, Begin)
    if FLAG_167:
        SIZE_Bytee = 1
        VAL_Bytee = '167'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_168, SIZE_168, VAL_168, Begin = match('168', True, Begin)
    if FLAG_168:
        SIZE_Bytee = 1
        VAL_Bytee = '168'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_169, SIZE_169, VAL_169, Begin = match('169', True, Begin)
    if FLAG_169:
        SIZE_Bytee = 1
        VAL_Bytee = '169'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_170, SIZE_170, VAL_170, Begin = match('170', True, Begin)
    if FLAG_170:
        SIZE_Bytee = 1
        VAL_Bytee = '170'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_171, SIZE_171, VAL_171, Begin = match('171', True, Begin)
    if FLAG_171:
        SIZE_Bytee = 1
        VAL_Bytee = '171'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_172, SIZE_172, VAL_172, Begin = match('172', True, Begin)
    if FLAG_172:
        SIZE_Bytee = 1
        VAL_Bytee = '172'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_173, SIZE_173, VAL_173, Begin = match('173', True, Begin)
    if FLAG_173:
        SIZE_Bytee = 1
        VAL_Bytee = '173'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_174, SIZE_174, VAL_174, Begin = match('174', True, Begin)
    if FLAG_174:
        SIZE_Bytee = 1
        VAL_Bytee = '174'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_175, SIZE_175, VAL_175, Begin = match('175', True, Begin)
    if FLAG_175:
        SIZE_Bytee = 1
        VAL_Bytee = '175'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_176, SIZE_176, VAL_176, Begin = match('176', True, Begin)
    if FLAG_176:
        SIZE_Bytee = 1
        VAL_Bytee = '176'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_177, SIZE_177, VAL_177, Begin = match('177', True, Begin)
    if FLAG_177:
        SIZE_Bytee = 1
        VAL_Bytee = '177'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_178, SIZE_178, VAL_178, Begin = match('178', True, Begin)
    if FLAG_178:
        SIZE_Bytee = 1
        VAL_Bytee = '178'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_179, SIZE_179, VAL_179, Begin = match('179', True, Begin)
    if FLAG_179:
        SIZE_Bytee = 1
        VAL_Bytee = '179'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_180, SIZE_180, VAL_180, Begin = match('180', True, Begin)
    if FLAG_180:
        SIZE_Bytee = 1
        VAL_Bytee = '180'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_181, SIZE_181, VAL_181, Begin = match('181', True, Begin)
    if FLAG_181:
        SIZE_Bytee = 1
        VAL_Bytee = '181'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_182, SIZE_182, VAL_182, Begin = match('182', True, Begin)
    if FLAG_182:
        SIZE_Bytee = 1
        VAL_Bytee = '182'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_183, SIZE_183, VAL_183, Begin = match('183', True, Begin)
    if FLAG_183:
        SIZE_Bytee = 1
        VAL_Bytee = '183'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_184, SIZE_184, VAL_184, Begin = match('184', True, Begin)
    if FLAG_184:
        SIZE_Bytee = 1
        VAL_Bytee = '184'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_185, SIZE_185, VAL_185, Begin = match('185', True, Begin)
    if FLAG_185:
        SIZE_Bytee = 1
        VAL_Bytee = '185'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_186, SIZE_186, VAL_186, Begin = match('186', True, Begin)
    if FLAG_186:
        SIZE_Bytee = 1
        VAL_Bytee = '186'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_187, SIZE_187, VAL_187, Begin = match('187', True, Begin)
    if FLAG_187:
        SIZE_Bytee = 1
        VAL_Bytee = '187'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_188, SIZE_188, VAL_188, Begin = match('188', True, Begin)
    if FLAG_188:
        SIZE_Bytee = 1
        VAL_Bytee = '188'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_189, SIZE_189, VAL_189, Begin = match('189', True, Begin)
    if FLAG_189:
        SIZE_Bytee = 1
        VAL_Bytee = '189'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_190, SIZE_190, VAL_190, Begin = match('190', True, Begin)
    if FLAG_190:
        SIZE_Bytee = 1
        VAL_Bytee = '190'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_191, SIZE_191, VAL_191, Begin = match('191', True, Begin)
    if FLAG_191:
        SIZE_Bytee = 1
        VAL_Bytee = '191'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_192, SIZE_192, VAL_192, Begin = match('192', True, Begin)
    if FLAG_192:
        SIZE_Bytee = 1
        VAL_Bytee = '192'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_193, SIZE_193, VAL_193, Begin = match('193', True, Begin)
    if FLAG_193:
        SIZE_Bytee = 1
        VAL_Bytee = '193'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_194, SIZE_194, VAL_194, Begin = match('194', True, Begin)
    if FLAG_194:
        SIZE_Bytee = 1
        VAL_Bytee = '194'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_195, SIZE_195, VAL_195, Begin = match('195', True, Begin)
    if FLAG_195:
        SIZE_Bytee = 1
        VAL_Bytee = '195'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_196, SIZE_196, VAL_196, Begin = match('196', True, Begin)
    if FLAG_196:
        SIZE_Bytee = 1
        VAL_Bytee = '196'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_197, SIZE_197, VAL_197, Begin = match('197', True, Begin)
    if FLAG_197:
        SIZE_Bytee = 1
        VAL_Bytee = '197'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_198, SIZE_198, VAL_198, Begin = match('198', True, Begin)
    if FLAG_198:
        SIZE_Bytee = 1
        VAL_Bytee = '198'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_199, SIZE_199, VAL_199, Begin = match('199', True, Begin)
    if FLAG_199:
        SIZE_Bytee = 1
        VAL_Bytee = '199'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_200, SIZE_200, VAL_200, Begin = match('200', True, Begin)
    if FLAG_200:
        SIZE_Bytee = 1
        VAL_Bytee = '200'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_201, SIZE_201, VAL_201, Begin = match('201', True, Begin)
    if FLAG_201:
        SIZE_Bytee = 1
        VAL_Bytee = '201'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_202, SIZE_202, VAL_202, Begin = match('202', True, Begin)
    if FLAG_202:
        SIZE_Bytee = 1
        VAL_Bytee = '202'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_203, SIZE_203, VAL_203, Begin = match('203', True, Begin)
    if FLAG_203:
        SIZE_Bytee = 1
        VAL_Bytee = '203'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_204, SIZE_204, VAL_204, Begin = match('204', True, Begin)
    if FLAG_204:
        SIZE_Bytee = 1
        VAL_Bytee = '204'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_205, SIZE_205, VAL_205, Begin = match('205', True, Begin)
    if FLAG_205:
        SIZE_Bytee = 1
        VAL_Bytee = '205'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_206, SIZE_206, VAL_206, Begin = match('206', True, Begin)
    if FLAG_206:
        SIZE_Bytee = 1
        VAL_Bytee = '206'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_207, SIZE_207, VAL_207, Begin = match('207', True, Begin)
    if FLAG_207:
        SIZE_Bytee = 1
        VAL_Bytee = '207'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_208, SIZE_208, VAL_208, Begin = match('208', True, Begin)
    if FLAG_208:
        SIZE_Bytee = 1
        VAL_Bytee = '208'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_209, SIZE_209, VAL_209, Begin = match('209', True, Begin)
    if FLAG_209:
        SIZE_Bytee = 1
        VAL_Bytee = '209'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_210, SIZE_210, VAL_210, Begin = match('210', True, Begin)
    if FLAG_210:
        SIZE_Bytee = 1
        VAL_Bytee = '210'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_211, SIZE_211, VAL_211, Begin = match('211', True, Begin)
    if FLAG_211:
        SIZE_Bytee = 1
        VAL_Bytee = '211'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_212, SIZE_212, VAL_212, Begin = match('212', True, Begin)
    if FLAG_212:
        SIZE_Bytee = 1
        VAL_Bytee = '212'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_213, SIZE_213, VAL_213, Begin = match('213', True, Begin)
    if FLAG_213:
        SIZE_Bytee = 1
        VAL_Bytee = '213'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_214, SIZE_214, VAL_214, Begin = match('214', True, Begin)
    if FLAG_214:
        SIZE_Bytee = 1
        VAL_Bytee = '214'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_215, SIZE_215, VAL_215, Begin = match('215', True, Begin)
    if FLAG_215:
        SIZE_Bytee = 1
        VAL_Bytee = '215'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_216, SIZE_216, VAL_216, Begin = match('216', True, Begin)
    if FLAG_216:
        SIZE_Bytee = 1
        VAL_Bytee = '216'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_217, SIZE_217, VAL_217, Begin = match('217', True, Begin)
    if FLAG_217:
        SIZE_Bytee = 1
        VAL_Bytee = '217'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_218, SIZE_218, VAL_218, Begin = match('218', True, Begin)
    if FLAG_218:
        SIZE_Bytee = 1
        VAL_Bytee = '218'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_219, SIZE_219, VAL_219, Begin = match('219', True, Begin)
    if FLAG_219:
        SIZE_Bytee = 1
        VAL_Bytee = '219'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_220, SIZE_220, VAL_220, Begin = match('220', True, Begin)
    if FLAG_220:
        SIZE_Bytee = 1
        VAL_Bytee = '220'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_221, SIZE_221, VAL_221, Begin = match('221', True, Begin)
    if FLAG_221:
        SIZE_Bytee = 1
        VAL_Bytee = '221'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_222, SIZE_222, VAL_222, Begin = match('222', True, Begin)
    if FLAG_222:
        SIZE_Bytee = 1
        VAL_Bytee = '222'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_223, SIZE_223, VAL_223, Begin = match('223', True, Begin)
    if FLAG_223:
        SIZE_Bytee = 1
        VAL_Bytee = '223'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_224, SIZE_224, VAL_224, Begin = match('224', True, Begin)
    if FLAG_224:
        SIZE_Bytee = 1
        VAL_Bytee = '224'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_225, SIZE_225, VAL_225, Begin = match('225', True, Begin)
    if FLAG_225:
        SIZE_Bytee = 1
        VAL_Bytee = '225'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_226, SIZE_226, VAL_226, Begin = match('226', True, Begin)
    if FLAG_226:
        SIZE_Bytee = 1
        VAL_Bytee = '226'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_227, SIZE_227, VAL_227, Begin = match('227', True, Begin)
    if FLAG_227:
        SIZE_Bytee = 1
        VAL_Bytee = '227'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_228, SIZE_228, VAL_228, Begin = match('228', True, Begin)
    if FLAG_228:
        SIZE_Bytee = 1
        VAL_Bytee = '228'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_229, SIZE_229, VAL_229, Begin = match('229', True, Begin)
    if FLAG_229:
        SIZE_Bytee = 1
        VAL_Bytee = '229'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_230, SIZE_230, VAL_230, Begin = match('230', True, Begin)
    if FLAG_230:
        SIZE_Bytee = 1
        VAL_Bytee = '230'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_231, SIZE_231, VAL_231, Begin = match('231', True, Begin)
    if FLAG_231:
        SIZE_Bytee = 1
        VAL_Bytee = '231'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_232, SIZE_232, VAL_232, Begin = match('232', True, Begin)
    if FLAG_232:
        SIZE_Bytee = 1
        VAL_Bytee = '232'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_233, SIZE_233, VAL_233, Begin = match('233', True, Begin)
    if FLAG_233:
        SIZE_Bytee = 1
        VAL_Bytee = '233'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_234, SIZE_234, VAL_234, Begin = match('234', True, Begin)
    if FLAG_234:
        SIZE_Bytee = 1
        VAL_Bytee = '234'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_235, SIZE_235, VAL_235, Begin = match('235', True, Begin)
    if FLAG_235:
        SIZE_Bytee = 1
        VAL_Bytee = '235'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_236, SIZE_236, VAL_236, Begin = match('236', True, Begin)
    if FLAG_236:
        SIZE_Bytee = 1
        VAL_Bytee = '236'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_237, SIZE_237, VAL_237, Begin = match('237', True, Begin)
    if FLAG_237:
        SIZE_Bytee = 1
        VAL_Bytee = '237'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_238, SIZE_238, VAL_238, Begin = match('238', True, Begin)
    if FLAG_238:
        SIZE_Bytee = 1
        VAL_Bytee = '238'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_239, SIZE_239, VAL_239, Begin = match('239', True, Begin)
    if FLAG_239:
        SIZE_Bytee = 1
        VAL_Bytee = '239'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_240, SIZE_240, VAL_240, Begin = match('240', True, Begin)
    if FLAG_240:
        SIZE_Bytee = 1
        VAL_Bytee = '240'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_241, SIZE_241, VAL_241, Begin = match('241', True, Begin)
    if FLAG_241:
        SIZE_Bytee = 1
        VAL_Bytee = '241'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_242, SIZE_242, VAL_242, Begin = match('242', True, Begin)
    if FLAG_242:
        SIZE_Bytee = 1
        VAL_Bytee = '242'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_243, SIZE_243, VAL_243, Begin = match('243', True, Begin)
    if FLAG_243:
        SIZE_Bytee = 1
        VAL_Bytee = '243'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_244, SIZE_244, VAL_244, Begin = match('244', True, Begin)
    if FLAG_244:
        SIZE_Bytee = 1
        VAL_Bytee = '244'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_245, SIZE_245, VAL_245, Begin = match('245', True, Begin)
    if FLAG_245:
        SIZE_Bytee = 1
        VAL_Bytee = '245'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_246, SIZE_246, VAL_246, Begin = match('246', True, Begin)
    if FLAG_246:
        SIZE_Bytee = 1
        VAL_Bytee = '246'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_247, SIZE_247, VAL_247, Begin = match('247', True, Begin)
    if FLAG_247:
        SIZE_Bytee = 1
        VAL_Bytee = '247'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_248, SIZE_248, VAL_248, Begin = match('248', True, Begin)
    if FLAG_248:
        SIZE_Bytee = 1
        VAL_Bytee = '248'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_249, SIZE_249, VAL_249, Begin = match('249', True, Begin)
    if FLAG_249:
        SIZE_Bytee = 1
        VAL_Bytee = '249'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_250, SIZE_250, VAL_250, Begin = match('250', True, Begin)
    if FLAG_250:
        SIZE_Bytee = 1
        VAL_Bytee = '250'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_251, SIZE_251, VAL_251, Begin = match('251', True, Begin)
    if FLAG_251:
        SIZE_Bytee = 1
        VAL_Bytee = '251'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_252, SIZE_252, VAL_252, Begin = match('252', True, Begin)
    if FLAG_252:
        SIZE_Bytee = 1
        VAL_Bytee = '252'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_253, SIZE_253, VAL_253, Begin = match('253', True, Begin)
    if FLAG_253:
        SIZE_Bytee = 1
        VAL_Bytee = '253'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_254, SIZE_254, VAL_254, Begin = match('254', True, Begin)
    if FLAG_254:
        SIZE_Bytee = 1
        VAL_Bytee = '254'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    FLAG_255, SIZE_255, VAL_255, Begin = match('255', True, Begin)
    if FLAG_255:
        SIZE_Bytee = 1
        VAL_Bytee = '255'
        return True, SIZE_Bytee, VAL_Bytee, Begin
    return False, 0, None, Temp


def Value(VAL_Length, Begin):
    Temp = Begin
    if not (VAL_Length > 0):
        return True, 0, None, Begin
    FLAG_Bytee, SIZE_Bytee, VAL_Bytee, Begin = Bytee(Begin)
    if FLAG_Bytee:
        FLAG_Value, SIZE_Value, VAL_Value, Begin = Value(VAL_Length - 1, Begin)
        if FLAG_Value:
            SIZE_Value = SIZE_Bytee + SIZE_Value
            VAL_Value = addtotuple_dsl([VAL_Bytee, VAL_Value])
            return True, SIZE_Value, VAL_Value, Begin
    return False, 0, None, Temp


def Pkcs(Begin):
    Temp = Begin
    FLAG_0, SIZE_0, VAL_0, Begin = match('0', True, Begin)
    if FLAG_0:
        FLAG_Bt, SIZE_Bt, VAL_Bt, Begin = Bt(Begin)
        if FLAG_Bt:
            FLAG_Padding, SIZE_Padding, VAL_Padding, Begin = Padding(Begin)
            if FLAG_Padding:
                FLAG_Pkcsseq, SIZE_Pkcsseq, VAL_Pkcsseq, Begin = Pkcsseq(Begin)
                if FLAG_Pkcsseq:
                    SIZE_Pkcs = 1 + SIZE_Bt + SIZE_Padding + SIZE_Pkcsseq
                    VAL_Pkcs = VAL_Pkcsseq
                    if not (SIZE_Padding >= 9 and endcheck([2])):
                        return False, 0, None, Temp
                    return True, SIZE_Pkcs, VAL_Pkcs, Begin
    return False, 0, None, Temp


def Bt(Begin):
    Temp = Begin
    FLAG_1, SIZE_1, VAL_1, Begin = match('1', True, Begin)
    if FLAG_1:
        SIZE_Bt = 1
        VAL_Bt = 1
        if not (endcheck([1])):
            return False, 0, None, Temp
        return True, SIZE_Bt, VAL_Bt, Begin
    return False, 0, None, Temp


def Padding(Begin):
    Temp = Begin
    FLAG_255, SIZE_255, VAL_255, Begin = match('255', True, Begin)
    if FLAG_255:
        FLAG_Padding, SIZE_Padding, VAL_Padding, Begin = Padding(Begin)
        if FLAG_Padding:
            SIZE_Padding = 1 + SIZE_Padding
            VAL_Padding = addtotuple_dsl([255, VAL_Padding])
            if not (endcheck([1])):
                return False, 0, None, Temp
            return True, SIZE_Padding, VAL_Padding, Begin
    FLAG_0, SIZE_0, VAL_0, Begin = match('0', True, Begin)
    if FLAG_0:
        SIZE_Padding = 1
        VAL_Padding = 0
        if not (endcheck([1])):
            return False, 0, None, Temp
        return True, SIZE_Padding, VAL_Padding, Begin
    return False, 0, None, Temp


def Pkcsseq(Begin):
    Temp = Begin
    FLAG_Typecheck, SIZE_Typecheck, VAL_Typecheck, Begin = Typecheck(48, Begin)
    if FLAG_Typecheck:
        FLAG_Length, SIZE_Length, VAL_Length, Begin = Length(Begin)
        if FLAG_Length:
            FLAG_Signalgo, SIZE_Signalgo, VAL_Signalgo, Begin = Signalgo(Begin)
            if FLAG_Signalgo:
                FLAG_Digest, SIZE_Digest, VAL_Digest, Begin = Digest(Begin)
                if FLAG_Digest:
                    SIZE_Pkcsseq = SIZE_Typecheck + SIZE_Length + SIZE_Signalgo + SIZE_Digest
                    VAL_Pkcsseq = addtotuple_dsl([VAL_Signalgo, VAL_Digest])
                    if not (VAL_Length > 0 and SIZE_Signalgo + SIZE_Digest == VAL_Length and endcheck([2])):
                        return False, 0, None, Temp
                    return True, SIZE_Pkcsseq, VAL_Pkcsseq, Begin
    return False, 0, None, Temp


def Digest(Begin):
    Temp = Begin
    FLAG_Typecheck, SIZE_Typecheck, VAL_Typecheck, Begin = Typecheck(4, Begin)
    if FLAG_Typecheck:
        FLAG_Length, SIZE_Length, VAL_Length, Begin = Length(Begin)
        if FLAG_Length:
            FLAG_Value, SIZE_Value, VAL_Value, Begin = Value(VAL_Length, Begin)
            if FLAG_Value:
                SIZE_Digest = SIZE_Typecheck + SIZE_Length + SIZE_Value
                VAL_Digest = array_to_bytes_dsl([VAL_Value])
                if not (VAL_Length > 0 and SIZE_Value == VAL_Length and endcheck([2])):
                    return False, 0, None, Temp
                return True, SIZE_Digest, VAL_Digest, Begin
    return False, 0, None, Temp


def Signalgo(Begin):
    Temp = Begin
    FLAG_Typecheck, SIZE_Typecheck, VAL_Typecheck, Begin = Typecheck(48, Begin)
    if FLAG_Typecheck:
        FLAG_Length, SIZE_Length, VAL_Length, Begin = Length(Begin)
        if FLAG_Length:
            FLAG_Fieldssignalgo, SIZE_Fieldssignalgo, VAL_Fieldssignalgo, Begin = Fieldssignalgo(VAL_Length, Begin)
            if FLAG_Fieldssignalgo:
                SIZE_Signalgo = SIZE_Typecheck + SIZE_Length + SIZE_Fieldssignalgo
                VAL_Signalgo = VAL_Fieldssignalgo
                if not (VAL_Length > 0 and SIZE_Fieldssignalgo == VAL_Length and endcheck([1])):
                    return False, 0, None, Temp
                return True, SIZE_Signalgo, VAL_Signalgo, Begin
    return False, 0, None, Temp


def Fieldssignalgo(VAL_Length, Begin):
    Temp = Begin
    FLAG_Signoid, SIZE_Signoid, VAL_Signoid, Begin = Signoid(Begin)
    if FLAG_Signoid:
        FLAG_Signparam, SIZE_Signparam, VAL_Signparam, Begin = Signparam(VAL_Length - SIZE_Signoid, Begin)
        if FLAG_Signparam:
            SIZE_Fieldssignalgo = SIZE_Signoid + SIZE_Signparam
            VAL_Fieldssignalgo = AlgorithmIdentifier([VAL_Signoid, VAL_Signparam])
            if not (endcheck([1])):
                return False, 0, None, Temp
            return True, SIZE_Fieldssignalgo, VAL_Fieldssignalgo, Begin
    return False, 0, None, Temp


def Signoid(Begin):
    Temp = Begin
    FLAG_Typecheck, SIZE_Typecheck, VAL_Typecheck, Begin = Typecheck(6, Begin)
    if FLAG_Typecheck:
        FLAG_Length, SIZE_Length, VAL_Length, Begin = Length(Begin)
        if FLAG_Length:
            FLAG_Value, SIZE_Value, VAL_Value, Begin = Value(VAL_Length, Begin)
            if FLAG_Value:
                SIZE_Signoid = SIZE_Typecheck + SIZE_Length + SIZE_Value
                VAL_Signoid = hex_n_bytes_to_int_dsl([VAL_Value])
                VAL_Signoid = [VAL_Signoid, SIZE_Value]
                if not (SIZE_Value == VAL_Length and endcheck([1])):
                    return False, 0, None, Temp
                return True, SIZE_Signoid, VAL_Signoid, Begin
    return False, 0, None, Temp


def Signparam(VAL_Lenthh, Begin):
    Temp = Begin
    if not (VAL_Lenthh > 0):
        return True, 0, None, Begin
    FLAG_Type, SIZE_Type, VAL_Type, Begin = Type(Begin)
    if FLAG_Type:
        FLAG_Length, SIZE_Length, VAL_Length, Begin = Length(Begin)
        if FLAG_Length:
            FLAG_Value, SIZE_Value, VAL_Value, Begin = Value(VAL_Length, Begin)
            if FLAG_Value:
                SIZE_Signparam = SIZE_Type + SIZE_Length + SIZE_Value
                VAL_Value = array_to_bytes_dsl([VAL_Value])
                VAL_Signparam = Parameter([VAL_Type, VAL_Value])
                if not (SIZE_Value == VAL_Length and (VAL_Type == 5 and VAL_Length == 0) and endcheck([1])):
                    return False, 0, None, Temp
                return True, SIZE_Signparam, VAL_Signparam, Begin
    return False, 0, None, Temp
