#pragma once

#include <glad/glad.h>
#include "Shader.h"

struct CharacterInfo
{
	int x, y;
	int width, height;
	int xOffset, yOffset;
	int xAdvance;
	int page;
	int channel;
};

class Font
{
public:
	Font(const std::string& fontName);
	~Font();

	CharacterInfo GetCharacterInfo(int character);
	int GetWidth() const { return m_TotalWidth; }
	int GetHeight() const { return m_TotalHeight; }
	GLuint GetBitmap() const { return m_Bitmap; }
	int GetSize() const { return m_Size; }

private:
	GLuint m_Bitmap;
	std::map<int, CharacterInfo> m_CharacterInformation;
	int m_LineHeight;
	int m_Size;
	int m_TotalWidth, m_TotalHeight;
	std::string m_BaseFont;
	std::string m_BitmapPath;
};

class TextRenderer;

class Text
{
public:
	Text(const std::vector<int>& letters, float leftX, float rightX, float baseLine, float size);
	Text(const std::string& text, float leftX, float rightX, float baseLine, float size);
	~Text();

	void AddText(const std::vector<int>& letters, int position);
	void AddText(const std::string& letters, int position);

private:
	float m_Size;
	std::vector<int> m_Text;
	int m_Begin, m_End;
	float m_LeftX, m_RightX, m_Baseline;
	friend TextRenderer;
};

class TextRenderer
{
public:
	TextRenderer(const std::string& fontName);
	~TextRenderer();

	void AddToRenderQueue(const std::shared_ptr<Text>& m_Text);
	void RenderQueue();

	std::shared_ptr<Font> GetFont() { return m_Font; }

private:
	std::shared_ptr<Font> m_Font;
	GLuint m_Vao, m_Vb, m_Ib;
	std::queue<std::shared_ptr<Text>> m_RenderQueue;
	Shader m_TextShader;
};